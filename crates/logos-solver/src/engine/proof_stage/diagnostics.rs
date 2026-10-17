//! Serialized host diagnostic service, upload validation, and compile-checkpoint evidence.

use crate::artifacts::ArtifactWriter;
use crate::engine::now_ms_since_epoch;
use crate::engine::report::{
    AcceptedDiagnosticSourceAudit, AgentAudit, DiagnosticArtifactBinding,
    DiagnosticCheckerInvocation, ProblemCompileCheckpointEvidence, RejectedDiagnosticSourceAudit,
};
use crate::engine::rocq_session::IncrementalDiagnostics;
use crate::error::{Error, Result};
use serde::{Deserialize, Serialize};
use sha2::Digest;
use sha2::Sha256;
use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use super::audit::{audit_proof_module_rocq_text, audit_rocq_text, audit_scratch_rocq_text};
use super::checker::{is_trusted_rocq_environment_failure, run_host_diagnostic_rocq_check};
use super::diagnostic_inputs::SharedInputs;
use super::workspace::{
    ModulePublication, checked_proof_module_cache_source, persist_successful_scratch_candidate,
    recover_interrupted_trusted_cache_swap, validate_diagnostic_candidate_path,
    validate_proof_module_candidate_path,
};
use super::{
    CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT, DIAGNOSTIC_BROKER_HEADER_MAX_BYTES,
    DIAGNOSTIC_SOCKET_FILE, DIAGNOSTIC_SOCKET_TEMP_ROOT, PROOF_AGENT_HOST_TMP_DIRECTORY,
    PROOF_AGENT_SESSION_HOME_COUNTER, sha256_hex, write_pretty_json_file,
};

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub(super) enum CandidateKind {
    Problem,
    Module,
    Scratch,
}

impl CandidateKind {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Problem => "problem",
            Self::Module => "module",
            Self::Scratch => "scratch",
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum DiagnosticPurpose {
    StaticObligation,
    SemanticEquivalence,
    Assembly,
}

impl DiagnosticPurpose {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::StaticObligation => "static-obligation",
            Self::SemanticEquivalence => "semantic-equivalence",
            Self::Assembly => "assembly",
        }
    }
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CheckRequest {
    pub(super) schema_version: u32,
    pub(super) nonce: String,
    pub(super) mode: CandidateKind,
    pub(super) candidate_path: String,
    pub(super) purpose: DiagnosticPurpose,
    pub(super) candidate_sha256: String,
    pub(super) candidate_bytes: u64,
    pub(super) requested_timeout_seconds: u64,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct CheckResponse {
    schema_version: u32,
    sequence: Option<usize>,
    mode: Option<CandidateKind>,
    candidate_path: Option<String>,
    purpose: Option<DiagnosticPurpose>,
    candidate_sha256: Option<String>,
    compile_passed: bool,
    problem_compile_passed: bool,
    compile_checkpoint_advanced: bool,
    exit_code: Option<i32>,
    timed_out: bool,
    elapsed_ms: u128,
    stdout: String,
    stderr: String,
    error: Option<String>,
}

#[derive(Clone, Debug)]
pub(super) struct CompileCheckpoint {
    // The path only needs to retain Problem.v: every imported agent module is
    // host-checked and immutable by logical name for the lifetime of this
    // generated workspace. A fixed-witness restart discards the live workspace
    // and module cache; the generation-tagged checkpoint remains immutable
    // evidence but can never be reused by a later workspace generation.
    pub(super) path: PathBuf,
    pub(super) sha256: String,
    pub(super) workspace_generation: usize,
    pub(super) round: usize,
    pub(super) sequence: usize,
}

impl CompileCheckpoint {
    pub(super) fn report_evidence(
        &self,
        artifacts: &ArtifactWriter,
    ) -> Result<ProblemCompileCheckpointEvidence> {
        let path = self.path.strip_prefix(artifacts.root()).map_err(|_| {
            Error::ProofAgentCommand(format!(
                "problem compile checkpoint {} escapes the case artifact root",
                self.path.display()
            ))
        })?;
        let path = path.to_str().ok_or_else(|| {
            Error::ProofAgentCommand("problem compile checkpoint path is not UTF-8".to_owned())
        })?;
        Ok(ProblemCompileCheckpointEvidence {
            workspace_generation: self.workspace_generation,
            path: path.to_owned(),
            sha256: self.sha256.clone(),
            round: self.round,
            sequence: self.sequence,
        })
    }
}

struct PendingDiagnosticUpload {
    path: PathBuf,
}

impl PendingDiagnosticUpload {
    fn new(path: PathBuf) -> Self {
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for PendingDiagnosticUpload {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
        if let Some(parent) = self.path.parent() {
            let _ = std::fs::remove_dir(parent);
        }
    }
}

pub(super) struct ReadOnlyMappedFile {
    pointer: *mut libc::c_void,
    length: usize,
}

impl ReadOnlyMappedFile {
    pub(super) fn open_utf8(path: &Path) -> Result<Self> {
        let file = File::open(path).map_err(|source| Error::Read {
            path: path.to_owned(),
            source,
        })?;
        let length = usize::try_from(
            file.metadata()
                .map_err(|source| Error::Read {
                    path: path.to_owned(),
                    source,
                })?
                .len(),
        )
        .map_err(|_| {
            Error::ProofAgentCommand(format!(
                "file is too large to address on this host: {}",
                path.display()
            ))
        })?;
        if length == 0 {
            return Ok(Self {
                pointer: std::ptr::null_mut(),
                length,
            });
        }
        // SAFETY: `file` is open for the mmap call, the returned mapping is
        // read-only/private, and `Drop` unmaps exactly `length` bytes.  The
        // mapped artifact is host-owned and not writable by the container.
        let pointer = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                length,
                libc::PROT_READ,
                libc::MAP_PRIVATE,
                file.as_raw_fd(),
                0,
            )
        };
        if pointer == libc::MAP_FAILED {
            return Err(Error::Read {
                path: path.to_owned(),
                source: std::io::Error::last_os_error(),
            });
        }
        let mapped = Self { pointer, length };
        std::str::from_utf8(mapped.as_bytes()).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "mapped file {} is not UTF-8: {source}",
                path.display()
            ))
        })?;
        Ok(mapped)
    }

    pub(super) fn as_bytes(&self) -> &[u8] {
        if self.length == 0 {
            return &[];
        }
        // SAFETY: the mapping remains live for `self` and contains `length`
        // readable bytes by construction.
        unsafe { std::slice::from_raw_parts(self.pointer.cast::<u8>(), self.length) }
    }

    pub(super) fn as_str(&self) -> &str {
        // UTF-8 validity is established once by `open_utf8`.
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }
}

impl Drop for ReadOnlyMappedFile {
    fn drop(&mut self) {
        if self.length != 0 {
            // SAFETY: this is the exact live mapping created by `open_utf8`.
            let _ = unsafe { libc::munmap(self.pointer, self.length) };
        }
    }
}

#[derive(Default)]
pub(super) struct BrokerState {
    pub(super) incremental_diagnostics: IncrementalDiagnostics,
    pub(super) requests_seen: usize,
    pub(super) timeout_seconds_reserved: u64,
    pub(super) workspace_generation: usize,
    pub(super) active_problem_compile_checkpoint_sha256: Option<String>,
    pub(super) invocations: Vec<DiagnosticCheckerInvocation>,
    pub(super) accepted_source_audits: Vec<AcceptedDiagnosticSourceAudit>,
    pub(super) rejected_source_audits: Vec<RejectedDiagnosticSourceAudit>,
    pub(super) latest_checkpoint: Option<CompileCheckpoint>,
    pub(super) latest_feedback: Option<String>,
    pub(super) trusted_environment_error: Option<String>,
}

#[derive(Debug)]
pub(super) struct BrokerOutcome {
    pub(super) requests_seen: usize,
    pub(super) requested_timeout_seconds_reserved: u64,
    pub(super) accepted_count: usize,
    pub(super) rejected_source_audit_count: usize,
    pub(super) other_rejected_request_count: usize,
    pub(super) invocations: Vec<DiagnosticCheckerInvocation>,
    pub(super) accepted_source_audits: Vec<AcceptedDiagnosticSourceAudit>,
    pub(super) rejected_source_audits: Vec<RejectedDiagnosticSourceAudit>,
    pub(super) latest_checkpoint: Option<CompileCheckpoint>,
    pub(super) latest_feedback: Option<String>,
    pub(super) trusted_environment_error: Option<String>,
}

pub(super) struct DiagnosticBroker {
    socket_path: PathBuf,
    // Unix-domain socket paths have a small platform limit. Keep only this
    // zero-byte rendezvous point in a short, private /tmp directory; all proof
    // state and generated artifacts remain in the case-local host-tmp tree.
    _socket_directory: SocketDirectory,
    nonce: String,
    artifacts_root: PathBuf,
    round: usize,
    stop: Arc<AtomicBool>,
    pub(super) state: Arc<Mutex<BrokerState>>,
    handle: Option<JoinHandle<()>>,
}

pub(super) struct SocketDirectory {
    path: PathBuf,
    pub(super) sidecar_path: PathBuf,
}

pub(super) fn parse_case_process_supervisor_pid(value: &OsStr) -> Result<u32> {
    let bytes = value.as_bytes();
    if bytes.is_empty() || bytes[0] == b'0' || bytes.iter().any(|byte| !byte.is_ascii_digit()) {
        return Err(Error::ProofAgentCommand(format!(
            "{CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} must be a canonical positive decimal u32"
        )));
    }
    let text = std::str::from_utf8(bytes).map_err(|_| {
        Error::ProofAgentCommand(format!(
            "{CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} must be a canonical positive decimal u32"
        ))
    })?;
    let process_id = text.parse::<u32>().map_err(|_| {
        Error::ProofAgentCommand(format!(
            "{CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} must be a canonical positive decimal u32"
        ))
    })?;
    if process_id.to_string() != text {
        return Err(Error::ProofAgentCommand(format!(
            "{CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} must be a canonical positive decimal u32"
        )));
    }
    Ok(process_id)
}

fn case_process_supervisor_pid() -> Result<u32> {
    if let Some(value) = std::env::var_os(CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT) {
        return parse_case_process_supervisor_pid(&value);
    }
    // Unit tests exercise the broker in-process, outside the benchmark runner.
    // Production builds fail closed when the runner-authenticated channel is
    // absent; tests separately cover the strict parser above.
    #[cfg(test)]
    {
        Ok(std::process::id())
    }
    #[cfg(not(test))]
    {
        Err(Error::ProofAgentCommand(format!(
            "missing required {CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} environment binding"
        )))
    }
}

impl SocketDirectory {
    pub(super) fn create(artifacts_root: &Path, round: usize) -> Result<Self> {
        let process_id = case_process_supervisor_pid()?;
        let temp_root = Path::new(DIAGNOSTIC_SOCKET_TEMP_ROOT);
        let root_metadata = std::fs::symlink_metadata(temp_root).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to inspect diagnostic socket temp root {}: {source}",
                temp_root.display()
            ))
        })?;
        if root_metadata.file_type().is_symlink() || !root_metadata.is_dir() {
            return Err(Error::ProofAgentCommand(format!(
                "diagnostic socket temp root {} must be a real directory",
                temp_root.display()
            )));
        }
        let host_tmp = artifacts_root.join(PROOF_AGENT_HOST_TMP_DIRECTORY);
        std::fs::create_dir_all(&host_tmp).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to create proof-agent host temp root {} for diagnostic sidecar: {source}",
                host_tmp.display()
            ))
        })?;
        let host_tmp_metadata = std::fs::symlink_metadata(&host_tmp).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to inspect proof-agent host temp root {} for diagnostic sidecar: {source}",
                host_tmp.display()
            ))
        })?;
        if host_tmp_metadata.file_type().is_symlink() || !host_tmp_metadata.is_dir() {
            return Err(Error::ProofAgentCommand(format!(
                "diagnostic socket sidecar root {} must be a real directory",
                host_tmp.display()
            )));
        }
        std::fs::set_permissions(&host_tmp, std::fs::Permissions::from_mode(0o700)).map_err(
            |source| {
                Error::ProofAgentCommand(format!(
                    "failed to secure diagnostic socket sidecar root {}: {source}",
                    host_tmp.display()
                ))
            },
        )?;

        // Publish the exact external path before creating anything under /tmp.
        // A case-level SIGKILL can therefore leave either no external resource,
        // a harmless sidecar whose directory is absent, or a fully discoverable
        // directory.  In particular, there is no tempdir-before-sidecar window.
        let token_seed = format!(
            "{}:{}:{}:{}:{}",
            artifacts_root.display(),
            process_id,
            round,
            now_ms_since_epoch(),
            PROOF_AGENT_SESSION_HOME_COUNTER.fetch_add(1, Ordering::Relaxed),
        );
        let token = &sha256_hex(token_seed.as_bytes())[..32];
        let socket_directory_name = format!("logos-pds-{process_id}-{token}");
        let socket_directory = temp_root.join(&socket_directory_name);
        match std::fs::symlink_metadata(&socket_directory) {
            Ok(_) => {
                return Err(Error::ProofAgentCommand(format!(
                    "refusing pre-existing diagnostic socket directory {}",
                    socket_directory.display()
                )));
            }
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
            Err(source) => {
                return Err(Error::ProofAgentCommand(format!(
                    "failed to inspect diagnostic socket directory {}: {source}",
                    socket_directory.display()
                )));
            }
        }
        let sidecar_path = host_tmp.join(format!(
            ".diagnostic-socket-{process_id}-{round:02}-{socket_directory_name}.json"
        ));
        let pending_sidecar = host_tmp.join(format!(
            ".pending-diagnostic-socket-{process_id}-{round:02}-{socket_directory_name}.{}.tmp",
            now_ms_since_epoch()
        ));
        if std::fs::symlink_metadata(&sidecar_path).is_ok() {
            return Err(Error::ProofAgentCommand(format!(
                "refusing pre-existing diagnostic socket sidecar {}",
                sidecar_path.display()
            )));
        }
        let sidecar = serde_json::json!({
            "schemaVersion": 1,
            "solverPid": process_id,
            "directory": socket_directory,
        });
        let mut pending = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&pending_sidecar)
            .map_err(|source| {
                Error::ProofAgentCommand(format!(
                    "failed to create diagnostic socket sidecar {}: {source}",
                    pending_sidecar.display()
                ))
            })?;
        let sidecar_bytes = serde_json::to_vec(&sidecar)
            .map_err(|source| Error::ProofAgentCommand(source.to_string()))?;
        if let Err(source) = pending
            .write_all(&sidecar_bytes)
            .and_then(|()| pending.write_all(b"\n"))
            .and_then(|()| pending.sync_all())
        {
            let _ = std::fs::remove_file(&pending_sidecar);
            return Err(Error::ProofAgentCommand(format!(
                "failed to write diagnostic socket sidecar {}: {source}",
                pending_sidecar.display()
            )));
        }
        drop(pending);
        if let Err(source) = std::fs::hard_link(&pending_sidecar, &sidecar_path) {
            let _ = std::fs::remove_file(&pending_sidecar);
            return Err(Error::ProofAgentCommand(format!(
                "failed to publish diagnostic socket sidecar {}: {source}",
                sidecar_path.display()
            )));
        }
        if let Err(source) = std::fs::remove_file(&pending_sidecar) {
            let _ = std::fs::remove_file(&sidecar_path);
            return Err(Error::ProofAgentCommand(format!(
                "failed to finalize diagnostic socket sidecar {}: {source}",
                sidecar_path.display()
            )));
        }
        let host_tmp_directory = File::open(&host_tmp).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to open diagnostic socket sidecar root {}: {source}",
                host_tmp.display()
            ))
        })?;
        host_tmp_directory.sync_all().map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to sync diagnostic socket sidecar root {}: {source}",
                host_tmp.display()
            ))
        })?;

        let mut directory_builder = std::fs::DirBuilder::new();
        directory_builder.mode(0o700);
        if let Err(source) = directory_builder.create(&socket_directory) {
            let _ = std::fs::remove_file(&sidecar_path);
            return Err(Error::ProofAgentCommand(format!(
                "failed to create recorded diagnostic socket directory {}: {source}",
                socket_directory.display()
            )));
        }
        let metadata = match std::fs::symlink_metadata(&socket_directory) {
            Ok(metadata) => metadata,
            Err(source) => {
                let _ = std::fs::remove_dir(&socket_directory);
                let _ = std::fs::remove_file(&sidecar_path);
                return Err(Error::ProofAgentCommand(format!(
                    "failed to inspect short diagnostic socket directory {}: {source}",
                    socket_directory.display()
                )));
            }
        };
        if metadata.file_type().is_symlink()
            || !metadata.is_dir()
            || metadata.permissions().mode() & 0o777 != 0o700
        {
            let _ = std::fs::remove_dir(&socket_directory);
            let _ = std::fs::remove_file(&sidecar_path);
            return Err(Error::ProofAgentCommand(format!(
                "short diagnostic socket directory {} is not an atomically-created mode-0700 directory",
                socket_directory.display()
            )));
        }
        Ok(Self {
            path: socket_directory,
            sidecar_path,
        })
    }

    pub(super) fn socket_path(&self) -> PathBuf {
        self.path.join(DIAGNOSTIC_SOCKET_FILE)
    }
}

impl Drop for SocketDirectory {
    fn drop(&mut self) {
        let socket_path = self.socket_path();
        match std::fs::remove_file(&socket_path) {
            Ok(()) => {}
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => return,
        }
        match std::fs::remove_dir(&self.path) {
            Ok(()) => {}
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => return,
        }
        // Keep the sidecar discoverable until the external directory is gone.
        let _ = std::fs::remove_file(&self.sidecar_path);
    }
}

fn diagnostic_evidence_error(message: impl Into<String>) -> Error {
    Error::ProofAgentCommand(format!(
        "diagnostic broker evidence integrity failure: {}",
        message.into()
    ))
}

fn diagnostic_artifact_relative_path(artifacts_root: &Path, path: &Path) -> Result<String> {
    let relative = path.strip_prefix(artifacts_root).map_err(|_| {
        diagnostic_evidence_error(format!(
            "{} escapes artifact root {}",
            path.display(),
            artifacts_root.display()
        ))
    })?;
    if relative.as_os_str().is_empty()
        || relative
            .components()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(diagnostic_evidence_error(format!(
            "{} is not a normalized artifact-relative path",
            relative.display()
        )));
    }
    relative
        .to_str()
        .map(str::to_owned)
        .ok_or_else(|| diagnostic_evidence_error("diagnostic artifact path is not UTF-8"))
}

fn diagnostic_artifact_binding(
    artifacts_root: &Path,
    path: &Path,
) -> Result<DiagnosticArtifactBinding> {
    let relative = diagnostic_artifact_relative_path(artifacts_root, path)?;
    let metadata = std::fs::symlink_metadata(path).map_err(|source| {
        diagnostic_evidence_error(format!("cannot stat {}: {source}", path.display()))
    })?;
    if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
        return Err(diagnostic_evidence_error(format!(
            "{} is not a regular non-symlink file",
            path.display()
        )));
    }
    let canonical_root = std::fs::canonicalize(artifacts_root).map_err(|source| {
        diagnostic_evidence_error(format!(
            "cannot canonicalize artifact root {}: {source}",
            artifacts_root.display()
        ))
    })?;
    let canonical_path = std::fs::canonicalize(path).map_err(|source| {
        diagnostic_evidence_error(format!("cannot canonicalize {}: {source}", path.display()))
    })?;
    if !canonical_path.starts_with(&canonical_root) {
        return Err(diagnostic_evidence_error(format!(
            "{} resolves outside artifact root {}",
            path.display(),
            artifacts_root.display()
        )));
    }
    let bytes = std::fs::read(path).map_err(|source| {
        diagnostic_evidence_error(format!("cannot read {}: {source}", path.display()))
    })?;
    Ok(DiagnosticArtifactBinding {
        path: relative,
        sha256: sha256_hex(&bytes),
        bytes: bytes.len(),
    })
}

fn read_bound_diagnostic_artifact(
    artifacts_root: &Path,
    binding: &DiagnosticArtifactBinding,
) -> Result<Vec<u8>> {
    let relative = Path::new(&binding.path);
    if relative.is_absolute()
        || relative.as_os_str().is_empty()
        || relative
            .components()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(diagnostic_evidence_error(format!(
            "reported path {:?} is not artifact-relative",
            binding.path
        )));
    }
    let path = artifacts_root.join(relative);
    let observed = diagnostic_artifact_binding(artifacts_root, &path)?;
    if observed != *binding {
        return Err(diagnostic_evidence_error(format!(
            "binding for {} drifted: expected {} bytes/{}, observed {} bytes/{}",
            binding.path, binding.bytes, binding.sha256, observed.bytes, observed.sha256
        )));
    }
    std::fs::read(&path).map_err(|source| {
        diagnostic_evidence_error(format!("cannot read bound {}: {source}", path.display()))
    })
}

fn record_diagnostic_environment_error(state: &Arc<Mutex<BrokerState>>, message: String) {
    if let Ok(mut locked) = state.lock() {
        locked.trusted_environment_error.get_or_insert(message);
    }
}

fn validate_diagnostic_broker_outcome(
    artifacts_root: &Path,
    round: usize,
    outcome: &BrokerOutcome,
) -> Result<()> {
    if outcome.accepted_count != outcome.invocations.len()
        || outcome.accepted_count != outcome.accepted_source_audits.len()
    {
        return Err(diagnostic_evidence_error(format!(
            "accepted count {} disagrees with {} checker invocations and {} accepted audits",
            outcome.accepted_count,
            outcome.invocations.len(),
            outcome.accepted_source_audits.len()
        )));
    }
    if outcome.rejected_source_audit_count != outcome.rejected_source_audits.len() {
        return Err(diagnostic_evidence_error(format!(
            "rejected source-audit count {} disagrees with {} records",
            outcome.rejected_source_audit_count,
            outcome.rejected_source_audits.len()
        )));
    }
    let classified_count = outcome
        .accepted_count
        .checked_add(outcome.rejected_source_audit_count)
        .ok_or_else(|| diagnostic_evidence_error("classified request count overflowed"))?;
    if classified_count > outcome.requests_seen
        || outcome.other_rejected_request_count != outcome.requests_seen - classified_count
    {
        return Err(diagnostic_evidence_error(format!(
            "request totals do not reconcile: seen {}, accepted {}, source-audit rejected {}, other rejected {}",
            outcome.requests_seen,
            outcome.accepted_count,
            outcome.rejected_source_audit_count,
            outcome.other_rejected_request_count
        )));
    }
    let mut request_ordinals = BTreeSet::new();
    let mut classified_requested_timeout_seconds = 0u64;
    let mut previous_accepted_request_ordinal = 0usize;
    for (index, (invocation, accepted)) in outcome
        .invocations
        .iter()
        .zip(&outcome.accepted_source_audits)
        .enumerate()
    {
        let sequence = index + 1;
        if invocation.sequence != Some(sequence)
            || invocation.mode.as_deref() != Some(accepted.mode.as_str())
            || invocation.candidate_path.as_deref() != Some(accepted.candidate_path.as_str())
            || invocation.purpose.as_deref() != Some(accepted.purpose.as_str())
            || accepted.sequence != sequence
            || invocation.candidate_sha256.as_deref() != Some(accepted.candidate_sha256.as_str())
            || invocation.requested_timeout_seconds != accepted.requested_timeout_seconds
            || invocation.problem_compile_passed
                != Some(accepted.mode == "problem" && invocation.compile_passed == Some(true))
            || invocation.compile_checkpoint_advanced
                != Some(accepted.mode == "problem" && invocation.compile_passed == Some(true))
        {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic identity drifted at checker sequence {sequence}"
            )));
        }
        if accepted.request_ordinal <= previous_accepted_request_ordinal
            || accepted.request_ordinal > outcome.requests_seen
            || !request_ordinals.insert(accepted.request_ordinal)
        {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic has invalid request ordinal {}",
                accepted.request_ordinal
            )));
        }
        previous_accepted_request_ordinal = accepted.request_ordinal;
        let stored_candidate = if accepted.mode == "module" {
            validate_proof_module_candidate_path(&accepted.candidate_path)
                .map_err(diagnostic_evidence_error)?
        } else {
            PathBuf::from("Problem.v")
        };
        let expected_candidate_path = format!(
            "proof-stage/proof-agent/rounds/{round:02}/interactive-diagnostics/{sequence:02}/checked-workspace/{}",
            stored_candidate.display()
        );
        if accepted.candidate.path != expected_candidate_path {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic candidate path {:?} does not equal {:?}",
                accepted.candidate.path, expected_candidate_path
            )));
        }
        let candidate = read_bound_diagnostic_artifact(artifacts_root, &accepted.candidate)?;
        if sha256_hex(&candidate) != accepted.candidate_sha256 {
            return Err(diagnostic_evidence_error(format!(
                "accepted candidate digest disagrees at checker sequence {sequence}"
            )));
        }
        let expected_audit_path = format!(
            "proof-stage/proof-agent/rounds/{round:02}/interactive-diagnostics/{sequence:02}/audit.json"
        );
        if accepted.audit.path != expected_audit_path {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic audit path {:?} does not equal {:?}",
                accepted.audit.path, expected_audit_path
            )));
        }
        let audit_bytes = read_bound_diagnostic_artifact(artifacts_root, &accepted.audit)?;
        let audit: AgentAudit = serde_json::from_slice(&audit_bytes).map_err(|source| {
            diagnostic_evidence_error(format!(
                "cannot parse accepted audit {}: {source}",
                accepted.audit.path
            ))
        })?;
        if !audit.passed || !audit.findings.is_empty() {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic audit {} is not clean",
                accepted.audit.path
            )));
        }
        classified_requested_timeout_seconds = classified_requested_timeout_seconds
            .checked_add(accepted.requested_timeout_seconds)
            .ok_or_else(|| diagnostic_evidence_error("accepted timeout total overflowed"))?;
    }

    let mut previous_rejected_request_ordinal = 0usize;
    for rejected in &outcome.rejected_source_audits {
        if rejected.request_ordinal <= previous_rejected_request_ordinal
            || rejected.request_ordinal > outcome.requests_seen
            || !request_ordinals.insert(rejected.request_ordinal)
        {
            return Err(diagnostic_evidence_error(format!(
                "source-audit rejection has invalid request ordinal {}",
                rejected.request_ordinal
            )));
        }
        previous_rejected_request_ordinal = rejected.request_ordinal;
        let root = format!(
            "proof-stage/proof-agent/rounds/{round:02}/rejected-diagnostic-source-audits/{:02}",
            rejected.request_ordinal
        );
        for (binding, name) in [
            (&rejected.problem, "Problem.v"),
            (&rejected.request, "request.json"),
            (&rejected.audit, "audit.json"),
            (&rejected.feedback, "feedback.txt"),
        ] {
            let expected_path = format!("{root}/{name}");
            if binding.path != expected_path {
                return Err(diagnostic_evidence_error(format!(
                    "rejected diagnostic binding path {:?} does not equal {:?}",
                    binding.path, expected_path
                )));
            }
        }
        let problem = read_bound_diagnostic_artifact(artifacts_root, &rejected.problem)?;
        if sha256_hex(&problem) != rejected.candidate_sha256 {
            return Err(diagnostic_evidence_error(format!(
                "rejected Problem.v digest disagrees with request ordinal {}",
                rejected.request_ordinal
            )));
        }
        let request_bytes = read_bound_diagnostic_artifact(artifacts_root, &rejected.request)?;
        let request: CheckRequest = serde_json::from_slice(&request_bytes).map_err(|source| {
            diagnostic_evidence_error(format!(
                "cannot parse rejected request {}: {source}",
                rejected.request.path
            ))
        })?;
        if request.schema_version != 2
            || request.mode.as_str() != rejected.mode
            || request.candidate_path != rejected.candidate_path
            || request.purpose.as_str() != rejected.purpose
            || request.candidate_sha256 != rejected.candidate_sha256
            || request.candidate_bytes != problem.len() as u64
            || request.requested_timeout_seconds != rejected.requested_timeout_seconds
        {
            return Err(diagnostic_evidence_error(format!(
                "rejected request identity drifted at ordinal {}",
                rejected.request_ordinal
            )));
        }
        let audit_bytes = read_bound_diagnostic_artifact(artifacts_root, &rejected.audit)?;
        let audit: AgentAudit = serde_json::from_slice(&audit_bytes).map_err(|source| {
            diagnostic_evidence_error(format!(
                "cannot parse rejected audit {}: {source}",
                rejected.audit.path
            ))
        })?;
        if audit.passed || audit.findings.is_empty() {
            return Err(diagnostic_evidence_error(format!(
                "rejected diagnostic audit {} does not contain a rejection finding",
                rejected.audit.path
            )));
        }
        let feedback_bytes = read_bound_diagnostic_artifact(artifacts_root, &rejected.feedback)?;
        let feedback = std::str::from_utf8(&feedback_bytes).map_err(|source| {
            diagnostic_evidence_error(format!(
                "rejected feedback {} is not UTF-8: {source}",
                rejected.feedback.path
            ))
        })?;
        if !feedback.contains(&rejected.candidate_sha256)
            || !feedback.contains("checker was not executed")
        {
            return Err(diagnostic_evidence_error(format!(
                "rejected feedback identity drifted at ordinal {}",
                rejected.request_ordinal
            )));
        }
        classified_requested_timeout_seconds = classified_requested_timeout_seconds
            .checked_add(rejected.requested_timeout_seconds)
            .ok_or_else(|| diagnostic_evidence_error("rejected timeout total overflowed"))?;
    }
    if classified_requested_timeout_seconds > outcome.requested_timeout_seconds_reserved {
        return Err(diagnostic_evidence_error(format!(
            "classified requests reserve {classified_requested_timeout_seconds} seconds but broker recorded only {}",
            outcome.requested_timeout_seconds_reserved
        )));
    }
    Ok(())
}

/// Immutable round inputs shared by all connections. Mutable counters and the
/// incremental session stay in BrokerState behind the existing single broker.
struct RequestContext<'a> {
    expected_nonce: &'a str,
    artifacts_root: &'a Path,
    round: usize,
    trusted_checker_path: &'a Path,
    proof_workdir: &'a Path,
    shared_inputs: &'a SharedInputs,
    logos_repo_root: &'a Path,
    rocq_opam_switch: Option<&'a Path>,
    writable_storage_limit_bytes: u64,
    deadline: Instant,
}

impl DiagnosticBroker {
    pub(super) fn start(
        artifacts_root: &Path,
        round: usize,
        workspace_generation: usize,
        trusted_checker_path: &Path,
        proof_workdir: &Path,
        logos_repo_root: &Path,
        rocq_opam_switch: Option<&Path>,
        active_problem_compile_checkpoint_sha256: Option<&str>,
        writable_storage_limit_bytes: u64,
        deadline: Instant,
    ) -> Result<Self> {
        let shared_inputs =
            SharedInputs::prepare(artifacts_root, proof_workdir, workspace_generation)?;
        let socket_directory = SocketDirectory::create(artifacts_root, round)?;
        let socket_path = socket_directory.socket_path();
        let listener = UnixListener::bind(&socket_path).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to bind proof diagnostic broker socket {}: {source}",
                socket_path.display()
            ))
        })?;
        std::fs::set_permissions(&socket_path, std::fs::Permissions::from_mode(0o600)).map_err(
            |source| {
                Error::ProofAgentCommand(format!(
                    "failed to secure proof diagnostic broker socket {}: {source}",
                    socket_path.display()
                ))
            },
        )?;
        listener.set_nonblocking(true).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to configure proof diagnostic broker socket {}: {source}",
                socket_path.display()
            ))
        })?;

        let nonce_seed = format!(
            "{}:{}:{}:{}",
            std::process::id(),
            now_ms_since_epoch(),
            PROOF_AGENT_SESSION_HOME_COUNTER.fetch_add(1, Ordering::Relaxed),
            socket_path.display()
        );
        let nonce = sha256_hex(nonce_seed.as_bytes());
        let stop = Arc::new(AtomicBool::new(false));
        let state = Arc::new(Mutex::new(BrokerState {
            workspace_generation,
            active_problem_compile_checkpoint_sha256: active_problem_compile_checkpoint_sha256
                .map(str::to_owned),
            ..BrokerState::default()
        }));
        let thread_stop = Arc::clone(&stop);
        let thread_state = Arc::clone(&state);
        let artifacts_root = artifacts_root.to_owned();
        let outcome_artifacts_root = artifacts_root.clone();
        let trusted_checker_path = trusted_checker_path.to_owned();
        let proof_workdir = proof_workdir.to_owned();
        let logos_repo_root = logos_repo_root.to_owned();
        let rocq_opam_switch = rocq_opam_switch.map(Path::to_owned);
        let expected_nonce = nonce.clone();
        let handle = thread::Builder::new()
            .name(format!("logos-proof-diagnostic-{round}"))
            .spawn(move || {
                let context = RequestContext {
                    expected_nonce: &expected_nonce,
                    artifacts_root: &artifacts_root,
                    round,
                    trusted_checker_path: &trusted_checker_path,
                    proof_workdir: &proof_workdir,
                    shared_inputs: &shared_inputs,
                    logos_repo_root: &logos_repo_root,
                    rocq_opam_switch: rocq_opam_switch.as_deref(),
                    writable_storage_limit_bytes,
                    deadline,
                };
                while !thread_stop.load(Ordering::Acquire) {
                    match listener.accept() {
                        Ok((stream, _)) => {
                            if thread_stop.load(Ordering::Acquire) {
                                break;
                            }
                            handle_diagnostic_broker_connection(stream, &context, &thread_state);
                        }
                        Err(source) if source.kind() == std::io::ErrorKind::WouldBlock => {
                            thread::sleep(Duration::from_millis(10));
                        }
                        Err(source) => {
                            if let Ok(mut locked) = thread_state.lock() {
                                locked.trusted_environment_error = Some(format!(
                                    "proof diagnostic broker accept failed: {source}"
                                ));
                            }
                            break;
                        }
                    }
                }
                // Linux parent-death signaling follows the spawning *thread*.
                // Stop/reap its REPL while this thread is still alive, so the
                // trusted shell can run its sandbox scratch-cleanup trap.
                if let Ok(mut locked) = thread_state.lock() {
                    locked.incremental_diagnostics = IncrementalDiagnostics::default();
                }
            })
            .map_err(|source| {
                Error::ProofAgentCommand(format!(
                    "failed to start proof diagnostic broker thread: {source}"
                ))
            })?;
        Ok(Self {
            socket_path,
            _socket_directory: socket_directory,
            nonce,
            artifacts_root: outcome_artifacts_root,
            round,
            stop,
            state,
            handle: Some(handle),
        })
    }

    pub(super) fn nonce(&self) -> &str {
        &self.nonce
    }

    pub(super) fn socket_path(&self) -> &Path {
        &self.socket_path
    }

    pub(super) fn finish(mut self) -> Result<BrokerOutcome> {
        self.stop.store(true, Ordering::Release);
        let _ = UnixStream::connect(&self.socket_path);
        if let Some(handle) = self.handle.take() {
            handle.join().map_err(|_| {
                Error::ProofAgentCommand("proof diagnostic broker thread panicked".to_owned())
            })?;
        }
        let mut state = self.state.lock().map_err(|_| {
            Error::ProofAgentCommand("proof diagnostic broker state was poisoned".to_owned())
        })?;
        let accepted_count = state.accepted_source_audits.len();
        let rejected_source_audit_count = state.rejected_source_audits.len();
        let classified_count = accepted_count
            .checked_add(rejected_source_audit_count)
            .ok_or_else(|| diagnostic_evidence_error("classified request count overflowed"))?;
        let other_rejected_request_count = state
            .requests_seen
            .checked_sub(classified_count)
            .ok_or_else(|| {
                diagnostic_evidence_error(
                    "accepted plus rejected source-audit records exceed requests seen",
                )
            })?;
        let outcome = BrokerOutcome {
            requests_seen: state.requests_seen,
            requested_timeout_seconds_reserved: state.timeout_seconds_reserved,
            accepted_count,
            rejected_source_audit_count,
            other_rejected_request_count,
            invocations: std::mem::take(&mut state.invocations),
            accepted_source_audits: std::mem::take(&mut state.accepted_source_audits),
            rejected_source_audits: std::mem::take(&mut state.rejected_source_audits),
            latest_checkpoint: state.latest_checkpoint.take(),
            latest_feedback: state.latest_feedback.take(),
            trusted_environment_error: state.trusted_environment_error.take(),
        };
        validate_diagnostic_broker_outcome(&self.artifacts_root, self.round, &outcome)?;
        Ok(outcome)
    }
}

impl Drop for DiagnosticBroker {
    fn drop(&mut self) {
        // Also cover early errors before finish(): otherwise the listener thread
        // (and now its persistent Rocq process) could outlive the proof round.
        self.stop.store(true, Ordering::Release);
        let _ = UnixStream::connect(&self.socket_path);
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

fn handle_diagnostic_broker_connection(
    mut stream: UnixStream,
    context: &RequestContext<'_>,
    state: &Arc<Mutex<BrokerState>>,
) {
    let transport_timeout = context
        .deadline
        .saturating_duration_since(Instant::now())
        .max(Duration::from_secs(1));
    let _ = stream.set_read_timeout(Some(transport_timeout));
    let _ = stream.set_write_timeout(Some(transport_timeout));
    let response = run_diagnostic_broker_request(&mut stream, context, state);
    let mut bytes = serde_json::to_vec(&response).unwrap_or_else(|source| {
        format!(
            "{{\"schemaVersion\":2,\"compilePassed\":false,\"problemCompilePassed\":false,\"error\":{}}}",
            serde_json::to_string(&source.to_string()).expect("serialize broker error")
        )
        .into_bytes()
    });
    bytes.push(b'\n');
    let _ = stream.write_all(&bytes);
    let _ = stream.flush();
}

fn run_diagnostic_broker_request(
    stream: &mut UnixStream,
    context: &RequestContext<'_>,
    state: &Arc<Mutex<BrokerState>>,
) -> CheckResponse {
    let RequestContext {
        expected_nonce,
        artifacts_root,
        round,
        trusted_checker_path,
        proof_workdir,
        shared_inputs,
        logos_repo_root,
        rocq_opam_switch,
        writable_storage_limit_bytes,
        deadline,
    } = *context;
    let rejected = |error: String| CheckResponse {
        schema_version: 2,
        sequence: None,
        mode: None,
        candidate_path: None,
        purpose: None,
        candidate_sha256: None,
        compile_passed: false,
        problem_compile_passed: false,
        compile_checkpoint_advanced: false,
        exit_code: None,
        timed_out: false,
        elapsed_ms: 0,
        stdout: String::new(),
        stderr: String::new(),
        error: Some(error),
    };

    let request_ordinal = {
        let mut locked = match state.lock() {
            Ok(locked) => locked,
            Err(_) => return rejected("diagnostic broker state was poisoned".to_owned()),
        };
        locked.requests_seen = locked.requests_seen.saturating_add(1);
        locked.requests_seen
    };

    let mut request_bytes = Vec::new();
    let mut block = [0u8; 512];
    loop {
        let count = match stream.read(&mut block) {
            Ok(0) => return rejected("diagnostic broker request ended before newline".to_owned()),
            Ok(count) => count,
            Err(source) => {
                return rejected(format!(
                    "failed to read diagnostic broker request: {source}"
                ));
            }
        };
        request_bytes.extend_from_slice(&block[..count]);
        if request_bytes.contains(&b'\n') {
            break;
        }
        if request_bytes.len() > DIAGNOSTIC_BROKER_HEADER_MAX_BYTES {
            return rejected(
                "diagnostic broker JSON header exceeds its protocol envelope".to_owned(),
            );
        }
    }
    let Some(newline) = request_bytes.iter().position(|byte| *byte == b'\n') else {
        return rejected("diagnostic broker request has no newline".to_owned());
    };
    if newline > DIAGNOSTIC_BROKER_HEADER_MAX_BYTES {
        return rejected("diagnostic broker JSON header exceeds its protocol envelope".to_owned());
    }
    let request = match serde_json::from_slice::<CheckRequest>(&request_bytes[..newline]) {
        Ok(request) => request,
        Err(source) => return rejected(format!("invalid diagnostic broker request: {source}")),
    };
    if request.schema_version != 2 {
        return rejected("diagnostic broker schemaVersion must equal 2".to_owned());
    }
    if request.nonce != expected_nonce {
        return rejected("diagnostic broker nonce mismatch".to_owned());
    }
    let candidate_path =
        match validate_diagnostic_candidate_path(request.mode, &request.candidate_path) {
            Ok(path) => path,
            Err(error) => return rejected(error),
        };
    if request.candidate_sha256.len() != 64
        || !request
            .candidate_sha256
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        return rejected("candidateSha256 must be 64 lowercase hexadecimal characters".to_owned());
    }
    if request.requested_timeout_seconds == 0 {
        return rejected("requestedTimeoutSeconds must be positive".to_owned());
    }
    if request.candidate_bytes > writable_storage_limit_bytes {
        return rejected(format!(
            "candidateBytes exceeds the proof-agent aggregate writable-storage quota of {writable_storage_limit_bytes} bytes"
        ));
    }

    let candidate_len = match usize::try_from(request.candidate_bytes) {
        Ok(candidate_len) => candidate_len,
        Err(_) => return rejected("candidateBytes cannot be represented on this host".to_owned()),
    };
    let upload_dir = artifacts_root.join(format!(
        "proof-stage/proof-agent/rounds/{round:02}/diagnostic-uploads"
    ));
    if let Err(source) = std::fs::create_dir_all(&upload_dir) {
        return rejected(format!(
            "failed to create diagnostic upload directory: {source}"
        ));
    }
    let pending_upload = PendingDiagnosticUpload::new(upload_dir.join(format!(
        ".request-{request_ordinal:08}-{}-{}.tmp",
        std::process::id(),
        now_ms_since_epoch()
    )));
    let mut upload = match OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(pending_upload.path())
    {
        Ok(upload) => upload,
        Err(source) => {
            return rejected(format!("failed to create diagnostic upload file: {source}"));
        }
    };
    let mut uploaded_digest = Sha256::new();
    let mut uploaded_len = 0usize;
    let buffered_candidate = &request_bytes[newline + 1..];
    if buffered_candidate.len() > candidate_len {
        return rejected("diagnostic request contains bytes beyond candidateBytes".to_owned());
    }
    if let Err(source) = upload.write_all(buffered_candidate) {
        return rejected(format!("failed to write diagnostic candidate: {source}"));
    }
    uploaded_digest.update(buffered_candidate);
    uploaded_len += buffered_candidate.len();
    let mut candidate_block = [0u8; 64 * 1024];
    while uploaded_len < candidate_len {
        let remaining = candidate_len - uploaded_len;
        let block_len = remaining.min(candidate_block.len());
        let count = match stream.read(&mut candidate_block[..block_len]) {
            Ok(0) => {
                return rejected("diagnostic candidate ended before candidateBytes".to_owned());
            }
            Ok(count) => count,
            Err(source) => {
                return rejected(format!("failed to read diagnostic candidate: {source}"));
            }
        };
        if let Err(source) = upload.write_all(&candidate_block[..count]) {
            return rejected(format!("failed to write diagnostic candidate: {source}"));
        }
        uploaded_digest.update(&candidate_block[..count]);
        uploaded_len += count;
    }
    if let Err(source) = upload.flush() {
        return rejected(format!("failed to flush diagnostic candidate: {source}"));
    }
    drop(upload);
    let uploaded_sha256 = format!("{:x}", uploaded_digest.finalize());
    if uploaded_sha256 != request.candidate_sha256 {
        return rejected(format!(
            "uploaded candidate digest differs from candidateSha256: expected {}, observed {uploaded_sha256}",
            request.candidate_sha256
        ));
    }
    if let Some(error) = state
        .lock()
        .ok()
        .and_then(|locked| locked.trusted_environment_error.clone())
    {
        return rejected(format!(
            "diagnostic broker is unavailable after a trusted environment failure: {error}"
        ));
    }

    // Reject edits to published names before allocating a diagnostic snapshot.
    // Such requests do not consume an invocation sequence. Rejecting after
    // snapshot creation left that sequence's WitnessModules directory behind,
    // poisoning the next otherwise-valid request in this same broker session.
    // The serialized broker binds the checked cache throughout this request.
    let checked_module_source = if request.mode == CandidateKind::Module {
        let source = match recover_interrupted_trusted_cache_swap(trusted_checker_path)
            .and_then(|()| checked_proof_module_cache_source(trusted_checker_path, &candidate_path))
        {
            Ok(source) => source,
            Err(error) => {
                let message = error.to_string();
                record_diagnostic_environment_error(state, message.clone());
                return rejected(message);
            }
        };
        if source
            .as_ref()
            .is_some_and(|source| source.sha256 != uploaded_sha256)
        {
            return rejected(format!(
                "checked proof module {} is immutable; create a new module name for revised source",
                request.candidate_path
            ));
        }
        source
    } else {
        None
    };

    let sequence = {
        let mut locked = match state.lock() {
            Ok(locked) => locked,
            Err(_) => return rejected("diagnostic broker state was poisoned".to_owned()),
        };
        if request.mode == CandidateKind::Problem
            && (locked.active_problem_compile_checkpoint_sha256.as_deref()
                == Some(request.candidate_sha256.as_str())
                || locked
                    .latest_checkpoint
                    .as_ref()
                    .is_some_and(|checkpoint| checkpoint.sha256 == request.candidate_sha256))
        {
            return rejected(format!(
                "Problem.v digest {} is already the active compile-clean checkpoint; an unchanged candidate is not recompiled or counted as progress",
                request.candidate_sha256
            ));
        }
        locked.timeout_seconds_reserved = locked
            .timeout_seconds_reserved
            .saturating_add(request.requested_timeout_seconds);
        locked.invocations.len() + 1
    };

    // The upload digest was verified above; snapshotting moves those bytes,
    // rather than independently computing another digest.
    let actual_sha256 = uploaded_sha256;
    let (checked_workspace, diagnostic_problem_path) =
        match snapshot_interactive_diagnostic_candidate(
            artifacts_root,
            proof_workdir,
            shared_inputs,
            round,
            sequence,
            request.mode,
            &candidate_path,
            pending_upload.path(),
        ) {
            Ok(value) => value,
            Err(error) => return rejected(error.to_string()),
        };
    let effective_timeout_seconds = request
        .requested_timeout_seconds
        .min(deadline.saturating_duration_since(Instant::now()).as_secs());
    if effective_timeout_seconds == 0 {
        return rejected(
            "no time remains in this proof-agent turn for a host diagnostic".to_owned(),
        );
    }
    let diagnostic_dir = checked_workspace
        .parent()
        .expect("interactive checked workspace has a parent");
    let diagnostic_problem_relative = diagnostic_problem_path
        .strip_prefix(artifacts_root)
        .unwrap_or(&diagnostic_problem_path)
        .display()
        .to_string();
    let mapped_problem = match ReadOnlyMappedFile::open_utf8(&diagnostic_problem_path) {
        Ok(mapped) => mapped,
        Err(error) => return rejected(error.to_string()),
    };
    let problem_text = mapped_problem.as_str();
    let audit_started = Instant::now();
    let audit_findings = match request.mode {
        CandidateKind::Problem => audit_rocq_text(&diagnostic_problem_relative, problem_text),
        CandidateKind::Module => {
            audit_proof_module_rocq_text(&diagnostic_problem_relative, problem_text)
        }
        CandidateKind::Scratch => {
            audit_scratch_rocq_text(&diagnostic_problem_relative, problem_text)
        }
    };
    let candidate_audit = AgentAudit {
        passed: audit_findings.is_empty(),
        scanned_files: vec![diagnostic_problem_relative],
        findings: audit_findings,
    };
    if !candidate_audit.passed {
        let findings = candidate_audit
            .findings
            .iter()
            .take(4)
            .map(|finding| format!("{} at line {}", finding.token, finding.line))
            .collect::<Vec<_>>()
            .join(", ");
        let error = format!(
            "deterministic transient {} audit rejected diagnostic candidate before checker execution ({} finding(s): {findings})",
            request.mode.as_str(),
            candidate_audit.findings.len()
        );
        let feedback = format!(
            "interactive {} compile #{sequence} for {} ({actual_sha256}, purpose {}) was rejected by the host deterministic source audit; the checker was not executed: {findings}",
            request.mode.as_str(),
            request.candidate_path,
            request.purpose.as_str()
        );
        let rejection_dir = artifacts_root.join(format!(
            "proof-stage/proof-agent/rounds/{round:02}/rejected-diagnostic-source-audits/{request_ordinal:02}"
        ));
        if let Err(source) = std::fs::create_dir_all(&rejection_dir)
            .and_then(|()| {
                std::fs::rename(&diagnostic_problem_path, rejection_dir.join("Problem.v"))
            })
            .and_then(|()| write_pretty_json_file(rejection_dir.join("request.json"), &request))
            .and_then(|()| {
                write_pretty_json_file(rejection_dir.join("audit.json"), &candidate_audit)
            })
            .and_then(|()| std::fs::write(rejection_dir.join("feedback.txt"), &feedback))
            .and_then(|()| std::fs::remove_dir_all(diagnostic_dir))
        {
            let message =
                format!("failed to persist rejected diagnostic source-audit evidence: {source}");
            record_diagnostic_environment_error(state, message.clone());
            return rejected(message);
        }
        let rejected_source_audit = match (|| -> Result<RejectedDiagnosticSourceAudit> {
            Ok(RejectedDiagnosticSourceAudit {
                request_ordinal,
                mode: request.mode.as_str().to_owned(),
                candidate_path: request.candidate_path.clone(),
                purpose: request.purpose.as_str().to_owned(),
                candidate_sha256: actual_sha256.clone(),
                requested_timeout_seconds: request.requested_timeout_seconds,
                problem: diagnostic_artifact_binding(
                    artifacts_root,
                    &rejection_dir.join("Problem.v"),
                )?,
                request: diagnostic_artifact_binding(
                    artifacts_root,
                    &rejection_dir.join("request.json"),
                )?,
                audit: diagnostic_artifact_binding(
                    artifacts_root,
                    &rejection_dir.join("audit.json"),
                )?,
                feedback: diagnostic_artifact_binding(
                    artifacts_root,
                    &rejection_dir.join("feedback.txt"),
                )?,
            })
        })() {
            Ok(record) => record,
            Err(error) => {
                let message = error.to_string();
                record_diagnostic_environment_error(state, message.clone());
                return rejected(message);
            }
        };
        let mut locked = match state.lock() {
            Ok(locked) => locked,
            Err(_) => return rejected("diagnostic broker state was poisoned".to_owned()),
        };
        locked.latest_feedback = Some(feedback);
        locked.rejected_source_audits.push(rejected_source_audit);
        drop(locked);
        return CheckResponse {
            schema_version: 2,
            sequence: None,
            mode: Some(request.mode),
            candidate_path: Some(request.candidate_path),
            purpose: Some(request.purpose),
            candidate_sha256: Some(actual_sha256),
            compile_passed: false,
            problem_compile_passed: false,
            compile_checkpoint_advanced: false,
            exit_code: None,
            timed_out: false,
            elapsed_ms: audit_started.elapsed().as_millis(),
            stdout: String::new(),
            stderr: String::new(),
            error: Some(error),
        };
    }
    if let Err(source) = write_pretty_json_file(diagnostic_dir.join("audit.json"), &candidate_audit)
    {
        let message = format!(
            "failed to persist the host diagnostic source audit before checker execution: {source}"
        );
        record_diagnostic_environment_error(state, message.clone());
        return rejected(message);
    }
    let accepted_source_audit = match (
        diagnostic_artifact_binding(artifacts_root, &diagnostic_problem_path),
        diagnostic_artifact_binding(artifacts_root, &diagnostic_dir.join("audit.json")),
    ) {
        (Ok(candidate), Ok(audit)) => AcceptedDiagnosticSourceAudit {
            request_ordinal,
            sequence,
            mode: request.mode.as_str().to_owned(),
            candidate_path: request.candidate_path.clone(),
            purpose: request.purpose.as_str().to_owned(),
            candidate_sha256: actual_sha256.clone(),
            requested_timeout_seconds: request.requested_timeout_seconds,
            candidate,
            audit,
        },
        (Err(error), _) | (_, Err(error)) => {
            let message = error.to_string();
            record_diagnostic_environment_error(state, message.clone());
            return rejected(message);
        }
    };

    // The broker handles one connection at a time. Installing the source now
    // closes the cache/source publication gap without making it reusable: the
    // current cache still lacks this logical name until the checker succeeds.
    let mut module_was_checked_before = false;
    let mut pending_module_publication = if request.mode == CandidateKind::Module {
        module_was_checked_before = checked_module_source.is_some();
        match ModulePublication::prepare(
            proof_workdir,
            &candidate_path,
            mapped_problem.as_bytes(),
            module_was_checked_before,
        ) {
            Ok(publication) => Some(publication),
            Err(error) => return rejected(error.to_string()),
        }
    } else {
        None
    };

    let mut incremental = state
        .lock()
        .map(|mut locked| std::mem::take(&mut locked.incremental_diagnostics))
        .unwrap_or_default();
    let (mut invocation, output) = run_host_diagnostic_rocq_check(
        trusted_checker_path,
        &checked_workspace,
        logos_repo_root,
        rocq_opam_switch,
        request.mode,
        &request.candidate_path,
        request.requested_timeout_seconds,
        effective_timeout_seconds,
        Some((&mut incremental, mapped_problem.as_str())),
    );
    if let Ok(mut locked) = state.lock() {
        locked.incremental_diagnostics = incremental;
    }
    let (stdout_bytes, stderr_bytes) = output
        .as_ref()
        .map(|output| (output.stdout.as_slice(), output.stderr.as_slice()))
        .unwrap_or((&[][..], &[][..]));
    let mut compile_passed = output
        .as_ref()
        .is_some_and(|output| output.status.success());
    if request.mode == CandidateKind::Module {
        let publication = pending_module_publication
            .take()
            .expect("module diagnostics prepare one source publication");
        let recovered_cache_source = recover_interrupted_trusted_cache_swap(trusted_checker_path)
            .and_then(|()| {
                checked_proof_module_cache_source(trusted_checker_path, &candidate_path)
            });
        if compile_passed {
            match recovered_cache_source {
                Ok(Some(source)) if source.bytes.as_slice() == mapped_problem.as_bytes() => {
                    publication.commit();
                }
                Ok(_) => {
                    let rollback_error = publication.rollback().err();
                    compile_passed = false;
                    let message = format!(
                        "module checker reported success without publishing the exact manifest-bound source/object pair for {}{}",
                        request.candidate_path,
                        rollback_error
                            .as_ref()
                            .map(|error| format!("; rollback also failed: {error}"))
                            .unwrap_or_default()
                    );
                    record_diagnostic_environment_error(state, message.clone());
                    invocation.error = Some(message);
                }
                Err(error) => {
                    let rollback_error = publication.rollback().err();
                    compile_passed = false;
                    let message = format!(
                        "could not validate successful module publication {} against the trusted cache: {error}{}",
                        request.candidate_path,
                        rollback_error
                            .as_ref()
                            .map(|error| format!("; rollback also failed: {error}"))
                            .unwrap_or_default()
                    );
                    record_diagnostic_environment_error(state, message.clone());
                    invocation.error = Some(message);
                }
            }
        } else {
            match recovered_cache_source {
                Ok(Some(source)) if source.bytes.as_slice() == mapped_problem.as_bytes() => {
                    // A late signal/timeout may make the wrapper report failure
                    // after the trusted checker atomically published its cache.
                    // Retain the already-installed exact source so no outcome
                    // can expose a cache-only module.
                    publication.commit();
                    if module_was_checked_before {
                        let message = format!(
                            "module checker failed while revalidating already checked source {}; retained the prior checked source and disabled the diagnostic broker",
                            request.candidate_path
                        );
                        record_diagnostic_environment_error(state, message.clone());
                        invocation.error = Some(message);
                    } else {
                        // The compiler-created object, exact source, ORDER, and
                        // all three digests were atomically published. A late
                        // wrapper signal cannot turn that completed diagnostic
                        // into a false response without splitting the durable
                        // reuse predicate from broker telemetry.
                        compile_passed = true;
                        invocation.error = None;
                    }
                }
                Ok(_) => {
                    if let Err(error) = publication.rollback() {
                        let message = format!(
                            "failed to roll back unsuccessful proof module {}: {error}",
                            request.candidate_path
                        );
                        record_diagnostic_environment_error(state, message.clone());
                        invocation.error = Some(message);
                    }
                }
                Err(error) => {
                    let rollback_error = publication.rollback().err();
                    let message = format!(
                        "could not reconcile failed module publication {} with the trusted cache: {error}{}",
                        request.candidate_path,
                        rollback_error
                            .as_ref()
                            .map(|error| format!("; rollback also failed: {error}"))
                            .unwrap_or_default()
                    );
                    record_diagnostic_environment_error(state, message.clone());
                    invocation.error = Some(message);
                }
            }
        }
    }
    if compile_passed
        && request.mode == CandidateKind::Scratch
        && let Err(error) = persist_successful_scratch_candidate(
            proof_workdir,
            &candidate_path,
            mapped_problem.as_bytes(),
        )
    {
        compile_passed = false;
        let message = format!(
            "failed to retain successful scratch candidate {}: {error}",
            request.candidate_path
        );
        record_diagnostic_environment_error(state, message.clone());
        invocation.error = Some(message);
    }
    let problem_compile_passed = compile_passed && request.mode == CandidateKind::Problem;
    let compile_checkpoint_advanced = problem_compile_passed;
    invocation.sequence = Some(sequence);
    invocation.mode = Some(request.mode.as_str().to_owned());
    invocation.candidate_sha256 = Some(actual_sha256.clone());
    invocation.candidate_path = Some(request.candidate_path.clone());
    invocation.purpose = Some(request.purpose.as_str().to_owned());
    invocation.compile_passed = Some(compile_passed);
    invocation.problem_compile_passed = Some(problem_compile_passed);
    invocation.compile_checkpoint_advanced = Some(compile_checkpoint_advanced);
    invocation.stdout_sha256 = Some(sha256_hex(stdout_bytes));
    invocation.stderr_sha256 = Some(sha256_hex(stderr_bytes));

    if let Err(source) = std::fs::write(diagnostic_dir.join("stdout.txt"), stdout_bytes)
        .and_then(|()| std::fs::write(diagnostic_dir.join("stderr.txt"), stderr_bytes))
        .and_then(|()| write_pretty_json_file(diagnostic_dir.join("request.json"), &request))
        .and_then(|()| write_pretty_json_file(diagnostic_dir.join("invocation.json"), &invocation))
    {
        record_diagnostic_environment_error(
            state,
            format!(
                "failed to persist accepted diagnostic checker evidence for sequence {sequence}: {source}"
            ),
        );
    }

    let stdout = String::from_utf8_lossy(stdout_bytes).into_owned();
    let stderr = String::from_utf8_lossy(stderr_bytes).into_owned();
    let feedback = format!(
        "interactive {} compile #{sequence} for {} ({actual_sha256}, purpose {}): exit {:?}, timed out {}, elapsed {} ms, checkpoint advanced {}\n{}",
        request.mode.as_str(),
        request.candidate_path,
        request.purpose.as_str(),
        invocation.exit_code,
        invocation.timed_out,
        invocation.elapsed_ms,
        compile_checkpoint_advanced,
        stderr
    );
    if let Ok(mut locked) = state.lock() {
        if compile_checkpoint_advanced {
            locked.latest_checkpoint = Some(CompileCheckpoint {
                path: diagnostic_problem_path.clone(),
                sha256: actual_sha256.clone(),
                workspace_generation: locked.workspace_generation,
                round,
                sequence,
            });
        }
        if is_trusted_rocq_environment_failure(invocation.exit_code) {
            locked.trusted_environment_error = Some(format!(
                "interactive host problem compiler reported an invalid trusted environment: {feedback}"
            ));
        }
        locked.latest_feedback = Some(feedback);
        locked.accepted_source_audits.push(accepted_source_audit);
        locked.invocations.push(invocation.clone());
    }

    CheckResponse {
        schema_version: 2,
        sequence: Some(sequence),
        mode: Some(request.mode),
        candidate_path: Some(request.candidate_path),
        purpose: Some(request.purpose),
        candidate_sha256: Some(actual_sha256),
        compile_passed,
        problem_compile_passed,
        compile_checkpoint_advanced,
        exit_code: invocation.exit_code,
        timed_out: invocation.timed_out,
        elapsed_ms: invocation.elapsed_ms,
        stdout,
        stderr,
        error: invocation.error,
    }
}

fn snapshot_interactive_diagnostic_candidate(
    artifacts_root: &Path,
    proof_workdir: &Path,
    shared_inputs: &SharedInputs,
    round: usize,
    sequence: usize,
    mode: CandidateKind,
    candidate_path: &Path,
    upload_path: &Path,
) -> Result<(PathBuf, PathBuf)> {
    let upload_metadata = std::fs::symlink_metadata(upload_path).map_err(|source| Error::Read {
        path: upload_path.to_owned(),
        source,
    })?;
    if !upload_metadata.file_type().is_file() || upload_metadata.file_type().is_symlink() {
        return Err(Error::ProofAgentCommand(format!(
            "interactive {} candidate {} is not a regular upload file",
            mode.as_str(),
            candidate_path.display()
        )));
    }
    let snapshot_dir = artifacts_root.join(format!(
        "proof-stage/proof-agent/rounds/{round:02}/interactive-diagnostics/{sequence:02}/checked-workspace"
    ));
    let parent = snapshot_dir.parent().expect("diagnostic snapshot parent");
    std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
        path: parent.to_owned(),
        source,
    })?;
    let stage = tempfile::Builder::new()
        .prefix(".snapshot-")
        .tempdir_in(parent)
        .map_err(|source| Error::CreateDir {
            path: parent.to_owned(),
            source,
        })?;
    std::fs::set_permissions(stage.path(), std::fs::Permissions::from_mode(0o700)).map_err(
        |source| Error::Write {
            path: stage.path().to_owned(),
            source,
        },
    )?;
    shared_inputs.link_into(stage.path())?;
    let candidate_relative = match mode {
        CandidateKind::Problem | CandidateKind::Scratch => Path::new("Problem.v"),
        CandidateKind::Module => candidate_path,
    };
    let snapshot_candidate = stage.path().join(candidate_relative);
    if let Some(parent) = snapshot_candidate.parent() {
        std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
            path: parent.to_owned(),
            source,
        })?;
    }
    if mode == CandidateKind::Module {
        let source_problem = proof_workdir.join("Problem.v");
        let destination_problem = stage.path().join("Problem.v");
        std::fs::copy(&source_problem, &destination_problem)
            .map(|_| ())
            .map_err(|source| Error::Write {
                path: destination_problem,
                source,
            })?;
    }
    std::fs::rename(upload_path, &snapshot_candidate).map_err(|source| Error::Write {
        path: snapshot_candidate.clone(),
        source,
    })?;
    std::fs::rename(stage.path(), &snapshot_dir).map_err(|source| Error::Write {
        path: snapshot_dir.clone(),
        source,
    })?;
    let candidate = snapshot_dir.join(candidate_relative);
    Ok((snapshot_dir, candidate))
}
