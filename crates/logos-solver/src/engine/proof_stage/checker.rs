//! Trusted compiler invocation and environment preflight. Only compiler success grants authority.

use crate::artifacts::ArtifactWriter;
use crate::engine::config::Config;
use crate::engine::now_ms_since_epoch;
use crate::engine::report::{DiagnosticCheckerInvocation, TrustedCheckInvocation};
use crate::engine::rocq_session::{IncrementalDiagnostics, SessionKey};
use crate::error::{Error, Result};
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::process::{Command, Output};
use std::time::{Duration, Instant};

use super::diagnostics::CandidateKind;
use super::workspace::trusted_diagnostic_cache_directory;
use super::{
    FIXED_HOST_LOCALE, TRUSTED_CHECKER_HOME, TRUSTED_CHECKER_PATH, TRUSTED_HOST_BASH,
    TRUSTED_HOST_TIMEOUT, TRUSTED_ROCQ_ENVIRONMENT_FAILURE_EXIT_CODE, write_pretty_json_file,
    write_trusted_rocq_checker,
};

#[derive(Clone)]
pub(super) enum CheckMode {
    Full,
    Preflight,
    WitnessPreflight,
    ProblemDiagnostic {
        timeout_seconds: u64,
    },
    ScratchDiagnostic {
        timeout_seconds: u64,
    },
    InteractiveDiagnostic {
        logical_name: String,
    },
    ModuleDiagnostic {
        timeout_seconds: u64,
        candidate_path: String,
    },
}

pub(super) fn run_trusted_rocq_check(
    trusted_checker_path: &Path,
    checked_workspace: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    timeout: Duration,
) -> std::io::Result<Output> {
    trusted_rocq_check_command(
        trusted_checker_path,
        checked_workspace,
        logos_repo_root,
        rocq_opam_switch,
        timeout,
        CheckMode::Full,
    )
    .output()
}

pub(super) fn run_host_diagnostic_rocq_check(
    trusted_checker_path: &Path,
    checked_workspace: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    candidate_mode: CandidateKind,
    candidate_path: &str,
    requested_timeout_seconds: u64,
    effective_timeout_seconds: u64,
    incremental: Option<(&mut IncrementalDiagnostics, &str)>,
) -> (DiagnosticCheckerInvocation, Option<Output>) {
    let started_at_unix_ms = now_ms_since_epoch();
    let started = Instant::now();
    let trusted_mode = match candidate_mode {
        CandidateKind::Module => CheckMode::ModuleDiagnostic {
            timeout_seconds: effective_timeout_seconds,
            candidate_path: candidate_path.to_owned(),
        },
        CandidateKind::Problem => CheckMode::ProblemDiagnostic {
            timeout_seconds: effective_timeout_seconds,
        },
        CandidateKind::Scratch => CheckMode::ScratchDiagnostic {
            timeout_seconds: effective_timeout_seconds,
        },
    };
    let result = (|| -> std::io::Result<Output> {
        let mut incremental = incremental;
        let mut compiler_key = None;
        let deadline = started + Duration::from_secs(effective_timeout_seconds);
        let mut note = String::new();
        if let Some((session, source)) = incremental.as_mut() {
            let manifest =
                trusted_diagnostic_cache_directory(trusted_checker_path).join("SHA256SUMS");
            if let Ok(manifest) = std::fs::read(&manifest) {
                let logical_name = if candidate_mode == CandidateKind::Module {
                    format!(
                        "LogosGenerated.{}",
                        candidate_path.trim_end_matches(".v").replace('/', ".")
                    )
                } else {
                    "LogosGenerated.Problem".to_owned()
                };
                // The broker lifetime binds authority, runtime and generated
                // workspace generation. Publishing a module changes this manifest
                // and invalidates the entire isolated REPL snapshot.
                let key = SessionKey::new(manifest, logical_name.clone());
                compiler_key = Some(key.clone());
                let mut command = trusted_rocq_check_command(
                    trusted_checker_path,
                    checked_workspace,
                    logos_repo_root,
                    rocq_opam_switch,
                    Duration::from_secs(effective_timeout_seconds),
                    CheckMode::InteractiveDiagnostic { logical_name },
                );
                if !session.prepare(&key) {
                    note = "LOGOS_ROCQ_INCREMENTAL cold=true compiler_required=true\n".to_owned();
                } else {
                    match session.check(&key, source, &mut command, deadline) {
                        Ok(diagnostic) => {
                            note = format!(
                                "LOGOS_ROCQ_INCREMENTAL reused_sentences={} executed_sentences={} compiler_required={}\n",
                                diagnostic.reused,
                                diagnostic.executed,
                                diagnostic.rejection.is_none()
                            );
                            if let Some(rejection) = diagnostic.rejection {
                                return Ok(Output {
                                    status: std::process::ExitStatus::from_raw(1 << 8),
                                    stdout: Vec::new(),
                                    stderr: format!(
                                        "{note}Candidate: {candidate_path}\n{rejection}"
                                    )
                                    .into_bytes(),
                                });
                            }
                        }
                        Err(error) if error.kind() == std::io::ErrorKind::TimedOut => {
                            let stderr = format!(
                                "LOGOS_ROCQ_INCREMENTAL timed_out=true session_discarded=true\n{error}\n"
                            ).into_bytes();
                            return Ok(Output {
                                status: std::process::ExitStatus::from_raw(124 << 8),
                                stdout: Vec::new(),
                                stderr,
                            });
                        }
                        Err(error) => {
                            note = format!("LOGOS_ROCQ_INCREMENTAL fallback=true reason={error}\n");
                        }
                    }
                }
            } else {
                // Let the existing checker classify absent/corrupt environments.
                **session = IncrementalDiagnostics::default();
            }
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Ok(Output {
                status: std::process::ExitStatus::from_raw(124 << 8),
                stdout: Vec::new(),
                stderr: format!("{note}diagnostic deadline exhausted before compilation\n")
                    .into_bytes(),
            });
        }
        // Only this path can report success. It publishes exactly the same
        // checked objects/checkpoints as before the incremental optimization.
        let mut output = trusted_rocq_check_command(
            trusted_checker_path,
            checked_workspace,
            logos_repo_root,
            rocq_opam_switch,
            remaining,
            trusted_mode,
        )
        .output()?;
        if let (Some((session, _)), Some(key)) = (incremental, compiler_key) {
            session.observe_compiler(&key, output.status.code());
        }
        if !note.is_empty() {
            output.stderr.splice(..0, note.into_bytes());
        }
        Ok(output)
    })();
    match result {
        Ok(output) => {
            let exit_code = output.status.code();
            (
                DiagnosticCheckerInvocation {
                    sequence: None,
                    mode: None,
                    candidate_sha256: None,
                    candidate_path: None,
                    purpose: None,
                    compile_passed: None,
                    problem_compile_passed: None,
                    compile_checkpoint_advanced: None,
                    stdout_sha256: None,
                    stderr_sha256: None,
                    requested_timeout_seconds,
                    effective_timeout_seconds,
                    started_at_unix_ms,
                    elapsed_ms: started.elapsed().as_millis(),
                    exit_code,
                    timed_out: matches!(exit_code, Some(124 | 137)),
                    error: None,
                },
                Some(output),
            )
        }
        Err(source) => (
            DiagnosticCheckerInvocation {
                sequence: None,
                mode: None,
                candidate_sha256: None,
                candidate_path: None,
                purpose: None,
                compile_passed: Some(false),
                problem_compile_passed: Some(false),
                compile_checkpoint_advanced: None,
                stdout_sha256: None,
                stderr_sha256: None,
                requested_timeout_seconds,
                effective_timeout_seconds,
                started_at_unix_ms,
                elapsed_ms: started.elapsed().as_millis(),
                exit_code: None,
                timed_out: source.kind() == std::io::ErrorKind::TimedOut,
                error: Some(format!(
                    "failed to start host problem-only Rocq check: {source}"
                )),
            },
            None,
        ),
    }
}

pub(super) fn run_trusted_rocq_environment_preflight(
    trusted_checker_path: &Path,
    proof_workspace: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    timeout: Duration,
    witness_only: bool,
) -> std::io::Result<Output> {
    trusted_rocq_check_command(
        trusted_checker_path,
        proof_workspace,
        logos_repo_root,
        rocq_opam_switch,
        timeout,
        if witness_only {
            CheckMode::WitnessPreflight
        } else {
            CheckMode::Preflight
        },
    )
    .output()
}

pub(super) fn trusted_rocq_check_command(
    trusted_checker_path: &Path,
    checked_workspace: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    timeout: Duration,
    mode: CheckMode,
) -> Command {
    let trusted_cache_dir = trusted_diagnostic_cache_directory(trusted_checker_path);
    // Interactive sessions live for the broker lifetime, not one request's
    // timeout. The host transport bounds every request and kills the whole
    // session group on timeout/drop; the shell still owns scratch cleanup.
    let interactive = matches!(&mode, CheckMode::InteractiveDiagnostic { .. });
    let mut process = Command::new(if interactive {
        TRUSTED_HOST_BASH
    } else {
        TRUSTED_HOST_TIMEOUT
    });
    process
        .env_clear()
        .env("PATH", TRUSTED_CHECKER_PATH)
        .env("HOME", TRUSTED_CHECKER_HOME)
        .env("LC_ALL", FIXED_HOST_LOCALE)
        .env("LANG", FIXED_HOST_LOCALE);
    if !interactive {
        process
            .arg("--signal=TERM")
            .arg("--kill-after=5s")
            .arg(if timeout.subsec_nanos() == 0 {
                format!("{}s", timeout.as_secs().max(1))
            } else {
                format!("{}s", timeout.as_secs_f64())
            })
            .arg(TRUSTED_HOST_BASH);
    }
    process
        .arg(trusted_checker_path)
        .env("LOGOS_REPO_ROOT", logos_repo_root)
        .env("LOGOS_PROOF_WORKDIR", checked_workspace)
        .env("LOGOS_TRUSTED_ROCQ_CACHE_DIR", trusted_cache_dir);
    match mode {
        CheckMode::Full => {}
        CheckMode::Preflight => {
            process.arg("--preflight");
        }
        CheckMode::WitnessPreflight => {
            process.arg("--witness-preflight");
        }
        CheckMode::ProblemDiagnostic { timeout_seconds } => {
            process
                .arg("--problem-diagnostic")
                .arg("--timeout-seconds")
                .arg(timeout_seconds.to_string());
        }
        CheckMode::ScratchDiagnostic { timeout_seconds } => {
            process
                .arg("--scratch-diagnostic")
                .arg("--timeout-seconds")
                .arg(timeout_seconds.to_string());
        }
        CheckMode::InteractiveDiagnostic { logical_name } => {
            process
                .arg("--interactive-diagnostic")
                .arg("--logical-name")
                .arg(logical_name);
        }
        CheckMode::ModuleDiagnostic {
            timeout_seconds,
            candidate_path,
        } => {
            process
                .arg("--module-diagnostic")
                .arg("--candidate")
                .arg(candidate_path)
                .arg("--timeout-seconds")
                .arg(timeout_seconds.to_string());
        }
    }
    if let Some(switch) = rocq_opam_switch {
        process.env("LOGOS_ROCQ_OPAM_SWITCH", switch);
    }
    for name in [
        "LOGOS_SHARED_ROCQ_PREFIX_CACHE_DIR",
        "LOGOS_SHARED_ROCQ_CHECKER_RUNTIME_CACHE_DIR",
        "LOGOS_TRUSTED_ROCQ_AUTHORITY_SHA256",
    ] {
        if let Some(value) = std::env::var_os(name) {
            process.env(name, value);
        }
    }
    process
}

pub(super) fn persist_trusted_environment_preflight_evidence(
    artifacts: &ArtifactWriter,
    workspace_generation: usize,
    stdout: &[u8],
    stderr: &[u8],
    invocation: &TrustedCheckInvocation,
) -> Result<()> {
    if workspace_generation == 0 {
        return Err(Error::ProofAgentCommand(
            "proof workspace generation must be positive".to_owned(),
        ));
    }
    let evidence_root = artifacts.root().join(format!(
        "proof-stage/proof-agent/workspace-generations/{workspace_generation:04}/trusted-environment-preflight"
    ));
    let parent = evidence_root.parent().ok_or_else(|| {
        Error::ProofAgentCommand("trusted preflight evidence path has no parent".to_owned())
    })?;
    std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
        path: parent.to_owned(),
        source,
    })?;
    std::fs::create_dir(&evidence_root).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "refusing to replace create-once trusted preflight evidence {}: {source}",
            evidence_root.display()
        ))
    })?;
    for (name, bytes) in [("stdout.txt", stdout), ("stderr.txt", stderr)] {
        let path = evidence_root.join(name);
        std::fs::write(&path, bytes).map_err(|source| Error::Write { path, source })?;
    }
    let invocation_path = evidence_root.join("invocation.json");
    write_pretty_json_file(invocation_path.clone(), invocation).map_err(|source| Error::Write {
        path: invocation_path,
        source,
    })?;
    Ok(())
}

pub(super) fn validate_trusted_rocq_environment(
    artifacts: &ArtifactWriter,
    options: &Config,
    workspace_generation: usize,
    witness_only: bool,
) -> Result<TrustedCheckInvocation> {
    let trusted_checker_path = write_trusted_rocq_checker(artifacts)?;
    let proof_workspace = artifacts.root().join("proof-stage/formal-sql");
    let logos_repo_root = options
        .logos_repo_root
        .clone()
        .map(Ok)
        .unwrap_or_else(std::env::current_dir)
        .map_err(|source| Error::TrustedRocqEnvironment(source.to_string()))?;
    let timeout_seconds = options.proof_check_timeout_seconds;
    let started = Instant::now();
    let output = match run_trusted_rocq_environment_preflight(
        &trusted_checker_path,
        &proof_workspace,
        &logos_repo_root,
        options.proof_rocq_opam_switch.as_deref(),
        Duration::from_secs(timeout_seconds),
        witness_only,
    ) {
        Ok(output) => output,
        Err(source) => {
            let message = source.to_string();
            let invocation = TrustedCheckInvocation {
                timeout_seconds,
                elapsed_ms: started.elapsed().as_millis(),
                exit_code: None,
                timed_out: source.kind() == std::io::ErrorKind::TimedOut,
                error: Some(message.clone()),
            };
            persist_trusted_environment_preflight_evidence(
                artifacts,
                workspace_generation,
                &[],
                &[],
                &invocation,
            )?;
            return Err(Error::TrustedRocqEnvironment(message));
        }
    };
    let stderr = String::from_utf8_lossy(&output.stderr);
    let exit_code = output.status.code();
    let timed_out = matches!(exit_code, Some(124 | 137));
    let error = (!output.status.success())
        .then(|| format!("preflight exited with status {}: {}", output.status, stderr));
    let invocation = TrustedCheckInvocation {
        timeout_seconds,
        elapsed_ms: started.elapsed().as_millis(),
        exit_code,
        timed_out,
        error: error.clone(),
    };
    persist_trusted_environment_preflight_evidence(
        artifacts,
        workspace_generation,
        &output.stdout,
        &output.stderr,
        &invocation,
    )?;
    if output.status.success() {
        return Ok(invocation);
    }
    Err(Error::TrustedRocqEnvironment(
        error.expect("non-successful preflight has an error message"),
    ))
}

pub(super) fn is_trusted_rocq_environment_failure(exit_code: Option<i32>) -> bool {
    exit_code == Some(TRUSTED_ROCQ_ENVIRONMENT_FAILURE_EXIT_CODE)
}
