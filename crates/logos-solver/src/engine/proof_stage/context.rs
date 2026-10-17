//! Agent context materialization and validation of the on-disk context manifest.

use crate::artifacts::ArtifactWriter;
use crate::core::{VerificationInput, VerificationMode};
use crate::engine::report::ProofAgentContext;
use crate::error::{Error, Result};
use serde::Serialize;
use std::path::Path;

use super::{
    FORMAL_SQL_DECLARATION_SEARCH_SCRIPT, FORMAL_SQL_SEMANTIC_PRIMER, proof_agent_instruction_body,
    sha256_hex, static_prompt_and_primer_bytes,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct FileBinding {
    pub(super) path: String,
    pub(super) bytes: usize,
    pub(super) sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct ContextManifest {
    pub(super) schema_version: u32,
    authority: &'static str,
    verification_mode: VerificationMode,
    static_prompt_and_primer_bytes: usize,
    source_sql: FileBinding,
    target_sql: FileBinding,
    query_shape: FileBinding,
    ordered_signatures: FileBinding,
    observation_certificates: FileBinding,
    semantic_primer: FileBinding,
    declaration_search: FileBinding,
    schema_module: FileBinding,
    queries_module: FileBinding,
    witness_module: FileBinding,
    goal_module: FileBinding,
}

pub(super) struct PreparedContext {
    pub(super) manifest: ContextManifest,
    manifest_text: String,
    pub(super) report: ProofAgentContext,
}

pub(super) fn context_binding(path: impl Into<String>, bytes: &[u8]) -> FileBinding {
    FileBinding {
        path: path.into(),
        bytes: bytes.len(),
        sha256: sha256_hex(bytes),
    }
}

pub(super) fn write_proof_agent_context(
    artifacts: &ArtifactWriter,
    input: &VerificationInput,
    verification_mode: VerificationMode,
    query_shape: &str,
    ordered_signatures: &str,
    observation_certificates: &str,
    schema_module: &str,
    queries_module: &str,
    witness_module: &str,
    problem_module: &str,
    goal_module: &str,
) -> Result<PreparedContext> {
    let context_root = "proof-stage/formal-sql";
    let legacy_catalog_path = artifacts.root().join(context_root).join("lemma-catalog");
    if legacy_catalog_path.exists() {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context contains an obsolete routed lemma catalog at {}",
            legacy_catalog_path.display()
        )));
    }
    artifacts.write_text(format!("{context_root}/source.sql"), input.source_sql())?;
    artifacts.write_text(format!("{context_root}/target.sql"), input.target_sql())?;
    artifacts.write_text(format!("{context_root}/query-shape.json"), query_shape)?;
    artifacts.write_text(
        format!("{context_root}/ordered-signatures.json"),
        ordered_signatures,
    )?;
    artifacts.write_text(
        format!("{context_root}/observation-certificates.json"),
        observation_certificates,
    )?;
    artifacts.write_text(
        format!("{context_root}/semantic-primer.md"),
        FORMAL_SQL_SEMANTIC_PRIMER,
    )?;
    artifacts.write_text(
        format!("{context_root}/search-rocq-declarations.py"),
        FORMAL_SQL_DECLARATION_SEARCH_SCRIPT,
    )?;

    let static_bytes = static_prompt_and_primer_bytes();
    let manifest = ContextManifest {
        schema_version: 8,
        authority: "navigation context only; exact SQL is pipeline input and generated Rocq plus FormalSQL and the Rocq kernel remain authoritative",
        verification_mode,
        static_prompt_and_primer_bytes: static_bytes,
        source_sql: context_binding("source.sql", input.source_sql().as_bytes()),
        target_sql: context_binding("target.sql", input.target_sql().as_bytes()),
        query_shape: context_binding("query-shape.json", query_shape.as_bytes()),
        ordered_signatures: context_binding(
            "ordered-signatures.json",
            ordered_signatures.as_bytes(),
        ),
        observation_certificates: context_binding(
            "observation-certificates.json",
            observation_certificates.as_bytes(),
        ),
        semantic_primer: context_binding(
            "semantic-primer.md",
            FORMAL_SQL_SEMANTIC_PRIMER.as_bytes(),
        ),
        declaration_search: context_binding(
            "search-rocq-declarations.py",
            FORMAL_SQL_DECLARATION_SEARCH_SCRIPT.as_bytes(),
        ),
        schema_module: context_binding("Schema.v", schema_module.as_bytes()),
        queries_module: context_binding("Queries.v", queries_module.as_bytes()),
        witness_module: context_binding("Witness.v", witness_module.as_bytes()),
        goal_module: context_binding("Goal.v", goal_module.as_bytes()),
    };
    let manifest_text = serde_json::to_string_pretty(&manifest)? + "\n";
    artifacts.write_text(
        format!("{context_root}/context-manifest.json"),
        &manifest_text,
    )?;
    let generated_context_bytes = manifest.source_sql.bytes
        + manifest.target_sql.bytes
        + manifest.query_shape.bytes
        + manifest.ordered_signatures.bytes
        + manifest.observation_certificates.bytes
        + manifest.semantic_primer.bytes
        + manifest.declaration_search.bytes
        + manifest.schema_module.bytes
        + manifest.queries_module.bytes
        + manifest.witness_module.bytes
        + problem_module.len()
        + manifest.goal_module.bytes
        + manifest_text.len()
        // The primer is already counted through its context file above.
        + proof_agent_instruction_body().len();
    let report = ProofAgentContext {
        manifest_path: format!("{context_root}/context-manifest.json"),
        manifest_sha256: sha256_hex(manifest_text.as_bytes()),
        manifest_bytes: manifest_text.len(),
        source_sql_sha256: manifest.source_sql.sha256.clone(),
        source_sql_bytes: manifest.source_sql.bytes,
        target_sql_sha256: manifest.target_sql.sha256.clone(),
        target_sql_bytes: manifest.target_sql.bytes,
        query_shape_sha256: manifest.query_shape.sha256.clone(),
        query_shape_bytes: manifest.query_shape.bytes,
        ordered_signatures_sha256: manifest.ordered_signatures.sha256.clone(),
        ordered_signatures_bytes: manifest.ordered_signatures.bytes,
        observation_certificates_sha256: manifest.observation_certificates.sha256.clone(),
        observation_certificates_bytes: manifest.observation_certificates.bytes,
        schema_module_sha256: manifest.schema_module.sha256.clone(),
        schema_module_bytes: manifest.schema_module.bytes,
        queries_module_sha256: manifest.queries_module.sha256.clone(),
        queries_module_bytes: manifest.queries_module.bytes,
        witness_module_sha256: manifest.witness_module.sha256.clone(),
        witness_module_bytes: manifest.witness_module.bytes,
        problem_module_bytes: problem_module.len(),
        goal_module_bytes: manifest.goal_module.bytes,
        semantic_primer_bytes: manifest.semantic_primer.bytes,
        declaration_search_sha256: manifest.declaration_search.sha256.clone(),
        declaration_search_bytes: manifest.declaration_search.bytes,
        generated_context_bytes,
    };
    let prepared = PreparedContext {
        manifest,
        manifest_text,
        report,
    };
    validate_proof_agent_context(artifacts, &prepared)?;
    Ok(prepared)
}
fn validate_context_binding(root: &Path, binding: &FileBinding) -> Result<()> {
    let path = root.join(&binding.path);
    let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
        path: path.clone(),
        source,
    })?;
    if !metadata.file_type().is_file() {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context drift: {} is not a regular file",
            path.display()
        )));
    }
    let bytes = std::fs::read(&path).map_err(|source| Error::Read {
        path: path.clone(),
        source,
    })?;
    let observed_digest = sha256_hex(&bytes);
    if bytes.len() != binding.bytes || observed_digest != binding.sha256 {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context drift: {} expected {} bytes with SHA-256 {}, observed {} bytes with SHA-256 {}",
            path.display(),
            binding.bytes,
            binding.sha256,
            bytes.len(),
            observed_digest
        )));
    }
    Ok(())
}

pub(super) fn validate_proof_agent_context(
    artifacts: &ArtifactWriter,
    prepared: &PreparedContext,
) -> Result<()> {
    let root = artifacts.root().join("proof-stage/formal-sql");
    for binding in [
        &prepared.manifest.source_sql,
        &prepared.manifest.target_sql,
        &prepared.manifest.query_shape,
        &prepared.manifest.ordered_signatures,
        &prepared.manifest.observation_certificates,
        &prepared.manifest.semantic_primer,
        &prepared.manifest.declaration_search,
        &prepared.manifest.schema_module,
        &prepared.manifest.queries_module,
        &prepared.manifest.witness_module,
        &prepared.manifest.goal_module,
    ] {
        validate_context_binding(&root, binding)?;
    }
    let manifest_path = root.join("context-manifest.json");
    let manifest_text = std::fs::read_to_string(&manifest_path).map_err(|source| Error::Read {
        path: manifest_path.clone(),
        source,
    })?;
    if manifest_text != prepared.manifest_text {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context drift: {} differs from the host-generated manifest",
            manifest_path.display()
        )));
    }

    let legacy_catalog_path = root.join("lemma-catalog");
    if legacy_catalog_path.exists() {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context unexpectedly contains obsolete routed lemma catalog {}",
            legacy_catalog_path.display()
        )));
    }
    Ok(())
}
