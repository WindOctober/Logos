use std::process::Command;
use std::time::Instant;

use logos_ir::ShellSqlIrFrontend;

use crate::artifacts::ArtifactWriter;
use crate::core::VerificationInput;
use crate::core::lower_verification_input;
use crate::engine::config::Config;
use crate::engine::now_ms_since_epoch;
use crate::engine::report::{
    AgentAudit, AgentRunLog, AuditFinding, Backend, BackendStatus, ProofReport, ProofWorkspace,
};
use crate::error::{Error, Result};

pub const DEFAULT_PROOF_AGENT_COMMAND: &str = "codex exec --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check --cd /workspace/problem - < proof-agent-prompt.md && bash run-rocq-check.sh";

const FORMAL_SQL_LEMMA_GUIDE: &str = include_str!("../../../../theories/FormalSQL/LEMMA_GUIDE.md");
const FORMAL_SQL_PROOF_AGENT_PROMPT: &str = include_str!("../../prompts/proof-agent.md");
const FORMAL_SQL_ROCQ_CHECK_SCRIPT: &str = include_str!("../../scripts/run-rocq-check.sh");
const FORMAL_SQL_DOCKER_AGENT_SCRIPT: &str =
    include_str!("../../scripts/run-proof-agent-docker.sh");

pub(super) fn run_proof_stage(
    artifacts: &ArtifactWriter,
    input: &VerificationInput,
    options: &Config,
) -> Result<ProofReport> {
    let started = Instant::now();
    let ir_frontend = ShellSqlIrFrontend::new(options.calcite_ir_command.clone());
    let ir_input = input.load_ir(&ir_frontend)?;
    artifacts.write_json("input/schema-ir.json", ir_input.schema_ir())?;
    artifacts.write_json("input/source-ir.json", ir_input.source_query_ir())?;
    artifacts.write_json("input/target-ir.json", ir_input.target_query_ir())?;

    let lowering_report = lower_verification_input(&ir_input);
    if let Some(schema) = lowering_report.schema.schema.as_ref() {
        artifacts.write_text("proof-stage/formal-sql/Schema.v", &schema.rocq_module)?;
    }
    if let Some(query_module) = lowering_report.query_module.as_ref() {
        artifacts.write_text(
            "proof-stage/formal-sql/Queries.v",
            &query_module.rocq_module,
        )?;
    }
    if let Some(proof_module) = lowering_report.proof_module.as_ref() {
        artifacts.write_text(
            "proof-stage/formal-sql/Problem.v",
            &proof_module.rocq_module,
        )?;
    }
    let proof_workspace = write_proof_workspace(artifacts)?;
    artifacts.write_json("proof-stage/formal-sql-lowering.json", &lowering_report)?;
    let proof_agent = if options.run_proof_agent {
        Some(execute_proof_agent(artifacts, options)?)
    } else {
        None
    };
    let backend_status = match &proof_agent {
        Some(run) if run.success => BackendStatus::ProofAgentRunCompleted,
        Some(_) => BackendStatus::ProofAgentFailed,
        None => BackendStatus::WorkspaceGenerated,
    };
    let status_reason = match &proof_agent {
        Some(run) if run.success => {
            "FormalSQL/Rocq proof agent run completed; equivalence proof is not marked complete yet"
                .to_owned()
        }
        Some(_) => "FormalSQL/Rocq proof agent failed; see proof-stage/proof-agent logs".to_owned(),
        None => {
            "FormalSQL/Rocq proof backend generated a proof workspace; automated proof search is not enabled"
                .to_owned()
        }
    };
    let report = ProofReport {
        backend: Backend::FormalSqlRocq,
        backend_status,
        status_reason,
        proof_workspace: Some(proof_workspace),
        proof_agent,
        elapsed_ms: started.elapsed().as_millis(),
    };
    artifacts.write_json("proof-stage/report.json", &report)?;
    Ok(report)
}

fn execute_proof_agent(artifacts: &ArtifactWriter, options: &Config) -> Result<AgentRunLog> {
    let command = options.proof_agent_command.clone();
    let docker_image = options.proof_docker_image.clone();
    let started_ms_since_epoch = now_ms_since_epoch();
    let started = Instant::now();
    let stdout_path = "proof-stage/proof-agent/stdout.txt";
    let stderr_path = "proof-stage/proof-agent/stderr.txt";
    let script_path = artifacts
        .root()
        .join("proof-stage/formal-sql/run-proof-agent-docker.sh");
    let logos_repo_root = options
        .logos_repo_root
        .clone()
        .map(Ok)
        .unwrap_or_else(std::env::current_dir)
        .map_err(|source| Error::ProofAgentCommand(source.to_string()))?;

    let mut process = Command::new("bash");
    process
        .arg(&script_path)
        .env("LOGOS_REPO_ROOT", logos_repo_root)
        .env("LOGOS_SOLVER_IMAGE", &docker_image)
        .env("LOGOS_PROOF_AGENT_COMMAND", &command);
    if let Some(switch) = options.proof_rocq_opam_switch.as_ref() {
        process.env("LOGOS_ROCQ_OPAM_SWITCH", switch);
    }

    let output = match process.output() {
        Ok(output) => output,
        Err(source) => {
            let audit = audit_proof_workspace(artifacts)?;
            let log = AgentRunLog {
                command,
                docker_image,
                started_ms_since_epoch,
                elapsed_ms: started.elapsed().as_millis(),
                success: false,
                exit_code: None,
                stdout_path: stdout_path.to_owned(),
                stderr_path: stderr_path.to_owned(),
                stdout_bytes: 0,
                stderr_bytes: 0,
                audit,
                error: Some(source.to_string()),
            };
            artifacts.write_json("proof-stage/proof-agent/run.json", &log)?;
            return Err(Error::ProofAgentCommand(source.to_string()));
        }
    };

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    artifacts.write_text(stdout_path, stdout.as_ref())?;
    artifacts.write_text(stderr_path, stderr.as_ref())?;
    let audit = audit_proof_workspace(artifacts)?;
    let success = output.status.success() && audit.passed;
    let log = AgentRunLog {
        command,
        docker_image,
        started_ms_since_epoch,
        elapsed_ms: started.elapsed().as_millis(),
        success,
        exit_code: output.status.code(),
        stdout_path: stdout_path.to_owned(),
        stderr_path: stderr_path.to_owned(),
        stdout_bytes: output.stdout.len(),
        stderr_bytes: output.stderr.len(),
        audit,
        error: if success {
            None
        } else if !output.status.success() {
            Some(format!("proof agent exited with status {}", output.status))
        } else {
            Some("proof agent output failed deterministic proof audit".to_owned())
        },
    };
    artifacts.write_json("proof-stage/proof-agent/run.json", &log)?;
    Ok(log)
}

fn audit_proof_workspace(artifacts: &ArtifactWriter) -> Result<AgentAudit> {
    let proof_dir = artifacts.root().join("proof-stage/formal-sql");
    let mut scanned_files = Vec::new();
    let mut findings = Vec::new();
    for entry in std::fs::read_dir(&proof_dir).map_err(|source| Error::Read {
        path: proof_dir.clone(),
        source,
    })? {
        let entry = entry.map_err(|source| Error::Read {
            path: proof_dir.clone(),
            source,
        })?;
        let path = entry.path();
        if path.extension().and_then(|ext| ext.to_str()) != Some("v") {
            continue;
        }
        let relative = path
            .strip_prefix(artifacts.root())
            .unwrap_or(&path)
            .display()
            .to_string();
        scanned_files.push(relative.clone());
        let text = std::fs::read_to_string(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        findings.extend(audit_rocq_text(&relative, &text));
    }
    let audit = AgentAudit {
        passed: findings.is_empty(),
        scanned_files,
        findings,
    };
    artifacts.write_json("proof-stage/proof-agent/audit.json", &audit)?;
    Ok(audit)
}

fn audit_rocq_text(path: &str, text: &str) -> Vec<AuditFinding> {
    const BANNED_TOKENS: &[&str] = &[
        "Axiom",
        "Parameter",
        "Hypothesis",
        "Conjecture",
        "Variable",
        "Admitted",
        "admit",
        "sorry",
        "Abort",
        "Fail",
        "Unshelve",
    ];

    let mut findings = Vec::new();
    for (line_index, line) in text.lines().enumerate() {
        for token in BANNED_TOKENS {
            if contains_rocq_token(line, token) {
                findings.push(AuditFinding {
                    path: path.to_owned(),
                    line: line_index + 1,
                    token: (*token).to_owned(),
                    excerpt: line.trim().to_owned(),
                });
            }
        }
    }
    findings
}

fn contains_rocq_token(line: &str, token: &str) -> bool {
    let mut start = 0;
    while let Some(offset) = line[start..].find(token) {
        let token_start = start + offset;
        let token_end = token_start + token.len();
        let before = line[..token_start].chars().next_back();
        let after = line[token_end..].chars().next();
        if before.is_none_or(|c| !is_rocq_ident_char(c))
            && after.is_none_or(|c| !is_rocq_ident_char(c))
        {
            return true;
        }
        start = token_end;
    }
    false
}

fn is_rocq_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn write_proof_workspace(artifacts: &ArtifactWriter) -> Result<ProofWorkspace> {
    artifacts.write_text(
        "proof-stage/formal-sql/lemma-guide.md",
        FORMAL_SQL_LEMMA_GUIDE,
    )?;
    artifacts.write_text(
        "proof-stage/formal-sql/proof-agent-prompt.md",
        FORMAL_SQL_PROOF_AGENT_PROMPT,
    )?;
    artifacts.write_text(
        "proof-stage/formal-sql/run-rocq-check.sh",
        FORMAL_SQL_ROCQ_CHECK_SCRIPT,
    )?;
    artifacts.write_text(
        "proof-stage/formal-sql/run-proof-agent-docker.sh",
        FORMAL_SQL_DOCKER_AGENT_SCRIPT,
    )?;

    Ok(ProofWorkspace {
        generated_module_dir: "proof-stage/formal-sql".to_owned(),
        problem_path: "proof-stage/formal-sql/Problem.v".to_owned(),
        lemma_guide_path: "proof-stage/formal-sql/lemma-guide.md".to_owned(),
        proof_agent_prompt_path: "proof-stage/formal-sql/proof-agent-prompt.md".to_owned(),
        rocq_check_script_path: "proof-stage/formal-sql/run-rocq-check.sh".to_owned(),
        docker_agent_script_path: "proof-stage/formal-sql/run-proof-agent-docker.sh".to_owned(),
    })
}
