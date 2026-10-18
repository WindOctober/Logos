//! Lemma availability is a proof-resource policy, not another SQL semantics.
use super::*;
use crate::engine::config::LemmaAvailability;
use crate::engine::report::AuditFinding;
use std::process::Stdio;

const DIRECTORY: &str = "proof-stage/proof-agent/trusted-launcher";
const SCRIPT: &str = include_str!("../../../scripts/lemma-ablation.py");
const INSTRUCTIONS: &str = include_str!("../../../prompts/lemma-ablation.md");
const PRIMER: &str = include_str!("../../../prompts/semantic-primer-ablation.md");

pub(super) fn primer(selection: LemmaAvailability) -> &'static str {
    if selection.is_full() {
        FORMAL_SQL_SEMANTIC_PRIMER
    } else {
        PRIMER
    }
}

pub(super) fn instructions(selection: LemmaAvailability) -> String {
    if selection.is_full() {
        return proof_agent_instruction_body();
    }
    // Keep the operational contract in one place; omit the full-library route
    // recommendations and discovery surface, rather than maintaining four copies.
    let operational = FORMAL_SQL_PROOF_AGENT_PROMPT
        .split_once("## Writable and trusted files")
        .expect("prompt section")
        .1
        .split_once("## Proof engineering and soundness")
        .expect("prompt section")
        .0;
    format!(
        "{INSTRUCTIONS}\nAvailable pre-proved groups: bag={}, other={}.\n\n## Writable and trusted files{operational}",
        selection.bag, selection.other
    )
}

pub(super) fn select_prompt(prompt: String, selection: LemmaAvailability) -> String {
    if selection.is_full() {
        prompt
    } else {
        prompt.replace(&proof_agent_instruction_body(), &instructions(selection))
    }
}

pub(super) fn static_bytes(selection: LemmaAvailability) -> usize {
    if selection.is_full() {
        return static_prompt_and_primer_bytes();
    }
    instructions(selection).len() + primer(selection).len()
}

pub(super) fn prepare(artifacts: &ArtifactWriter, options: &Config) -> Result<()> {
    let directory = artifacts.root().join(DIRECTORY);
    if options.lemma_availability.is_full() {
        if directory.join("lemma-policy.json").exists() {
            return Err(Error::ProofAgentCommand(
                "lemma availability cannot change in an existing run; use a fresh log directory"
                    .into(),
            ));
        }
        return Ok(());
    }
    if !directory.join("lemma-policy.json").exists()
        && artifacts
            .root()
            .join("proof-stage/proof-agent/trusted-diagnostic-cache")
            .exists()
    {
        return Err(Error::ProofAgentCommand(
            "cannot enable ablation on an existing proof cache; use a fresh log directory".into(),
        ));
    }
    artifacts.write_text(format!("{DIRECTORY}/lemma-ablation.py"), SCRIPT)?;
    artifacts.write_text(
        format!("{DIRECTORY}/search-rocq-declarations.py"),
        FORMAL_SQL_DECLARATION_SEARCH_SCRIPT,
    )?;
    let authority = options
        .logos_repo_root
        .clone()
        .unwrap_or_else(crate::runtime::repo_root);
    let output = Command::new("python3")
        .arg(directory.join("lemma-ablation.py"))
        .arg("prepare")
        .arg("--authority")
        .arg(authority)
        .arg("--output")
        .arg(&directory)
        .arg("--baseline")
        .arg(artifacts.root().join("proof-stage/formal-sql/Problem.v"))
        .arg("--bag")
        .arg(if options.lemma_availability.bag {
            "on"
        } else {
            "off"
        })
        .arg("--other")
        .arg(if options.lemma_availability.other {
            "on"
        } else {
            "off"
        })
        .output()
        .map_err(|e| Error::ProofAgentCommand(format!("prepare lemma availability: {e}")))?;
    if !output.status.success() {
        return Err(Error::ProofAgentCommand(
            String::from_utf8_lossy(&output.stderr).into_owned(),
        ));
    }
    Ok(())
}

/// Called before either a prefix probe or compilation, and again on final
/// source audit. The policy is host-owned, never supplied by the candidate.
pub(super) fn audit(root: &Path, path: &str, text: &str) -> Vec<AuditFinding> {
    let directory = root.join(DIRECTORY);
    let policy = directory.join("lemma-policy.json");
    if !policy.exists() {
        return Vec::new();
    }
    let result = (|| -> std::io::Result<std::process::Output> {
        let mut child = Command::new("python3")
            .arg(directory.join("lemma-ablation.py"))
            .arg("source-check")
            .arg("--policy")
            .arg(policy)
            .arg("--source")
            .arg("-")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        child
            .stdin
            .take()
            .expect("piped stdin")
            .write_all(text.as_bytes())?;
        child.wait_with_output()
    })();
    match result {
        Ok(output) if output.status.success() => Vec::new(),
        output => vec![AuditFinding {
            path: path.into(),
            line: 1,
            token: "lemma availability".into(),
            excerpt: match output {
                Ok(output) => String::from_utf8_lossy(&output.stderr).trim().to_owned(),
                Err(error) => format!("cannot check lemma policy: {error}"),
            },
        }],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn profiles_keep_operational_contract_without_disabled_route_documents() {
        for bag in [true, false] {
            for other in [true, false] {
                let selection = LemmaAvailability { bag, other };
                let body = instructions(selection);
                assert!(body.contains("generated_queries_verified"));
                assert!(body.contains("--operation probe"));
                assert!(body.contains("VerificationCountermodel"));
                assert_eq!(
                    static_bytes(selection),
                    body.len() + primer(selection).len()
                );
                let prompt = select_prompt(
                    render_proof_agent_prompt(VerificationMode::OutcomeUnconditional, None, None),
                    selection,
                );
                assert!(prompt.contains(&body));
                if selection.is_full() {
                    assert_eq!(body, proof_agent_instruction_body());
                } else {
                    assert!(!body.contains("ProofAgentFacade.v"));
                    assert!(!body.contains("query_expr_{project,filter,group}"));
                    assert!(!primer(selection).contains("BagClosed"));
                    assert!(body.contains(&format!("bag={bag}, other={other}")));
                }
            }
        }
    }
}
