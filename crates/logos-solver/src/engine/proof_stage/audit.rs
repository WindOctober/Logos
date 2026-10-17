//! Source-policy and verification-claim auditing. Kernel checking remains a separate boundary.

use crate::artifacts::ArtifactWriter;
use crate::core::VerificationMode;
use crate::engine::report::{AgentAudit, AuditFinding, PreconditionSource, VerificationClaimKind};
use crate::error::{Error, Result};
use std::path::Path;

use super::diagnostics::CandidateKind;
use super::workspace::valid_proof_module_stem;
use super::{
    PROOF_MODULE_DIRECTORY, PROOF_SOURCE_FILES, TRUSTED_PROBLEM_IMPORT_LINES, TrustedProofSources,
    validated_proof_module_sources,
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum AuditPurpose {
    Certificate,
    ManualReview,
}

/// Named audit output keeps the claim and its precondition evidence together.
pub(super) struct WorkspaceAudit {
    pub(super) audit: AgentAudit,
    pub(super) candidate_claim: Option<VerificationClaimKind>,
    pub(super) precondition_source: Option<PreconditionSource>,
    pub(super) precondition_definition: Option<String>,
}

#[cfg(test)]
pub(super) fn audit_proof_workspace(
    artifacts: &ArtifactWriter,
    proof_dir: &Path,
    trusted_sources: &TrustedProofSources,
) -> Result<AgentAudit> {
    audit_proof_workspace_for_mode(
        artifacts,
        proof_dir,
        trusted_sources,
        VerificationMode::SafeUnconditional,
        AuditPurpose::Certificate,
    )
    .map(|result| result.audit)
}

pub(super) fn audit_proof_workspace_for_mode(
    artifacts: &ArtifactWriter,
    proof_dir: &Path,
    trusted_sources: &TrustedProofSources,
    verification_mode: VerificationMode,
    purpose: AuditPurpose,
) -> Result<WorkspaceAudit> {
    let mut scanned_files = Vec::new();
    let mut findings = Vec::new();
    let mut problem_text = None;
    let mut problem_path = None;
    for name in PROOF_SOURCE_FILES {
        let path = proof_dir.join(name);
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
        if trusted_sources
            .get(name)
            .is_some_and(|expected| expected != &text)
        {
            findings.push(AuditFinding {
                path: relative.clone(),
                line: 1,
                token: "trusted source modified".to_owned(),
                excerpt: format!("{name} differs from the pre-agent generated source"),
            });
        }
        if *name == "Problem.v" {
            findings.extend(audit_rocq_text(&relative, &text));
            problem_text = Some(text);
            problem_path = Some(relative);
        }
    }
    for (module_relative, module_bytes) in
        validated_proof_module_sources(&proof_dir.join(PROOF_MODULE_DIRECTORY))?
    {
        let path = proof_dir.join(&module_relative);
        let relative = path
            .strip_prefix(artifacts.root())
            .unwrap_or(&path)
            .display()
            .to_string();
        let text = std::str::from_utf8(&module_bytes)
            .expect("validated proof module source remains UTF-8");
        scanned_files.push(relative.clone());
        findings.extend(audit_proof_module_rocq_text(&relative, text));
    }
    let problem_path = problem_path
        .as_deref()
        .expect("proof source registry always contains Problem.v");
    let problem_text = problem_text
        .as_deref()
        .expect("proof source registry always contains Problem.v");
    let (candidate_claim, precondition_source, precondition_definition) = if purpose
        == AuditPurpose::ManualReview
        && !problem_declares_final_theorem(problem_text, verification_mode)
    {
        // All source safety checks above still apply. A review request is
        // not a certificate: claim/precondition metadata need not exist.
        // Never use this relaxation for a candidate declaring a final theorem.
        let (claim, _) = classify_verification_claim(problem_path, problem_text);
        (claim, None, None)
    } else if verification_mode == VerificationMode::Conditional {
        let finding = reject_conditional_verification_claim(problem_path, problem_text);
        findings.extend(finding);
        let (source, finding) = classify_precondition_source(problem_path, problem_text);
        findings.extend(finding);
        let (definition, finding) = extract_precondition_definition(problem_path, problem_text);
        findings.extend(finding);
        (Some(VerificationClaimKind::Equivalence), source, definition)
    } else {
        let (claim, finding) = classify_verification_claim(problem_path, problem_text);
        findings.extend(finding);
        (claim, None, None)
    };
    let audit = AgentAudit {
        passed: findings.is_empty(),
        scanned_files,
        findings,
    };
    artifacts.write_json("proof-stage/proof-agent/audit.json", &audit)?;
    Ok(WorkspaceAudit {
        audit,
        candidate_claim,
        precondition_source,
        precondition_definition,
    })
}

pub(super) fn classify_verification_claim(
    path: &str,
    text: &str,
) -> (Option<VerificationClaimKind>, Option<AuditFinding>) {
    const NAME: &str = "generated_verification_claim";
    let uncommented = strip_rocq_comments(text);
    let declarations = rocq_sentences(&uncommented)
        .into_iter()
        .filter(|sentence| {
            let tokens = rocq_identifier_tokens(sentence);
            matches!(tokens.as_slice(), ["Definition", NAME, ..])
        })
        .collect::<Vec<_>>();
    let tokens = declarations
        .first()
        .map(|declaration| rocq_identifier_tokens(declaration));
    let claim = match tokens.as_deref() {
        Some(
            [
                "Definition",
                NAME,
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "verification_claim_kind",
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "VerificationEquivalence",
            ],
        ) if declarations.len() == 1 => Some(VerificationClaimKind::Equivalence),
        Some(
            [
                "Definition",
                NAME,
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "verification_claim_kind",
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "VerificationCountermodel",
            ],
        ) if declarations.len() == 1 => Some(VerificationClaimKind::FormalCountermodel),
        _ => None,
    };
    if claim.is_some() {
        return (claim, None);
    }

    let line = text
        .find(NAME)
        .map(|offset| text[..offset].lines().count())
        .unwrap_or(1);
    let excerpt = text
        .lines()
        .find(|line| line.contains(NAME))
        .map(str::trim)
        .unwrap_or("missing generated_verification_claim definition")
        .to_owned();
    (
        None,
        Some(AuditFinding {
            path: path.to_owned(),
            line,
            token: NAME.to_owned(),
            excerpt: format!(
                "{excerpt}; unconditional proofs must declare the fully qualified verification_claim_kind type and exactly one direct, fully qualified VerificationEquivalence or VerificationCountermodel constructor"
            ),
        }),
    )
}

pub(super) fn reject_conditional_verification_claim(
    path: &str,
    text: &str,
) -> Option<AuditFinding> {
    const NAME: &str = "generated_verification_claim";
    let uncommented = strip_rocq_comments(text);
    let declaration = rocq_sentences(&uncommented).into_iter().find(|sentence| {
        let tokens = rocq_identifier_tokens(sentence);
        matches!(tokens.as_slice(), ["Definition", NAME, ..])
    })?;
    let line = text
        .find(NAME)
        .map(|offset| text[..offset].lines().count())
        .unwrap_or(1);
    Some(AuditFinding {
        path: path.to_owned(),
        line,
        token: NAME.to_owned(),
        excerpt: format!(
            "{}; conditional mode has only the precondition-qualified equivalence claim and forbids an unconditional countermodel selector",
            declaration.trim()
        ),
    })
}

pub(super) fn classify_precondition_source(
    path: &str,
    text: &str,
) -> (Option<PreconditionSource>, Option<AuditFinding>) {
    const NAME: &str = "generated_precondition_source";
    let uncommented = strip_rocq_comments(text);
    let declarations = rocq_sentences(&uncommented)
        .into_iter()
        .filter(|sentence| {
            let tokens = rocq_identifier_tokens(sentence);
            matches!(tokens.as_slice(), ["Definition", NAME, ..])
        })
        .collect::<Vec<_>>();
    let tokens = declarations
        .first()
        .map(|declaration| rocq_identifier_tokens(declaration));
    let source = match tokens.as_deref() {
        Some(
            [
                "Definition",
                NAME,
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "precondition_source",
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "PreconditionDerived",
            ],
        ) if declarations.len() == 1 => Some(PreconditionSource::Derived),
        Some(
            [
                "Definition",
                NAME,
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "precondition_source",
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "PreconditionExternal",
            ],
        ) if declarations.len() == 1 => Some(PreconditionSource::External),
        _ => None,
    };
    if source.is_some() {
        return (source, None);
    }

    let line = text
        .find(NAME)
        .map(|offset| text[..offset].lines().count())
        .unwrap_or(1);
    let excerpt = text
        .lines()
        .find(|line| line.contains(NAME))
        .map(str::trim)
        .unwrap_or("missing generated_precondition_source definition")
        .to_owned();
    (
        None,
        Some(AuditFinding {
            path: path.to_owned(),
            line,
            token: NAME.to_owned(),
            excerpt: format!(
                "{excerpt}; conditional proofs must declare the fully qualified precondition_source type and exactly one direct, fully qualified PreconditionDerived or PreconditionExternal constructor"
            ),
        }),
    )
}

pub(super) fn extract_precondition_definition(
    path: &str,
    text: &str,
) -> (Option<String>, Option<AuditFinding>) {
    const NAME: &str = "generated_precondition";
    let uncommented = strip_rocq_comments(text);
    let definitions = rocq_sentences(&uncommented)
        .into_iter()
        .filter(|sentence| {
            let tokens = rocq_identifier_tokens(sentence);
            matches!(
                tokens.as_slice(),
                [
                    "Definition",
                    NAME,
                    "Logos",
                    "FormalSQL",
                    "VerificationConditions",
                    "verification_condition",
                    ..
                ]
            )
        })
        .collect::<Vec<_>>();
    if let [definition] = definitions.as_slice() {
        return (Some(definition.trim().to_owned()), None);
    }

    let line = text
        .lines()
        .position(|line| {
            let tokens = rocq_identifier_tokens(line);
            matches!(tokens.as_slice(), ["Definition", NAME, ..])
        })
        .map(|line| line + 1)
        .unwrap_or(1);
    (
        None,
        Some(AuditFinding {
            path: path.to_owned(),
            line,
            token: NAME.to_owned(),
            excerpt: format!(
                "conditional proofs must contain exactly one direct {NAME} definition; found {}",
                definitions.len()
            ),
        }),
    )
}

fn rocq_identifier_tokens(text: &str) -> Vec<&str> {
    text.split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .filter(|token| !token.is_empty())
        .collect()
}

fn rocq_sentences(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut sentences = Vec::new();
    let mut start = 0usize;
    let mut index = 0usize;
    let mut in_string = false;
    while index < bytes.len() {
        if bytes[index] == b'"' {
            if in_string && index + 1 < bytes.len() && bytes[index + 1] == b'"' {
                index += 2;
                continue;
            }
            in_string = !in_string;
        } else if !in_string
            && bytes[index] == b'.'
            && bytes
                .get(index + 1)
                .is_none_or(|next| next.is_ascii_whitespace())
        {
            sentences.push(&text[start..=index]);
            start = index + 1;
        }
        index += 1;
    }
    if text[start..]
        .chars()
        .any(|character| !character.is_whitespace())
    {
        sentences.push(&text[start..]);
    }
    sentences
}

pub(super) fn problem_declares_final_theorem(
    text: &str,
    verification_mode: VerificationMode,
) -> bool {
    let required_name = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "generated_queries_verified"
        }
        VerificationMode::Conditional => "generated_queries_equivalent",
    };
    let uncommented = strip_rocq_comments(text);
    rocq_sentences(&uncommented).into_iter().any(|sentence| {
        let tokens = rocq_identifier_tokens(sentence);
        matches!(tokens.as_slice(), ["Theorem", name, ..] if *name == required_name)
    })
}

pub(super) fn strip_rocq_comments(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut output = Vec::with_capacity(bytes.len());
    let mut index = 0;
    let mut comment_depth = 0usize;
    let mut in_string = false;
    while index < bytes.len() {
        if comment_depth > 0 {
            if bytes[index..].starts_with(b"(*") {
                comment_depth += 1;
                output.extend_from_slice(b"  ");
                index += 2;
            } else if bytes[index..].starts_with(b"*)") {
                comment_depth -= 1;
                output.extend_from_slice(b"  ");
                index += 2;
            } else {
                output.push(if bytes[index] == b'\n' { b'\n' } else { b' ' });
                index += 1;
            }
            continue;
        }

        if !in_string && bytes[index..].starts_with(b"(*") {
            comment_depth = 1;
            output.extend_from_slice(b"  ");
            index += 2;
        } else if bytes[index] == b'"' {
            output.push(bytes[index]);
            index += 1;
            if in_string && index < bytes.len() && bytes[index] == b'"' {
                output.push(bytes[index]);
                index += 1;
            } else {
                in_string = !in_string;
            }
        } else {
            output.push(bytes[index]);
            index += 1;
        }
    }
    String::from_utf8(output).expect("comment stripping preserves UTF-8 input")
}

pub(super) fn audit_rocq_text(path: &str, text: &str) -> Vec<AuditFinding> {
    audit_rocq_text_with_mode(path, text, CandidateKind::Problem)
}

pub(super) fn audit_scratch_rocq_text(path: &str, text: &str) -> Vec<AuditFinding> {
    audit_rocq_text_with_mode(path, text, CandidateKind::Scratch)
}

pub(super) fn audit_proof_module_rocq_text(path: &str, text: &str) -> Vec<AuditFinding> {
    audit_rocq_text_with_mode(path, text, CandidateKind::Module)
}

fn audit_rocq_text_with_mode(path: &str, text: &str, mode: CandidateKind) -> Vec<AuditFinding> {
    const ALWAYS_BANNED_TOKENS: &[&str] = &[
        "Axiom",
        "Axioms",
        "Parameter",
        "Parameters",
        "Hypothesis",
        "Hypotheses",
        "Conjecture",
        "Conjectures",
        "Coercion",
        "Admitted",
        "Admit",
        "admit",
        "sorry",
        "Abort",
        "Fail",
        "Unshelve",
        "Load",
        "LoadPath",
        "Redirect",
        "Print",
        "Write",
        "Chdir",
        "Cd",
        "System",
        "Declare",
        "Unset",
        "bypass_check",
        "exact_no_check",
        "change_no_check",
        "vm_cast_no_check",
        "native_cast_no_check",
        "Notation",
        "Infix",
        "Abbreviation",
        "Reserved",
        "Delimit",
        "Bind",
        "Tactic",
        "Ltac",
        "Ltac2",
    ];
    const FINAL_ONLY_BANNED_TOKENS: &[&str] =
        &["Variable", "Variables", "Context", "Module", "Section"];
    const SCRATCH_ONLY_BANNED_TOKENS: &[&str] = &["Defined"];

    let mut findings = Vec::new();
    for (line_index, line) in text.lines().enumerate() {
        let mode_tokens = match mode {
            CandidateKind::Problem => FINAL_ONLY_BANNED_TOKENS,
            CandidateKind::Module | CandidateKind::Scratch => SCRATCH_ONLY_BANNED_TOKENS,
        };
        for token in ALWAYS_BANNED_TOKENS.iter().chain(mode_tokens) {
            if contains_rocq_token(line, token) {
                findings.push(AuditFinding {
                    path: path.to_owned(),
                    line: line_index + 1,
                    token: (*token).to_owned(),
                    excerpt: line.trim().to_owned(),
                });
            }
        }
        if is_untrusted_problem_import(line) {
            findings.push(AuditFinding {
                path: path.to_owned(),
                line: line_index + 1,
                token: "untrusted import".to_owned(),
                excerpt: line.trim().to_owned(),
            });
        }
    }
    let has_opaque_qed = if matches!(mode, CandidateKind::Module | CandidateKind::Scratch) {
        let uncommented = strip_rocq_comments(text);
        rocq_sentences(&uncommented)
            .into_iter()
            .any(|sentence| rocq_identifier_tokens(sentence).as_slice() == ["Qed"])
    } else {
        true
    };
    if !has_opaque_qed {
        findings.push(AuditFinding {
            path: path.to_owned(),
            line: 1,
            token: "missing Qed".to_owned(),
            excerpt:
                "scratch and proof-module diagnostics must contain at least one opaque Qed subgoal"
                    .to_owned(),
        });
    }
    findings
}

fn is_untrusted_problem_import(line: &str) -> bool {
    let line = line.trim();
    if !["Require", "Import", "Export", "Include"]
        .iter()
        .any(|token| contains_rocq_token(line, token))
    {
        return false;
    }
    if is_agent_proof_module_import(line) {
        return false;
    }
    !TRUSTED_PROBLEM_IMPORT_LINES
        .iter()
        .any(|trusted| trusted == line)
}

fn is_agent_proof_module_import(line: &str) -> bool {
    const PREFIX: &str = "From LogosGenerated.ProofModules Require Import ";
    let Some(body) = line
        .strip_prefix(PREFIX)
        .and_then(|rest| rest.strip_suffix('.'))
    else {
        return false;
    };
    !body.is_empty() && body.split_ascii_whitespace().all(valid_proof_module_stem)
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
