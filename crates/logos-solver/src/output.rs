use crate::engine::{BackendStatus, Evidence, SolverOutcome, SolverReport};
use crate::error::Result;

pub enum OutputFormat {
    Json,
    Pretty,
    Both,
}

pub fn print_report(report: &SolverReport, format: OutputFormat) -> Result<()> {
    match format {
        OutputFormat::Json => print_json(report),
        OutputFormat::Pretty => {
            print_pretty(report);
            Ok(())
        }
        OutputFormat::Both => {
            print_pretty(report);
            println!();
            print_json(report)
        }
    }
}

fn print_json(report: &SolverReport) -> Result<()> {
    println!("{}", serde_json::to_string_pretty(report)?);
    Ok(())
}

fn print_pretty(report: &SolverReport) {
    let (label, color) = outcome_label(report);
    println!("{}", color.paint(label));
    println!("Reason: {}", report.reason);

    if let Some(evidence) = report.counterexample.as_ref() {
        print_evidence(evidence);
    }

    if let Some(proof) = report.proof.as_ref() {
        let proof_label = match proof.backend_status {
            BackendStatus::ProofComplete => Color::Green.paint("proof complete"),
            BackendStatus::ProofAgentRunCompleted => {
                Color::Yellow.paint("proof agent completed; proof not marked complete")
            }
            BackendStatus::WorkspaceGenerated => Color::Cyan.paint("proof workspace generated"),
            BackendStatus::ProofAgentFailed => Color::Red.paint("proof agent failed"),
        };
        println!("Proof stage: {proof_label}");
        if let Some(agent) = proof.proof_agent.as_ref() {
            println!(
                "Proof agent: success={} elapsed={}ms",
                agent.success, agent.elapsed_ms
            );
        }
    }

    println!("Logs: {}", report.log_dir);
    println!("Elapsed: {}ms", report.elapsed_ms);
}

fn outcome_label(report: &SolverReport) -> (&'static str, Color) {
    match report.outcome {
        SolverOutcome::Equivalent => ("EQUIVALENCE PROVED", Color::Green),
        SolverOutcome::NotEquivalent => ("NOT EQUIVALENT", Color::Red),
        SolverOutcome::TransformOnly => ("TRANSFORM COMPLETE", Color::Cyan),
        SolverOutcome::EquivalenceVerificationIncomplete => {
            ("EQUIVALENCE VERIFICATION INCOMPLETE", Color::Yellow)
        }
        SolverOutcome::NeedsManualReview => ("MANUAL REVIEW REQUIRED", Color::Yellow),
        SolverOutcome::LlmAssessmentOnly => ("LLM ASSESSMENT COMPLETE", Color::Cyan),
    }
}

fn print_evidence(evidence: &Evidence) {
    match evidence {
        Evidence::DataDifference {
            witness_sql,
            diff_sample,
            ..
        } => {
            println!("Evidence: {}", Color::Red.paint("data difference"));
            println!("Witness SQL: {}", one_line(witness_sql));
            println!("Diff sample: {}", one_line(diff_sample));
        }
        Evidence::OutputSchemaMismatch { witness_sql, .. } => {
            println!("Evidence: {}", Color::Red.paint("output schema mismatch"));
            println!("Witness SQL: {}", one_line(witness_sql));
        }
    }
}

fn one_line(value: &str) -> String {
    const LIMIT: usize = 240;
    let compact = value.split_whitespace().collect::<Vec<_>>().join(" ");
    if compact.len() <= LIMIT {
        compact
    } else {
        format!("{}...", compact.chars().take(LIMIT).collect::<String>())
    }
}

#[derive(Debug, Clone, Copy)]
enum Color {
    Green,
    Red,
    Yellow,
    Cyan,
}

impl Color {
    fn paint(self, text: &str) -> String {
        format!("\x1b[{}m{text}\x1b[0m", self.code())
    }

    fn code(self) -> &'static str {
        match self {
            Color::Green => "32;1",
            Color::Red => "31;1",
            Color::Yellow => "33;1",
            Color::Cyan => "36;1",
        }
    }
}
