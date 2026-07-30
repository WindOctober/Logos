use clap::ValueEnum;
use serde::Serialize;

/// Selects the theorem strength generated for the Rocq proof stage.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, ValueEnum)]
#[serde(rename_all = "snake_case")]
pub enum VerificationMode {
    /// Both queries are safe on every conforming database and return the same
    /// result. This is the strongest mode.
    SafeUnconditional,
    /// Every success and every SQL runtime-error category is preserved.
    #[default]
    OutcomeUnconditional,
    /// Error-preserving equivalence holds under a structured, audited input
    /// precondition with a proved provenance obligation.
    Conditional,
}

impl VerificationMode {
    pub const fn label(self) -> &'static str {
        match self {
            Self::SafeUnconditional => "SAFE-UNCONDITIONAL",
            Self::OutcomeUnconditional => "OUTCOME-UNCONDITIONAL",
            Self::Conditional => "CONDITIONAL",
        }
    }
}
