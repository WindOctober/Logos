use serde::Serialize;

use crate::diagnostics::features::FeatureSummary;
use crate::diagnostics::rel_alignment::RelPlanAlignmentSummary;
use crate::diagnostics::rel_audit::RelShapeSummary;
use crate::diagnostics::scalar_audit::ScalarOpSummary;
use crate::diagnostics::semantic_scalar_audit::{
    SemanticScalarExampleGroups, SemanticScalarExamples, SemanticScalarSummary,
};
use crate::diagnostics::support_audit::{SupportConsistencySummary, SupportSummary};
use crate::error::{Error, Result};

pub trait JsonReport: Serialize {
    fn scanned_files(&self) -> usize;
    fn failed_files(&self) -> usize;
}

macro_rules! impl_json_report {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl JsonReport for $ty {
                fn scanned_files(&self) -> usize {
                    self.scanned_files
                }

                fn failed_files(&self) -> usize {
                    self.failed_files
                }
            }
        )+
    };
}

impl_json_report!(
    FeatureSummary,
    ScalarOpSummary,
    SemanticScalarSummary,
    RelShapeSummary,
    RelPlanAlignmentSummary,
    SupportSummary,
    SupportConsistencySummary,
    SemanticScalarExamples,
    SemanticScalarExampleGroups,
);

pub fn run_report<T>(
    name: &'static str,
    build: impl FnOnce() -> T,
    extra_failure: impl FnOnce(&T) -> Option<String>,
) -> Result<()>
where
    T: JsonReport,
{
    let report = build();
    let text = serde_json::to_string_pretty(&report)
        .unwrap_or_else(|_| panic!("serializing {name} cannot fail"));
    println!("{text}");

    let failed = report.failed_files();
    let extra = extra_failure(&report);
    if failed == 0 && extra.is_none() {
        return Ok(());
    }

    let mut details = Vec::new();
    if let Some(extra) = extra {
        details.push(extra);
    }
    if failed != 0 {
        details.push(format!(
            "failed for {failed}/{} files",
            report.scanned_files()
        ));
    }
    Err(Error::CalciteQueryError(format!(
        "{name} {}",
        details.join(" and ")
    )))
}
