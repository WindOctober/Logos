use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

// Keep the solver's sourceSql byte/token authority in the same unquoted form
// as the submitted PostgreSQL program. The adapter's identify mode is safe for
// standalone ingestion after its quote-identity audit, but the solver does not
// consume that separate audit report and therefore must not infer authority
// from newly inserted quotes.
const DEFAULT_CALCITE_IR_ARGS: &str = "--read postgres --write postgres --no-identify";

pub fn repo_root() -> PathBuf {
    let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let child_logos = current_dir.join("Logos");
    if is_repo_root(&child_logos) {
        return child_logos;
    }
    current_dir
        .ancestors()
        .find(|path| is_repo_root(path))
        .map(PathBuf::from)
        .unwrap_or(current_dir)
}

pub fn default_run_dir() -> PathBuf {
    let millis = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .unwrap_or(0);
    repo_root()
        .join("var")
        .join("logos-solver")
        .join("runs")
        .join(format!("run-{millis}"))
}

pub fn calcite_ir_command(logos_repo_root: &Path) -> String {
    let script = logos_repo_root.join("scripts/calcite-ir-sqlglot");
    format!("{} {DEFAULT_CALCITE_IR_ARGS}", shell_quote_path(&script))
}

pub fn rocq_opam_switch(logos_repo_root: &Path) -> Option<PathBuf> {
    // External switches must be explicit; implicit parent-directory probing makes
    // an otherwise self-contained Logos checkout depend on its host layout.
    [
        std::env::var_os("LOGOS_ROCQ_OPAM_SWITCH").map(PathBuf::from),
        std::env::var_os("ROCQ_OPAM_SWITCH").map(PathBuf::from),
        std::env::var_os("OPAM_SWITCH").map(PathBuf::from),
        Some(logos_repo_root.join(".opam-rocq")),
        Some(logos_repo_root.join(".opam")),
    ]
    .into_iter()
    .flatten()
    .find(|switch| is_rocq_opam_switch(switch))
}

fn is_rocq_opam_switch(path: &Path) -> bool {
    path.join("_opam/bin/rocq").is_file()
}

fn is_repo_root(path: &Path) -> bool {
    path.join("vendor/FormalSQL/src").is_dir()
        && path.join("theories/FormalSQL").is_dir()
        && path.join("scripts/calcite-ir-sqlglot").is_file()
}

fn shell_quote_path(path: &Path) -> String {
    let text = path.to_string_lossy();
    format!("'{}'", text.replace('\'', "'\\''"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_calcite_command_preserves_solver_source_identifier_authority() {
        let command = calcite_ir_command(Path::new("/tmp/logos repo"));
        assert!(command.contains("scripts/calcite-ir-sqlglot"));
        assert!(command.contains("--read postgres --write postgres --no-identify"));
    }
}
