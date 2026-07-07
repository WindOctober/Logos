use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

const DEFAULT_CALCITE_IR_ARGS: &str = "--read postgres --write postgres";

pub fn repo_root() -> PathBuf {
    let current_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
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
    let switch = logos_repo_root.join(".opam");
    switch.join("_opam/bin").is_dir().then_some(switch)
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
