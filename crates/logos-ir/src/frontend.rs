use std::path::Path;
use std::process::Command;

use crate::calcite::CalciteFile;
use crate::convert_raw_file;
use crate::error::{Error, Result};
use crate::ir::LogosIrFile;

pub trait SqlIrFrontend {
    fn load_sql(&self, schema_path: &Path, query_path: &Path) -> Result<LogosIrFile>;
}

#[derive(Debug, Clone)]
pub struct ShellSqlIrFrontend {
    command: String,
}

impl ShellSqlIrFrontend {
    pub fn new(command: String) -> Self {
        Self { command }
    }
}

impl SqlIrFrontend for ShellSqlIrFrontend {
    fn load_sql(&self, schema_path: &Path, query_path: &Path) -> Result<LogosIrFile> {
        let command = format!(
            "{} --schema {} --sql {}",
            self.command,
            shell_quote(schema_path),
            shell_quote(query_path)
        );
        let output = Command::new("sh")
            .arg("-c")
            .arg(command)
            .output()
            .map_err(|source| Error::SqlIrFrontendCommand(source.to_string()))?;
        if !output.status.success() {
            return Err(Error::SqlIrFrontendCommand(
                String::from_utf8_lossy(&output.stderr).trim().to_owned(),
            ));
        }

        let raw: CalciteFile =
            serde_json::from_slice(&output.stdout).map_err(Error::SqlIrFrontendJson)?;
        convert_raw_file(raw)
    }
}

fn shell_quote(path: &Path) -> String {
    let value = path.to_string_lossy();
    format!("'{}'", value.replace('\'', "'\\''"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quotes_shell_paths() {
        assert_eq!(shell_quote(Path::new("a'b.sql")), "'a'\\''b.sql'");
    }
}
