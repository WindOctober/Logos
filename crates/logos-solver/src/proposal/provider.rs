use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use crate::error::{Error, Result};

pub trait Provider {
    fn complete(&self, prompt: &str, output_path: &Path) -> Result<Completion>;
    fn command_summary(&self) -> Option<&str> {
        None
    }
}

#[derive(Debug, Clone)]
pub struct CommandProvider {
    command: String,
}

#[derive(Debug, Clone)]
pub struct Completion {
    pub stdout: String,
    pub stderr: String,
    pub exit_code: Option<i32>,
    pub success: bool,
}

impl CommandProvider {
    pub fn new(command: String) -> Self {
        Self { command }
    }
}

impl Provider for CommandProvider {
    fn complete(&self, prompt: &str, output_path: &Path) -> Result<Completion> {
        let mut child = Command::new("sh")
            .arg("-c")
            .arg(&self.command)
            .env("LOGOS_PROPOSAL_JSON", output_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|source| Error::ProposalCommand(source.to_string()))?;

        let stdin = child.stdin.as_mut().ok_or_else(|| {
            Error::ProposalCommand("failed to open agent command stdin".to_owned())
        })?;
        stdin
            .write_all(prompt.as_bytes())
            .map_err(|source| Error::ProposalCommand(source.to_string()))?;

        let output = child
            .wait_with_output()
            .map_err(|source| Error::ProposalCommand(source.to_string()))?;
        Ok(Completion {
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            exit_code: output.status.code(),
            success: output.status.success(),
        })
    }

    fn command_summary(&self) -> Option<&str> {
        Some(&self.command)
    }
}
