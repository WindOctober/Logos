use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use crate::error::{Error, Result};
use crate::usage::{CodexInvocationUsage, UsageError, parse_codex_jsonl};

const COMMAND_PROVIDER_SHELL: &str = "/usr/bin/bash";
const COMMAND_PROVIDER_SHELL_ARGS: &[&str] = &["--noprofile", "--norc", "-c"];
const COMMAND_PROVIDER_FIXED_ENVIRONMENT: &[(&str, &str)] = &[
    ("HOME", "/nonexistent"),
    ("TMPDIR", "/tmp"),
    ("LC_ALL", "C"),
    ("LANG", "C"),
    ("TZ", "UTC"),
];
const COMMAND_PROVIDER_PARENT_ENVIRONMENT_ALLOWLIST: &[&str] = &[
    "PATH",
    "CODEX_HOME",
    "LOGOS_SOLVER_CODEX_HOME",
    "LOGOS_SOLVER_CODEX_CONFIG",
];

pub trait Provider {
    fn complete(&self, prompt: &str, output_path: &Path) -> Result<Completion>;
    fn resume(&self, prompt: &str, output_path: &Path, session_id: &str) -> Result<Completion> {
        let _ = (prompt, output_path, session_id);
        Err(Error::ProposalCommand(
            "counterexample provider does not support same-session resume".to_owned(),
        ))
    }
}

#[derive(Debug, Clone)]
pub struct CommandProvider {
    command: String,
    resume_command: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Completion {
    pub command: Option<String>,
    pub stdout: String,
    pub stderr: String,
    pub exit_code: Option<i32>,
    pub success: bool,
    pub usage: std::result::Result<CodexInvocationUsage, UsageError>,
}

impl CommandProvider {
    #[cfg(test)]
    pub fn new(command: String) -> Self {
        Self {
            command,
            resume_command: None,
        }
    }

    pub fn with_resume(command: String, resume_command: String) -> Self {
        Self {
            command,
            resume_command: Some(resume_command),
        }
    }

    fn run_command(&self, command: &str, prompt: &str, output_path: &Path) -> Result<Completion> {
        let mut process = Command::new(COMMAND_PROVIDER_SHELL);
        process
            .args(COMMAND_PROVIDER_SHELL_ARGS)
            .arg(command)
            .env_clear();
        for (name, value) in COMMAND_PROVIDER_FIXED_ENVIRONMENT {
            process.env(name, value);
        }
        for name in COMMAND_PROVIDER_PARENT_ENVIRONMENT_ALLOWLIST {
            if let Some(value) = std::env::var_os(name) {
                process.env(name, value);
            } else if *name == "PATH" {
                return Err(Error::ProposalCommand(
                    "PATH is required by the command-provider launch contract".to_owned(),
                ));
            }
        }
        let mut child = process
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
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let usage = parse_codex_jsonl(&stdout);
        Ok(Completion {
            command: Some(command.to_owned()),
            stdout,
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            exit_code: output.status.code(),
            success: output.status.success(),
            usage,
        })
    }
}

impl Provider for CommandProvider {
    fn complete(&self, prompt: &str, output_path: &Path) -> Result<Completion> {
        self.run_command(&self.command, prompt, output_path)
    }

    fn resume(&self, prompt: &str, output_path: &Path, session_id: &str) -> Result<Completion> {
        if !is_codex_session_id(session_id) {
            return Err(Error::ProposalCommand(format!(
                "refusing to resume malformed Codex session ID {session_id:?}"
            )));
        }
        let template = self.resume_command.as_ref().ok_or_else(|| {
            Error::ProposalCommand(
                "counterexample provider has no configured resume command".to_owned(),
            )
        })?;
        if !template.contains("{session_id}") {
            return Err(Error::ProposalCommand(
                "counterexample resume command must contain the {session_id} placeholder"
                    .to_owned(),
            ));
        }
        let command = template.replace("{session_id}", session_id);
        self.run_command(&command, prompt, output_path)
    }
}

fn is_codex_session_id(value: &str) -> bool {
    value.len() == 36
        && value.bytes().enumerate().all(|(index, byte)| {
            if matches!(index, 8 | 13 | 18 | 23) {
                byte == b'-'
            } else {
                byte.is_ascii_hexdigit()
            }
        })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::os::unix::fs::PermissionsExt;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;

    #[test]
    fn hostile_shell_startup_and_exported_functions_cannot_change_provider_command() {
        const CHILD_MODE: &str = "LOGOS_COMMAND_PROVIDER_ENVIRONMENT_TEST_CHILD";
        if let Some(root) = std::env::var_os(CHILD_MODE) {
            let root = PathBuf::from(root);
            let observed_environment = root.join("provider-environment.txt");
            let marker = root.join("hostile-shell-code-executed");
            let completion = CommandProvider::new("codex".to_owned())
                .complete("test prompt", &observed_environment)
                .expect("execute sanitized provider command");
            assert!(
                completion.success,
                "provider command failed: {}",
                completion.stderr
            );
            let usage = completion.usage.expect("parse fake provider usage");
            assert_eq!(usage.session_id, "provider-environment-test");
            assert_eq!(usage.usage.input_tokens, 1);
            assert_eq!(usage.usage.cached_input_tokens, 0);
            assert_eq!(usage.usage.output_tokens, 1);
            assert!(!marker.exists(), "hostile shell code executed");

            let environment = std::fs::read_to_string(&observed_environment)
                .expect("read provider child environment");
            let environment = environment
                .lines()
                .filter_map(|line| line.split_once('='))
                .map(|(name, value)| (name.to_owned(), value.to_owned()))
                .collect::<BTreeMap<_, _>>();
            for (name, value) in COMMAND_PROVIDER_FIXED_ENVIRONMENT {
                assert_eq!(environment.get(*name).map(String::as_str), Some(*value));
            }
            assert_eq!(
                environment.get("PATH").map(String::as_str),
                Some(root.join("bin").to_string_lossy().as_ref())
            );
            for (name, value) in [
                ("CODEX_HOME", "/trusted/codex-home"),
                ("LOGOS_SOLVER_CODEX_HOME", "/trusted/codex-home"),
                (
                    "LOGOS_SOLVER_CODEX_CONFIG",
                    "/trusted/codex-home/config.toml",
                ),
            ] {
                assert_eq!(environment.get(name).map(String::as_str), Some(value));
            }
            assert_eq!(
                environment.get("LOGOS_PROPOSAL_JSON").map(String::as_str),
                Some(observed_environment.to_string_lossy().as_ref())
            );
            for name in [
                CHILD_MODE,
                "BASH_ENV",
                "ENV",
                "SHELLOPTS",
                "BASHOPTS",
                "LD_PRELOAD",
                "LD_LIBRARY_PATH",
                "OCAMLPATH",
                "CAML_LD_LIBRARY_PATH",
                "CDPATH",
                "JAVA_TOOL_OPTIONS",
                "_JAVA_OPTIONS",
                "JDK_JAVA_OPTIONS",
                "CLASSPATH",
                "OPENAI_API_KEY",
                "CODEX_API_KEY",
                "OPENAI_BASE_URL",
                "HTTP_PROXY",
                "HTTPS_PROXY",
                "ALL_PROXY",
                "NO_PROXY",
            ] {
                assert!(!environment.contains_key(name), "{name} reached provider");
            }
            assert!(
                environment
                    .keys()
                    .all(|name| !name.starts_with("BASH_FUNC_")),
                "an exported Bash function reached provider"
            );
            return;
        }

        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after Unix epoch")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "logos-command-provider-environment-{}-{nonce}",
            std::process::id()
        ));
        let bin = root.join("bin");
        std::fs::create_dir_all(&bin).expect("create provider environment fixture");
        let fake_codex = bin.join("codex");
        std::fs::write(
            &fake_codex,
            concat!(
                "#!/usr/bin/bash\n",
                "set -euo pipefail\n",
                "/usr/bin/cat >/dev/null\n",
                "/usr/bin/env >\"$LOGOS_PROPOSAL_JSON\"\n",
                "/usr/bin/printf '%s\\n' \\\n",
                "  '{\"type\":\"thread.started\",\"thread_id\":\"provider-environment-test\"}' \\\n",
                "  '{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":1,\"cached_input_tokens\":0,\"output_tokens\":1}}'\n",
            ),
        )
        .expect("write fake Codex provider");
        let mut permissions = std::fs::metadata(&fake_codex)
            .expect("stat fake Codex provider")
            .permissions();
        permissions.set_mode(0o700);
        std::fs::set_permissions(&fake_codex, permissions)
            .expect("make fake Codex provider executable");

        let marker = root.join("hostile-shell-code-executed");
        let bash_env = root.join("ambient-bash-env.sh");
        std::fs::write(
            &bash_env,
            format!("/usr/bin/printf bash-env >>'{}'\n", marker.display()),
        )
        .expect("write BASH_ENV sentinel");

        let current_thread = std::thread::current();
        let test_name = current_thread.name().expect("test thread has a name");
        let output = Command::new(std::env::current_exe().expect("current test executable"))
            .arg("--exact")
            .arg(test_name)
            .arg("--nocapture")
            .env(CHILD_MODE, &root)
            .env("PATH", &bin)
            .env("HOME", "/ambient/home")
            .env("TMPDIR", "/ambient/tmp")
            .env("CODEX_HOME", "/trusted/codex-home")
            .env("LOGOS_SOLVER_CODEX_HOME", "/trusted/codex-home")
            .env(
                "LOGOS_SOLVER_CODEX_CONFIG",
                "/trusted/codex-home/config.toml",
            )
            .env("BASH_ENV", &bash_env)
            .env("ENV", &bash_env)
            .env(
                "BASH_FUNC_codex%%",
                format!(
                    "() {{ /usr/bin/printf function >>'{}'; /usr/bin/false; }}",
                    marker.display()
                ),
            )
            .env("SHELLOPTS", "braceexpand:hashall:interactive-comments")
            .env("BASHOPTS", "checkwinsize:cmdhist:complete_fullquote")
            .env("LD_PRELOAD", "")
            .env("LD_LIBRARY_PATH", "/ambient/ld-library-path")
            .env("OCAMLPATH", "/ambient/ocamlpath")
            .env("CAML_LD_LIBRARY_PATH", "/ambient/caml-ld-library-path")
            .env("CDPATH", "/ambient/cdpath")
            .env("JAVA_TOOL_OPTIONS", "-Dambient.java.tool.options=true")
            .env("_JAVA_OPTIONS", "-Dambient.java.options=true")
            .env("JDK_JAVA_OPTIONS", "-Dambient.jdk.options=true")
            .env("CLASSPATH", "/ambient/classpath")
            .env("OPENAI_API_KEY", "ambient-openai-key")
            .env("CODEX_API_KEY", "ambient-codex-key")
            .env("OPENAI_BASE_URL", "https://ambient.invalid")
            .env("HTTP_PROXY", "http://ambient.invalid")
            .env("HTTPS_PROXY", "http://ambient.invalid")
            .env("ALL_PROXY", "socks5://ambient.invalid")
            .env("NO_PROXY", "ambient.invalid")
            .output()
            .expect("re-execute provider environment regression");
        assert!(
            output.status.success(),
            "provider environment child failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(!marker.exists(), "hostile shell code executed");
        std::fs::remove_dir_all(root).expect("remove provider environment fixture");
    }
}
