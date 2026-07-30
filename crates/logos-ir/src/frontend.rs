use std::path::Path;
use std::process::Command;

use crate::calcite::CalciteFile;
use crate::convert_raw_file;
use crate::error::{Error, Result};
use crate::ir::{LogosIrFile, SqlEnvironment};

const SQL_FRONTEND_SHELL: &str = "/usr/bin/bash";
const SQL_FRONTEND_SHELL_ARGS: &[&str] = &["--noprofile", "--norc", "-c"];
const SQL_FRONTEND_FIXED_ENVIRONMENT: &[(&str, &str)] = &[
    ("PATH", "/usr/bin:/bin"),
    ("HOME", "/nonexistent"),
    ("TMPDIR", "/tmp"),
    ("LC_ALL", "C"),
    ("LANG", "C"),
    ("TZ", "UTC"),
];
const SQL_FRONTEND_PARENT_ENVIRONMENT_ALLOWLIST: &[&str] = &[
    "JAVA_HOME",
    "MAVEN_VERSION",
    "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
];

pub trait SqlIrFrontend {
    fn load_sql(&self, schema_path: &Path, query_path: &Path) -> Result<LogosIrFile>;
}

#[derive(Debug, Clone)]
pub struct ShellSqlIrFrontend {
    command: String,
    environment: SqlEnvironment,
}

impl ShellSqlIrFrontend {
    pub fn new(command: String) -> Self {
        Self {
            command,
            environment: SqlEnvironment::default(),
        }
    }

    pub fn with_environment(mut self, environment: SqlEnvironment) -> Self {
        self.environment = environment;
        self
    }
}

impl SqlIrFrontend for ShellSqlIrFrontend {
    fn load_sql(&self, schema_path: &Path, query_path: &Path) -> Result<LogosIrFile> {
        let command = format!(
            "{} --schema {} --sql {} --default-collation {} --character-classification {} --locale-provider {} --server-encoding {}",
            self.command,
            shell_quote(schema_path),
            shell_quote(query_path),
            self.environment.default_collation_label(),
            self.environment.character_classification_label(),
            self.environment.locale_provider_label(),
            self.environment.server_encoding_label(),
        );
        let mut process = Command::new(SQL_FRONTEND_SHELL);
        process
            .args(SQL_FRONTEND_SHELL_ARGS)
            .arg(command)
            .env_clear();
        for (name, value) in SQL_FRONTEND_FIXED_ENVIRONMENT {
            process.env(name, value);
        }
        for name in SQL_FRONTEND_PARENT_ENVIRONMENT_ALLOWLIST {
            if let Some(value) = std::env::var_os(name) {
                process.env(name, value);
            }
        }
        let output = process
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
    use std::collections::BTreeMap;
    use std::os::unix::fs::PermissionsExt;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;

    #[test]
    fn quotes_shell_paths() {
        assert_eq!(shell_quote(Path::new("a'b.sql")), "'a'\\''b.sql'");
    }

    #[test]
    fn canonical_calcite_launcher_uses_fixed_shell_and_direct_path_tools() {
        let script = include_str!("../../../scripts/calcite-ir");
        assert!(script.starts_with("#!/usr/bin/bash\n"));
        assert!(script.contains("$(/usr/bin/dirname \"${BASH_SOURCE[0]}\")"));
        assert!(script.contains("$(/usr/bin/readlink -f \"$JAVA_HOME/bin/java\")"));
        assert!(script.contains(
            "exec \"$JAVA_BIN\" -XX:+PerfDisableSharedMem -cp \"$CLASSES_DIR:$RUNTIME_CLASSPATH\""
        ));
        assert!(!script.contains("#!/usr/bin/env bash"));
        assert!(!script.contains("$(dirname "));
        assert!(!script.contains("$(readlink "));
    }

    #[test]
    fn direct_calcite_launcher_disables_shared_perf_data_before_classpath() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after Unix epoch")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "logos-calcite-direct-java-{}-{nonce}",
            std::process::id()
        ));
        let script = root.join("scripts/calcite-ir");
        let classes = root.join("frontend/calcite-wrapper/target/classes");
        let classpath = root.join("runtime-classpath.txt");
        let java_home = root.join("jdk");
        let java = java_home.join("bin/java");
        std::fs::create_dir_all(script.parent().expect("script parent"))
            .expect("create script directory");
        std::fs::create_dir_all(&classes).expect("create classes directory");
        std::fs::create_dir_all(java.parent().expect("java parent"))
            .expect("create fake Java directory");
        std::fs::write(&script, include_str!("../../../scripts/calcite-ir"))
            .expect("write launcher copy");
        std::fs::write(&classpath, "/bound/dependency.jar\n").expect("write bound classpath");
        std::fs::write(&java, "#!/usr/bin/bash\nprintf '%s\\n' \"$@\"\n")
            .expect("write fake Java executable");
        for path in [&script, &java] {
            let mut permissions = std::fs::metadata(path)
                .expect("stat executable fixture")
                .permissions();
            permissions.set_mode(0o700);
            std::fs::set_permissions(path, permissions).expect("make fixture executable");
        }

        let output = Command::new(&script)
            .args(["--schema", "/schema.sql", "--sql", "/query.sql"])
            .env_clear()
            .env("JAVA_HOME", &java_home)
            .env("LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE", &classpath)
            .output()
            .expect("run direct Calcite launcher fixture");
        assert!(
            output.status.success(),
            "launcher fixture failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let arguments = String::from_utf8(output.stdout)
            .expect("fake Java arguments are UTF-8")
            .lines()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        assert_eq!(arguments[0], "-XX:+PerfDisableSharedMem");
        assert_eq!(arguments[1], "-cp");
        assert_eq!(
            arguments[2],
            format!("{}:/bound/dependency.jar", classes.display())
        );
        assert_eq!(arguments[3], "dev.logos.calcite.CalciteIrCli");
        assert_eq!(
            &arguments[4..],
            ["--schema", "/schema.sql", "--sql", "/query.sql"]
        );

        std::fs::remove_dir_all(root).expect("remove direct launcher fixture");
    }

    #[test]
    fn hostile_shell_startup_and_exported_functions_cannot_change_frontend_output() {
        const CHILD_MODE: &str = "LOGOS_SQL_FRONTEND_ENVIRONMENT_TEST_CHILD";
        if let Some(root) = std::env::var_os(CHILD_MODE) {
            let root = PathBuf::from(root);
            let observed_environment = root.join("frontend-environment.txt");
            let marker = root.join("hostile-shell-code-executed");
            let command = format!(
                concat!(
                    "readlink -f / >/dev/null; ",
                    "/usr/bin/env > {}; ",
                    "/usr/bin/printf '{{}}'; ",
                    "/usr/bin/true"
                ),
                shell_quote(&observed_environment),
            );
            let ir = ShellSqlIrFrontend::new(command)
                .load_sql(
                    Path::new("/unused/schema.sql"),
                    Path::new("/unused/query.sql"),
                )
                .expect("sanitized frontend returns invariant valid IR");
            assert!(ir.schema.tables.is_empty());
            assert!(ir.queries.is_empty());
            assert!(!marker.exists(), "hostile shell code executed");

            let environment = std::fs::read_to_string(&observed_environment)
                .expect("read frontend child environment");
            let environment = environment
                .lines()
                .filter_map(|line| line.split_once('='))
                .map(|(name, value)| (name.to_owned(), value.to_owned()))
                .collect::<BTreeMap<_, _>>();
            for (name, value) in SQL_FRONTEND_FIXED_ENVIRONMENT {
                assert_eq!(environment.get(*name).map(String::as_str), Some(*value));
            }
            for (name, value) in [
                ("JAVA_HOME", "/trusted/jdk"),
                ("MAVEN_VERSION", "3.9.11"),
                (
                    "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
                    "/trusted/calcite-classpath.txt",
                ),
            ] {
                assert_eq!(environment.get(name).map(String::as_str), Some(value));
            }
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
                "HTTPS_PROXY",
            ] {
                assert!(!environment.contains_key(name), "{name} reached frontend");
            }
            assert!(
                environment
                    .keys()
                    .all(|name| !name.starts_with("BASH_FUNC_")),
                "an exported Bash function reached frontend"
            );
            return;
        }

        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after Unix epoch")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "logos-sql-frontend-environment-{}-{nonce}",
            std::process::id()
        ));
        std::fs::create_dir_all(&root).expect("create frontend environment fixture");
        let marker = root.join("hostile-shell-code-executed");
        let bash_env = root.join("ambient-bash-env.sh");
        std::fs::write(
            &bash_env,
            format!("/usr/bin/printf bash-env >>'{}'\n", marker.display()),
        )
        .expect("write BASH_ENV sentinel");
        let mut permissions = std::fs::metadata(&bash_env)
            .expect("stat BASH_ENV sentinel")
            .permissions();
        permissions.set_mode(0o700);
        std::fs::set_permissions(&bash_env, permissions).expect("make BASH_ENV executable");

        let current_thread = std::thread::current();
        let test_name = current_thread.name().expect("test thread has a name");
        let output = Command::new(std::env::current_exe().expect("current test executable"))
            .arg("--exact")
            .arg(test_name)
            .arg("--nocapture")
            .env(CHILD_MODE, &root)
            .env("PATH", "/ambient/untrusted-path")
            .env("HOME", "/ambient/home")
            .env("TMPDIR", "/ambient/tmp")
            .env("JAVA_HOME", "/trusted/jdk")
            .env("MAVEN_VERSION", "3.9.11")
            .env(
                "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
                "/trusted/calcite-classpath.txt",
            )
            .env("BASH_ENV", &bash_env)
            .env("ENV", &bash_env)
            .env(
                "BASH_FUNC_readlink%%",
                format!(
                    "() {{ /usr/bin/printf function >>'{}'; /usr/bin/readlink \"$@\"; }}",
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
            .env("OPENAI_API_KEY", "ambient-api-key")
            .env("HTTPS_PROXY", "http://ambient.invalid")
            .output()
            .expect("re-execute frontend environment regression");
        assert!(
            output.status.success(),
            "frontend environment child failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(!marker.exists(), "hostile shell code executed");
        std::fs::remove_dir_all(root).expect("remove frontend environment fixture");
    }
}
