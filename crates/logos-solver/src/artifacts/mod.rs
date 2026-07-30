use std::{
    ffi::OsString,
    fs::{File, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use serde::Serialize;

use crate::error::{Error, Result};
use crate::runtime;

static ARTIFACT_TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);
const ARTIFACT_TEMP_CREATE_ATTEMPTS: usize = 1024;

#[derive(Debug, Clone)]
pub struct ArtifactWriter {
    root: PathBuf,
}

impl ArtifactWriter {
    pub fn new(path: Option<PathBuf>) -> Result<Self> {
        let root = path.unwrap_or_else(default_log_dir);
        std::fs::create_dir_all(&root).map_err(|source| Error::CreateDir {
            path: root.clone(),
            source,
        })?;
        Ok(Self { root })
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn write_text(&self, relative: impl AsRef<Path>, text: &str) -> Result<()> {
        self.write_text_before_rename(relative, text, |_| Ok(()))
    }

    fn write_text_before_rename<F>(
        &self,
        relative: impl AsRef<Path>,
        text: &str,
        before_rename: F,
    ) -> Result<()>
    where
        F: FnOnce(&Path) -> io::Result<()>,
    {
        let path = self.root.join(relative);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
                path: parent.to_owned(),
                source,
            })?;
        }
        atomic_replace(&path, text.as_bytes(), before_rename)
            .map_err(|source| Error::Write { path, source })
    }

    pub fn write_json<T: Serialize>(&self, relative: impl AsRef<Path>, value: &T) -> Result<()> {
        let text = serde_json::to_string_pretty(value)?;
        self.write_text(relative, &(text + "\n"))
    }
}

fn default_log_dir() -> PathBuf {
    runtime::default_run_dir()
}

fn atomic_replace<F>(path: &Path, bytes: &[u8], before_rename: F) -> io::Result<()>
where
    F: FnOnce(&Path) -> io::Result<()>,
{
    let parent = path.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "artifact destination has no parent directory",
        )
    })?;
    let (mut temporary, temporary_path) = create_temporary_file(path)?;

    let staged = (|| {
        temporary.write_all(bytes)?;
        temporary.sync_all()?;
        before_rename(&temporary_path)
    })();
    drop(temporary);
    if let Err(source) = staged {
        return Err(cleanup_temporary_after_failure(&temporary_path, source));
    }

    if let Err(source) = std::fs::rename(&temporary_path, path) {
        return Err(cleanup_temporary_after_failure(&temporary_path, source));
    }

    File::open(parent)?.sync_all()
}

fn create_temporary_file(destination: &Path) -> io::Result<(File, PathBuf)> {
    let parent = destination.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "artifact destination has no parent directory",
        )
    })?;
    let file_name = destination
        .file_name()
        .filter(|name| !name.is_empty())
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "artifact destination has no file name",
            )
        })?;

    for _ in 0..ARTIFACT_TEMP_CREATE_ATTEMPTS {
        let sequence = ARTIFACT_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let mut temporary_name = OsString::from(".");
        temporary_name.push(file_name);
        temporary_name.push(format!(".{}.{}.tmp", std::process::id(), sequence));
        let temporary_path = parent.join(temporary_name);
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary_path)
        {
            Ok(file) => return Ok((file, temporary_path)),
            Err(source) if source.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(source) => return Err(source),
        }
    }

    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        "could not allocate a unique artifact temporary file",
    ))
}

fn cleanup_temporary_after_failure(path: &Path, source: io::Error) -> io::Error {
    match std::fs::remove_file(path) {
        Ok(()) => source,
        Err(cleanup) if cleanup.kind() == io::ErrorKind::NotFound => source,
        Err(cleanup) => io::Error::new(
            cleanup.kind(),
            format!(
                "{source}; additionally failed to remove temporary artifact {}: {cleanup}",
                path.display()
            ),
        ),
    }
}

#[cfg(test)]
mod tests {
    use std::{
        sync::{
            Arc,
            atomic::{AtomicBool, Ordering},
        },
        thread,
    };

    use serde_json::{Value, json};

    use super::*;

    fn temporary_artifacts(root: &Path) -> Vec<PathBuf> {
        std::fs::read_dir(root)
            .expect("read artifact root")
            .map(|entry| entry.expect("read artifact entry").path())
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with('.') && name.ends_with(".tmp"))
            })
            .collect()
    }

    #[test]
    fn pre_rename_failure_preserves_destination_and_removes_temporary() {
        let root = tempfile::tempdir().expect("create artifact root");
        let writer = ArtifactWriter::new(Some(root.path().to_owned())).expect("create writer");
        writer
            .write_text("report.json", "old terminal report\n")
            .expect("write old report");

        let mut staged_path = None;
        let error = writer
            .write_text_before_rename("report.json", "new terminal report\n", |path| {
                staged_path = Some(path.to_owned());
                assert_eq!(path.parent(), Some(root.path()));
                assert_eq!(
                    std::fs::read(path).expect("read staged report"),
                    b"new terminal report\n"
                );
                Err(io::Error::other("injected pre-rename failure"))
            })
            .expect_err("injected failure must be returned");

        assert!(error.to_string().contains("injected pre-rename failure"));
        assert_eq!(
            std::fs::read(root.path().join("report.json")).expect("read preserved report"),
            b"old terminal report\n"
        );
        assert!(!staged_path.expect("observe staged path").exists());
        assert!(temporary_artifacts(root.path()).is_empty());
    }

    #[test]
    fn repeated_json_replacement_is_always_one_complete_version() {
        let root = tempfile::tempdir().expect("create artifact root");
        let writer = ArtifactWriter::new(Some(root.path().to_owned())).expect("create writer");
        let old = json!({"generation": 1, "payload": "a".repeat(32 * 1024)});
        let new = json!({"generation": 2, "payload": "b".repeat(32 * 1024)});
        writer
            .write_json("report.json", &old)
            .expect("write initial JSON report");

        let destination = Arc::new(root.path().join("report.json"));
        let stop = Arc::new(AtomicBool::new(false));
        let reader_destination = Arc::clone(&destination);
        let reader_stop = Arc::clone(&stop);
        let old_for_reader = old.clone();
        let new_for_reader = new.clone();
        let reader = thread::spawn(move || -> std::result::Result<(), String> {
            while !reader_stop.load(Ordering::Acquire) {
                let bytes = std::fs::read(&*reader_destination)
                    .map_err(|error| format!("read replaced report: {error}"))?;
                let observed: Value = serde_json::from_slice(&bytes)
                    .map_err(|error| format!("parse replaced report: {error}"))?;
                if observed != old_for_reader && observed != new_for_reader {
                    return Err("observed a JSON report other than the old or new value".to_owned());
                }
            }
            Ok(())
        });

        let replacement_result: Result<()> = (|| {
            for index in 0..32 {
                writer.write_json("report.json", if index % 2 == 0 { &new } else { &old })?;
            }
            Ok(())
        })();
        stop.store(true, Ordering::Release);
        let reader_result = reader.join().expect("JSON reader thread did not panic");

        replacement_result.expect("replace JSON report repeatedly");
        reader_result.expect("reader observed only complete JSON versions");
        let final_value: Value =
            serde_json::from_slice(&std::fs::read(&*destination).expect("read final JSON report"))
                .expect("parse final JSON report");
        assert!(final_value == old || final_value == new);
        assert!(temporary_artifacts(root.path()).is_empty());
    }

    #[cfg(unix)]
    #[test]
    fn replacement_does_not_follow_an_existing_destination_symlink() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("create test root");
        let artifact_root = root.path().join("artifacts");
        let writer =
            ArtifactWriter::new(Some(artifact_root.clone())).expect("create artifact writer");
        let outside = root.path().join("outside-sentinel.json");
        std::fs::write(&outside, b"outside must remain unchanged\n")
            .expect("write outside sentinel");
        let destination = artifact_root.join("report.json");
        symlink(&outside, &destination).expect("create destination symlink");

        let report = json!({"status": "complete", "generation": 2});
        writer
            .write_json("report.json", &report)
            .expect("atomically replace destination symlink");

        assert_eq!(
            std::fs::read(&outside).expect("read outside sentinel"),
            b"outside must remain unchanged\n"
        );
        assert!(!destination.is_symlink());
        assert!(destination.is_file());
        assert_eq!(
            serde_json::from_slice::<Value>(
                &std::fs::read(&destination).expect("read replacement report")
            )
            .expect("parse replacement report"),
            report
        );
        assert!(temporary_artifacts(&artifact_root).is_empty());
    }
}
