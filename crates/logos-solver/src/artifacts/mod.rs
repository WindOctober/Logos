use std::path::{Path, PathBuf};

use serde::Serialize;

use crate::error::{Error, Result};
use crate::runtime;

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
        let path = self.root.join(relative);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
                path: parent.to_owned(),
                source,
            })?;
        }
        std::fs::write(&path, text).map_err(|source| Error::Write { path, source })
    }

    pub fn write_json<T: Serialize>(&self, relative: impl AsRef<Path>, value: &T) -> Result<()> {
        let text = serde_json::to_string_pretty(value)?;
        self.write_text(relative, &(text + "\n"))
    }
}

fn default_log_dir() -> PathBuf {
    runtime::default_run_dir()
}
