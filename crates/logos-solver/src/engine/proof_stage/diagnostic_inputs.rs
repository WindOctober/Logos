//! Generation-scoped, host-only source snapshots for diagnostic workspaces.
//!
//! Never hard-link the live workspace. Only private copies owned by this module
//! may be linked into diagnostic evidence; neither tree is agent-writable.

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::{Path, PathBuf};

use crate::engine::report::DiagnosticArtifactBinding;
use crate::error::{Error, Result};

use super::sha256_hex;

const COMMON_FILES: [&str; 5] = [
    "Schema.v",
    "Queries.v",
    "WitnessData.v",
    "Witness.v",
    "Goal.v",
];

pub(super) struct SharedInputs {
    root: PathBuf,
    files: Vec<PathBuf>,
    manifest: DiagnosticArtifactBinding,
}

fn regular_directory(path: &Path) -> io::Result<()> {
    if !fs::symlink_metadata(path)?.is_dir() {
        return Err(io::Error::other(format!(
            "not a regular directory: {}",
            path.display()
        )));
    }
    Ok(())
}

fn read_file(path: &Path, readonly: bool) -> io::Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_file() || (readonly && metadata.permissions().mode() & 0o222 != 0) {
        return Err(io::Error::other(format!(
            "unsafe diagnostic input: {}",
            path.display()
        )));
    }
    fs::read(path)
}

fn read_inputs(root: &Path, readonly: bool) -> io::Result<BTreeMap<PathBuf, Vec<u8>>> {
    regular_directory(root)?;
    let mut files = BTreeMap::new();
    for name in COMMON_FILES {
        files.insert(PathBuf::from(name), read_file(&root.join(name), readonly)?);
    }
    let modules = root.join("WitnessModules");
    regular_directory(&modules)?;
    for entry in fs::read_dir(&modules)? {
        let entry = entry?;
        let relative = Path::new("WitnessModules").join(entry.file_name());
        files.insert(relative, read_file(&entry.path(), readonly)?);
    }
    if !files.contains_key(Path::new("WitnessModules/ORDER")) {
        return Err(io::Error::other("missing witness module order"));
    }
    Ok(files)
}

fn write_readonly(path: &Path, bytes: &[u8]) -> io::Result<()> {
    fs::write(path, bytes)?;
    fs::set_permissions(path, fs::Permissions::from_mode(0o400))
}

impl SharedInputs {
    /// Called before launching the agent, once per broker/round. Reopening a
    /// generation validates persisted bytes against the trusted live inputs;
    /// the request hot path only links this already validated private snapshot.
    pub(super) fn prepare(
        artifacts_root: &Path,
        workdir: &Path,
        generation: usize,
    ) -> Result<Self> {
        Self::prepare_inner(artifacts_root, workdir, generation).map_err(|error| {
            Error::TrustedRocqEnvironment(format!(
                "shared diagnostic inputs for generation {generation}: {error}"
            ))
        })
    }

    fn prepare_inner(artifacts_root: &Path, workdir: &Path, generation: usize) -> io::Result<Self> {
        if generation == 0 {
            return Err(io::Error::other("workspace generation must be positive"));
        }
        let relative = PathBuf::from(format!(
            "proof-stage/proof-agent/diagnostic-inputs/{generation:04}"
        ));
        let root = artifacts_root.join(&relative);
        let parent = root.parent().unwrap();
        fs::DirBuilder::new()
            .recursive(true)
            .mode(0o700)
            .create(parent)?;
        regular_directory(parent)?;
        let files = read_inputs(workdir, false)?;
        let bindings: Vec<_> = files
            .iter()
            .map(|(path, bytes)| DiagnosticArtifactBinding {
                path: relative.join(path).to_string_lossy().into_owned(),
                sha256: sha256_hex(bytes),
                bytes: bytes.len(),
            })
            .collect();
        let manifest_bytes = serde_json::to_vec_pretty(&serde_json::json!({
            "schemaVersion": 1,
            "workspaceGeneration": generation,
            "files": bindings,
        }))?;
        match fs::symlink_metadata(&root) {
            Ok(metadata) => {
                if !metadata.is_dir() || metadata.permissions().mode() & 0o077 != 0 {
                    return Err(io::Error::other(
                        "shared input snapshot is not a private directory",
                    ));
                }
                // A generation is immutable, including its file set. Never
                // silently rebuild drifted evidence used by earlier requests.
                if read_inputs(&root, true)? != files
                    || read_file(&root.join("manifest.json"), true)? != manifest_bytes
                {
                    return Err(io::Error::other(format!(
                        "workspace generation {generation} input snapshot drifted"
                    )));
                }
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let stage = tempfile::Builder::new()
                    .prefix(".pending-")
                    .tempdir_in(parent)?;
                fs::set_permissions(stage.path(), fs::Permissions::from_mode(0o700))?;
                fs::DirBuilder::new()
                    .mode(0o700)
                    .create(stage.path().join("WitnessModules"))?;
                for (path, bytes) in &files {
                    write_readonly(&stage.path().join(path), bytes)?;
                }
                write_readonly(&stage.path().join("manifest.json"), &manifest_bytes)?;
                // The broker is serialized. Publish only complete generations;
                // RAII removes incomplete staging directories on any error.
                fs::rename(stage.path(), &root)?;
            }
            Err(error) => return Err(error),
        }
        Ok(Self {
            root,
            files: files.into_keys().collect(),
            manifest: DiagnosticArtifactBinding {
                path: relative
                    .join("manifest.json")
                    .to_string_lossy()
                    .into_owned(),
                sha256: sha256_hex(&manifest_bytes),
                bytes: manifest_bytes.len(),
            },
        })
    }

    pub(super) fn link_into(&self, destination: &Path) -> Result<()> {
        let link = || -> io::Result<()> {
            fs::create_dir(destination.join("WitnessModules"))?;
            for path in &self.files {
                fs::hard_link(self.root.join(path), destination.join(path))?;
            }
            // Explicit artifact-relative binding for replay, even when an
            // archive/export does not preserve hard-link identity.
            fs::write(
                destination.join("shared-inputs.json"),
                serde_json::to_vec_pretty(&self.manifest)?,
            )
        };
        link().map_err(|error| {
            Error::TrustedRocqEnvironment(format!("linking shared diagnostic inputs: {error}"))
        })
    }
}

#[cfg(test)]
#[path = "../../../tests/diagnostic_inputs/mod.rs"]
mod tests;
