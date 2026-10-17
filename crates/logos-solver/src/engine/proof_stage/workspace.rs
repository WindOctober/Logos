//! Scratch transactions, immutable module publication, and digest-bound compiler caches.

use crate::artifacts::ArtifactWriter;
use crate::engine::now_ms_since_epoch;
use crate::engine::report::TrustedDiagnosticCacheEvidence;
use crate::error::{Error, Result};
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CString, OsStr};
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

use super::diagnostics::CandidateKind;
use super::{
    CHECKED_SCRATCH_DIRECTORY, PROOF_MODULE_DIRECTORY, SCRATCH_ALLOWED_EXTENSIONS,
    WITNESS_MODULE_DIRECTORY, sha256_hex,
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct ScratchUsage {
    pub(super) file_count: usize,
    pub(super) total_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ScratchFile {
    pub(super) relative_path: PathBuf,
    pub(super) bytes: Vec<u8>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct ScratchTree {
    pub(super) files: Vec<ScratchFile>,
    /// Relative directory paths, with the empty path representing the root.
    pub(super) directories: BTreeSet<PathBuf>,
    /// Structurally safe regular files that are not eligible for persistence.
    pub(super) dropped_unsupported_files: Vec<PathBuf>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum UnsupportedScratchFilePolicy {
    Reject,
    Drop,
}

fn validate_scratch_relative_path(path: &Path) -> std::result::Result<(), String> {
    if path.is_absolute() || path.as_os_str().is_empty() {
        return Err("scratch path must be a nonempty relative path".to_owned());
    }
    let components = path.components().collect::<Vec<_>>();
    if components
        .iter()
        .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err("scratch path must contain only normalized components".to_owned());
    }
    let text = path
        .to_str()
        .ok_or_else(|| "scratch path must be UTF-8".to_owned())?;
    if text.contains('\\') || text.chars().any(char::is_control) {
        return Err("scratch path contains unsupported characters".to_owned());
    }
    Ok(())
}

fn validate_scratch_child_path(path: &Path) -> std::result::Result<(), String> {
    validate_scratch_relative_path(path)?;
    let extension = path
        .extension()
        .and_then(|extension| extension.to_str())
        .ok_or_else(|| "scratch file must have an allowed extension".to_owned())?;
    if !SCRATCH_ALLOWED_EXTENSIONS.contains(&extension) {
        return Err(format!(
            "scratch files must use one of the extensions {:?}",
            SCRATCH_ALLOWED_EXTENSIONS
        ));
    }
    Ok(())
}

fn open_directory_nofollow(path: &Path) -> Result<File> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
        .map_err(|source| Error::Read {
            path: path.to_owned(),
            source,
        })?;
    let metadata = file.metadata().map_err(|source| Error::Read {
        path: path.to_owned(),
        source,
    })?;
    if !metadata.file_type().is_dir() {
        return Err(Error::ProofAgentCommand(format!(
            "{} must be a regular non-symlink directory",
            path.display()
        )));
    }
    Ok(file)
}

fn openat_nofollow(
    parent: &File,
    component: &OsStr,
    display_path: &Path,
    directory: bool,
) -> Result<File> {
    let component = CString::new(component.as_bytes()).map_err(|_| {
        Error::ProofAgentCommand(format!(
            "path component in {} contains a NUL byte",
            display_path.display()
        ))
    })?;
    let type_flags = if directory {
        libc::O_DIRECTORY
    } else {
        // Opening a FIFO nonblocking prevents an attacker-controlled entry from
        // stalling the broker before fstat rejects it as non-regular.
        libc::O_NONBLOCK
    };
    // SAFETY: parent is a live owned directory descriptor, component is a
    // NUL-terminated single normalized component, and a successful descriptor
    // is transferred exactly once into File below.
    let descriptor = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            component.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | type_flags,
        )
    };
    if descriptor < 0 {
        return Err(Error::Read {
            path: display_path.to_owned(),
            source: std::io::Error::last_os_error(),
        });
    }
    // SAFETY: openat returned a fresh descriptor owned by this call, and no
    // other File is constructed from it.
    Ok(unsafe { File::from_raw_fd(descriptor) })
}

fn read_regular_file_beneath(root: &File, root_path: &Path, relative: &Path) -> Result<Vec<u8>> {
    if relative.is_absolute() || relative.as_os_str().is_empty() {
        return Err(Error::ProofAgentCommand(format!(
            "candidate path {} must be a nonempty relative path",
            relative.display()
        )));
    }
    let components = relative.components().collect::<Vec<_>>();
    if components
        .iter()
        .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(Error::ProofAgentCommand(format!(
            "candidate path {} is not normalized",
            relative.display()
        )));
    }
    let mut directory = root.try_clone().map_err(|source| Error::Read {
        path: root_path.to_owned(),
        source,
    })?;
    let mut display_path = root_path.to_owned();
    for component in &components[..components.len() - 1] {
        let std::path::Component::Normal(component) = component else {
            unreachable!("candidate components were validated above")
        };
        display_path.push(component);
        directory = openat_nofollow(&directory, component, &display_path, true)?;
    }
    let std::path::Component::Normal(file_name) = components[components.len() - 1] else {
        unreachable!("candidate components were validated above")
    };
    display_path.push(file_name);
    let mut file = openat_nofollow(&directory, file_name, &display_path, false)?;
    let metadata = file.metadata().map_err(|source| Error::Read {
        path: display_path.clone(),
        source,
    })?;
    if !metadata.file_type().is_file() {
        return Err(Error::ProofAgentCommand(format!(
            "{} is not a regular non-symlink file",
            display_path.display()
        )));
    }
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes).map_err(|source| Error::Read {
        path: display_path.clone(),
        source,
    })?;
    Ok(bytes)
}

pub(super) fn validate_diagnostic_candidate_path(
    mode: CandidateKind,
    candidate_path: &str,
) -> std::result::Result<PathBuf, String> {
    match mode {
        CandidateKind::Problem if candidate_path == "Problem.v" => {
            Ok(PathBuf::from(candidate_path))
        }
        CandidateKind::Problem => {
            Err("problem diagnostics require candidatePath Problem.v".to_owned())
        }
        CandidateKind::Module => validate_proof_module_candidate_path(candidate_path),
        CandidateKind::Scratch => {
            let path = Path::new(candidate_path);
            let mut components = path.components();
            if components.next()
                != Some(std::path::Component::Normal(std::ffi::OsStr::new(
                    "scratch",
                )))
            {
                return Err("scratch diagnostics require candidatePath scratch/*.v".to_owned());
            }
            let child = components.collect::<PathBuf>();
            validate_scratch_child_path(&child)?;
            if is_checked_scratch_snapshot(&child) {
                return Err(
                    "scratch diagnostics cannot target the reserved scratch/checked/ namespace"
                        .to_owned(),
                );
            }
            if child.extension().and_then(|extension| extension.to_str()) != Some("v") {
                return Err("scratch diagnostics require a .v candidate".to_owned());
            }
            let normalized = Path::new("scratch").join(&child);
            if normalized.to_str() != Some(candidate_path) {
                return Err("candidatePath must be normalized".to_owned());
            }
            Ok(normalized)
        }
    }
}

pub(super) fn valid_proof_module_stem(stem: &str) -> bool {
    let mut characters = stem.chars();
    matches!(characters.next(), Some(first) if first.is_ascii_uppercase())
        && characters.all(|character| character.is_ascii_alphanumeric() || character == '_')
}

pub(super) fn validate_proof_module_candidate_path(
    candidate_path: &str,
) -> std::result::Result<PathBuf, String> {
    let path = Path::new(candidate_path);
    let mut components = path.components();
    if components.next()
        != Some(std::path::Component::Normal(std::ffi::OsStr::new(
            PROOF_MODULE_DIRECTORY,
        )))
    {
        return Err(format!(
            "module diagnostics require candidatePath {PROOF_MODULE_DIRECTORY}/<UppercaseRocqIdentifier>.v"
        ));
    }
    let Some(std::path::Component::Normal(file_name)) = components.next() else {
        return Err("module candidate is missing its file name".to_owned());
    };
    if components.next().is_some() {
        return Err("proof modules must be direct children of ProofModules/".to_owned());
    }
    let file_name = file_name
        .to_str()
        .ok_or_else(|| "proof module file name must be UTF-8".to_owned())?;
    let stem = file_name
        .strip_suffix(".v")
        .ok_or_else(|| "proof module candidate must have a .v extension".to_owned())?;
    if !valid_proof_module_stem(stem) {
        return Err(
            "proof module file stem must be an uppercase Rocq identifier containing only ASCII letters, digits, and underscores"
                .to_owned(),
        );
    }
    let normalized = Path::new(PROOF_MODULE_DIRECTORY).join(file_name);
    if normalized.to_str() != Some(candidate_path) {
        return Err("candidatePath must be normalized".to_owned());
    }
    Ok(normalized)
}

pub(super) fn validated_scratch_tree_with_policy(
    root: &Path,
    unsupported_file_policy: UnsupportedScratchFilePolicy,
) -> Result<ScratchTree> {
    let metadata = match std::fs::symlink_metadata(root) {
        Ok(metadata) => metadata,
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => {
            return Ok(ScratchTree::default());
        }
        Err(source) => {
            return Err(Error::Read {
                path: root.to_owned(),
                source,
            });
        }
    };
    if !metadata.file_type().is_dir() || metadata.file_type().is_symlink() {
        return Err(Error::ProofAgentCommand(format!(
            "scratch root {} must be a regular non-symlink directory",
            root.display()
        )));
    }

    let root_descriptor = open_directory_nofollow(root)?;
    let mut pending_directories = vec![(root.to_owned(), PathBuf::new())];
    let mut directory_paths = BTreeSet::from([PathBuf::new()]);
    let mut snapshots = Vec::new();
    let mut dropped_unsupported_files = Vec::new();
    while let Some((directory, directory_relative)) = pending_directories.pop() {
        let entries = std::fs::read_dir(&directory).map_err(|source| Error::Read {
            path: directory.clone(),
            source,
        })?;
        for entry in entries {
            let entry = entry.map_err(|source| Error::Read {
                path: directory.clone(),
                source,
            })?;
            let path = entry.path();
            let relative = if directory_relative.as_os_str().is_empty() {
                PathBuf::from(entry.file_name())
            } else {
                directory_relative.join(entry.file_name())
            };
            let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
                path: path.clone(),
                source,
            })?;
            if metadata.file_type().is_symlink() {
                return Err(Error::ProofAgentCommand(format!(
                    "scratch tree contains a symlink: {}",
                    path.display()
                )));
            }
            if metadata.file_type().is_dir() {
                validate_scratch_relative_path(&relative).map_err(Error::ProofAgentCommand)?;
                directory_paths.insert(relative.clone());
                pending_directories.push((path, relative));
                continue;
            }
            if !metadata.file_type().is_file() {
                return Err(Error::ProofAgentCommand(format!(
                    "scratch tree contains a non-regular entry: {}",
                    path.display()
                )));
            }
            validate_scratch_relative_path(&relative).map_err(|reason| {
                Error::ProofAgentCommand(format!(
                    "scratch file {} has an invalid path: {reason}",
                    relative.display()
                ))
            })?;
            if let Err(reason) = validate_scratch_child_path(&relative) {
                match unsupported_file_policy {
                    UnsupportedScratchFilePolicy::Reject => {
                        return Err(Error::ProofAgentCommand(format!(
                            "scratch file {} is not persistable: {reason}",
                            relative.display()
                        )));
                    }
                    UnsupportedScratchFilePolicy::Drop => {
                        dropped_unsupported_files.push(relative);
                        continue;
                    }
                }
            }
            let bytes = read_regular_file_beneath(&root_descriptor, root, &relative)?;
            std::str::from_utf8(&bytes).map_err(|source| {
                Error::ProofAgentCommand(format!(
                    "scratch file {} is not UTF-8: {source}",
                    path.display()
                ))
            })?;
            snapshots.push(ScratchFile {
                relative_path: relative,
                bytes,
            });
        }
    }
    snapshots.sort_by(|left, right| left.relative_path.cmp(&right.relative_path));
    dropped_unsupported_files.sort();
    Ok(ScratchTree {
        files: snapshots,
        directories: directory_paths,
        dropped_unsupported_files,
    })
}

pub(super) fn validated_scratch_tree(root: &Path) -> Result<ScratchTree> {
    validated_scratch_tree_with_policy(root, UnsupportedScratchFilePolicy::Reject)
}

fn validated_scratch_files(root: &Path) -> Result<Vec<ScratchFile>> {
    Ok(validated_scratch_tree(root)?.files)
}

fn validated_staged_scratch_files(root: &Path) -> Result<Vec<ScratchFile>> {
    let tree = validated_scratch_tree_with_policy(root, UnsupportedScratchFilePolicy::Drop)?;
    for relative in &tree.dropped_unsupported_files {
        eprintln!(
            "warning: dropping scratch/{} at the proof-agent round boundary because its extension is not persistable; only {:?} are retained between rounds",
            relative.display(),
            SCRATCH_ALLOWED_EXTENSIONS
        );
    }
    Ok(tree.files)
}

pub(super) fn scratch_workspace_state(root: &Path) -> Result<ScratchUsage> {
    let files = validated_scratch_tree(root)?.files;
    Ok(ScratchUsage {
        file_count: files.len(),
        total_bytes: files.iter().map(|file| file.bytes.len()).sum(),
    })
}

fn ensure_scratch_directory(path: &Path) -> Result<()> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_dir() && !metadata.file_type().is_symlink() => {}
        Ok(_) => {
            return Err(Error::ProofAgentCommand(format!(
                "scratch directory component {} is not a regular directory",
                path.display()
            )));
        }
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => {
            std::fs::create_dir(path).map_err(|source| Error::CreateDir {
                path: path.to_owned(),
                source,
            })?;
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).map_err(
                |source| {
                    Error::ProofAgentCommand(format!(
                        "failed to secure scratch directory {}: {source}",
                        path.display()
                    ))
                },
            )?;
        }
        Err(source) => {
            return Err(Error::Read {
                path: path.to_owned(),
                source,
            });
        }
    }
    Ok(())
}

fn validate_projected_scratch_directories<'a>(
    existing: &BTreeSet<PathBuf>,
    file_paths: impl IntoIterator<Item = &'a Path>,
) -> Result<()> {
    projected_scratch_directories(existing, file_paths).map(|_| ())
}

fn projected_scratch_directories<'a>(
    existing: &BTreeSet<PathBuf>,
    file_paths: impl IntoIterator<Item = &'a Path>,
) -> Result<BTreeSet<PathBuf>> {
    let mut projected = existing.clone();
    // All merge and promotion paths materialize the scratch root, including an
    // otherwise empty workspace, so count it before any filesystem mutation.
    projected.insert(PathBuf::new());
    for file_path in file_paths {
        validate_scratch_child_path(file_path).map_err(Error::ProofAgentCommand)?;
        let mut relative_parent = PathBuf::new();
        if let Some(parent) = file_path.parent() {
            for component in parent.components() {
                let std::path::Component::Normal(component) = component else {
                    return Err(Error::ProofAgentCommand(
                        "scratch snapshot parent is not normalized".to_owned(),
                    ));
                };
                relative_parent.push(component);
                projected.insert(relative_parent.clone());
            }
        }
    }
    Ok(projected)
}

fn write_scratch_snapshot(root: &Path, snapshot: &ScratchFile) -> Result<()> {
    validate_scratch_child_path(&snapshot.relative_path).map_err(Error::ProofAgentCommand)?;
    ensure_scratch_directory(root)?;
    let mut parent = root.to_owned();
    if let Some(relative_parent) = snapshot.relative_path.parent() {
        for component in relative_parent.components() {
            let std::path::Component::Normal(component) = component else {
                return Err(Error::ProofAgentCommand(
                    "scratch snapshot parent is not normalized".to_owned(),
                ));
            };
            parent.push(component);
            ensure_scratch_directory(&parent)?;
        }
    }
    let destination = root.join(&snapshot.relative_path);
    if let Ok(metadata) = std::fs::symlink_metadata(&destination)
        && (!metadata.file_type().is_file() || metadata.file_type().is_symlink())
    {
        return Err(Error::ProofAgentCommand(format!(
            "scratch destination {} is not a regular non-symlink file",
            destination.display()
        )));
    }
    let temporary = parent.join(format!(
        ".scratch-write-{}-{}",
        std::process::id(),
        now_ms_since_epoch()
    ));
    let result = (|| {
        std::fs::write(&temporary, &snapshot.bytes).map_err(|source| Error::Write {
            path: temporary.clone(),
            source,
        })?;
        std::fs::set_permissions(&temporary, std::fs::Permissions::from_mode(0o600)).map_err(
            |source| Error::Write {
                path: temporary.clone(),
                source,
            },
        )?;
        std::fs::rename(&temporary, &destination).map_err(|source| Error::Write {
            path: destination.clone(),
            source,
        })?;
        Ok(())
    })();
    if result.is_err() {
        let _ = std::fs::remove_file(&temporary);
    }
    result
}

fn merge_scratch_snapshots(root: &Path, additions: Vec<ScratchFile>) -> Result<ScratchUsage> {
    let existing_tree = validated_scratch_tree(root)?;
    let existing = existing_tree
        .files
        .into_iter()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    let mut merged = existing
        .values()
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    for snapshot in additions {
        validate_scratch_child_path(&snapshot.relative_path).map_err(Error::ProofAgentCommand)?;
        std::str::from_utf8(&snapshot.bytes).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "scratch file {} is not UTF-8: {source}",
                snapshot.relative_path.display()
            ))
        })?;
        merged.insert(snapshot.relative_path.clone(), snapshot);
    }
    validate_projected_scratch_directories(
        &existing_tree.directories,
        merged.keys().map(PathBuf::as_path),
    )?;
    let changed = merged.values().filter(|snapshot| {
        existing
            .get(&snapshot.relative_path)
            .is_none_or(|prior| prior.bytes != snapshot.bytes)
    });
    ensure_scratch_directory(root)?;
    for snapshot in changed {
        write_scratch_snapshot(root, snapshot)?;
    }
    scratch_workspace_state(root)
}

fn scratch_snapshot_state(snapshots: &BTreeMap<PathBuf, ScratchFile>) -> Result<ScratchUsage> {
    let total_bytes = snapshots
        .values()
        .try_fold(0usize, |total, snapshot| {
            total.checked_add(snapshot.bytes.len())
        })
        .ok_or_else(|| Error::ProofAgentCommand("scratch byte total overflowed".to_owned()))?;
    Ok(ScratchUsage {
        file_count: snapshots.len(),
        total_bytes,
    })
}

fn scratch_snapshot_layout(
    snapshots: &BTreeMap<PathBuf, ScratchFile>,
) -> Result<(ScratchUsage, BTreeSet<PathBuf>)> {
    let state = scratch_snapshot_state(snapshots)?;
    let directories =
        projected_scratch_directories(&BTreeSet::new(), snapshots.keys().map(PathBuf::as_path))?;
    Ok((state, directories))
}

fn is_exact_checked_duplicate(
    snapshot: &ScratchFile,
    checked: &BTreeMap<PathBuf, ScratchFile>,
) -> bool {
    !is_checked_scratch_snapshot(&snapshot.relative_path)
        && checked
            .get(&checked_scratch_relative_path(
                &snapshot.relative_path,
                &snapshot.bytes,
            ))
            .is_some_and(|checked_snapshot| checked_snapshot.bytes == snapshot.bytes)
}

fn select_scratch_snapshots(
    mut checked: BTreeMap<PathBuf, ScratchFile>,
    untrusted: Vec<ScratchFile>,
) -> BTreeMap<PathBuf, ScratchFile> {
    for snapshot in untrusted {
        if !is_checked_scratch_snapshot(&snapshot.relative_path)
            && !is_exact_checked_duplicate(&snapshot, &checked)
        {
            checked.insert(snapshot.relative_path.clone(), snapshot);
        }
    }
    checked
}

pub(super) const SCRATCH_TRANSACTION_PREFIX: &str = ".scratch-transaction-";

fn remove_stale_scratch_transactions(parent: &Path) -> Result<()> {
    let entries = std::fs::read_dir(parent).map_err(|source| Error::Read {
        path: parent.to_owned(),
        source,
    })?;
    for entry in entries {
        let entry = entry.map_err(|source| Error::Read {
            path: parent.to_owned(),
            source,
        })?;
        let name = entry.file_name();
        let Some(name) = name.to_str() else {
            continue;
        };
        if !name.starts_with(SCRATCH_TRANSACTION_PREFIX) {
            continue;
        }
        let path = entry.path();
        let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
            return Err(Error::ProofAgentCommand(format!(
                "stale scratch transaction {} is not a real directory",
                path.display()
            )));
        }
        std::fs::remove_dir_all(&path).map_err(|source| Error::Write { path, source })?;
    }
    Ok(())
}

fn atomic_exchange_scratch_directories(returned: &Path, live: &Path) -> Result<()> {
    for path in [returned, live] {
        let metadata = std::fs::symlink_metadata(path).map_err(|source| Error::Read {
            path: path.to_owned(),
            source,
        })?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
            return Err(Error::ProofAgentCommand(format!(
                "scratch transaction path {} is not a real directory",
                path.display()
            )));
        }
    }
    let returned_c = CString::new(returned.as_os_str().as_bytes()).map_err(|_| {
        Error::ProofAgentCommand("scratch transaction path contains a NUL byte".to_owned())
    })?;
    let live_c = CString::new(live.as_os_str().as_bytes()).map_err(|_| {
        Error::ProofAgentCommand("live scratch path contains a NUL byte".to_owned())
    })?;
    // SAFETY: both C strings are NUL-terminated paths to host-validated real
    // directories. RENAME_EXCHANGE changes the two directory entries in one
    // atomic namespace operation and does not retain either pointer.
    let status = unsafe {
        libc::syscall(
            libc::SYS_renameat2,
            libc::AT_FDCWD,
            returned_c.as_ptr(),
            libc::AT_FDCWD,
            live_c.as_ptr(),
            libc::RENAME_EXCHANGE,
        )
    };
    if status != 0 {
        return Err(Error::Write {
            path: live.to_owned(),
            source: std::io::Error::last_os_error(),
        });
    }
    let mut parents = BTreeSet::new();
    if let Some(parent) = returned.parent() {
        parents.insert(parent.to_owned());
    }
    if let Some(parent) = live.parent() {
        parents.insert(parent.to_owned());
    }
    for parent in parents {
        File::open(&parent)
            .and_then(|directory| directory.sync_all())
            .map_err(|source| Error::Write {
                path: parent,
                source,
            })?;
    }
    Ok(())
}

fn sync_scratch_transaction_tree(
    root: &Path,
    snapshots: &BTreeMap<PathBuf, ScratchFile>,
    directories: &BTreeSet<PathBuf>,
) -> Result<()> {
    for relative in snapshots.keys() {
        let path = root.join(relative);
        File::open(&path)
            .and_then(|file| file.sync_all())
            .map_err(|source| Error::Write { path, source })?;
    }
    let mut directory_paths = directories
        .iter()
        .map(|relative| root.join(relative))
        .collect::<Vec<_>>();
    directory_paths.sort_by_key(|path| std::cmp::Reverse(path.components().count()));
    for path in directory_paths {
        File::open(&path)
            .and_then(|directory| directory.sync_all())
            .map_err(|source| Error::Write { path, source })?;
    }
    Ok(())
}

pub(super) fn replace_scratch_snapshots_with_pre_exchange_hook<F>(
    root: &Path,
    existing_tree: ScratchTree,
    selected: BTreeMap<PathBuf, ScratchFile>,
    pre_exchange_hook: F,
) -> Result<ScratchUsage>
where
    F: FnOnce(&Path) -> Result<()>,
{
    let (expected_state, selected_directories) = scratch_snapshot_layout(&selected)?;
    let parent = root.parent().ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "live scratch path {} has no parent directory",
            root.display()
        ))
    })?;
    remove_stale_scratch_transactions(parent)?;
    let current_tree = validated_scratch_tree(root)?;
    if current_tree != existing_tree {
        return Err(Error::ProofAgentCommand(
            "live scratch state changed after it was selected for replacement".to_owned(),
        ));
    }
    // A missing live root is the canonical empty tree. Validate that captured
    // state before materializing the directory; otherwise our own mkdir would
    // look like a concurrent state change against ScratchTree::default().
    ensure_scratch_directory(root)?;
    let transaction = tempfile::Builder::new()
        .prefix(SCRATCH_TRANSACTION_PREFIX)
        .tempdir_in(parent)
        .map_err(|source| Error::CreateDir {
            path: parent.to_owned(),
            source,
        })?;
    std::fs::set_permissions(transaction.path(), std::fs::Permissions::from_mode(0o700)).map_err(
        |source| Error::Write {
            path: transaction.path().to_owned(),
            source,
        },
    )?;
    for snapshot in selected.values() {
        write_scratch_snapshot(transaction.path(), snapshot)?;
    }
    let staged_tree = validated_scratch_tree(transaction.path())?;
    let staged_state = ScratchUsage {
        file_count: staged_tree.files.len(),
        total_bytes: staged_tree.files.iter().map(|file| file.bytes.len()).sum(),
    };
    if staged_state != expected_state || staged_tree.directories != selected_directories {
        return Err(Error::ProofAgentCommand(format!(
            "staged scratch transaction drifted: expected {} files/{} bytes, observed {} files/{} bytes",
            expected_state.file_count,
            expected_state.total_bytes,
            staged_state.file_count,
            staged_state.total_bytes
        )));
    }
    sync_scratch_transaction_tree(transaction.path(), &selected, &selected_directories)?;
    pre_exchange_hook(transaction.path())?;
    atomic_exchange_scratch_directories(transaction.path(), root)?;
    let observed = scratch_workspace_state(root)?;
    if observed != expected_state {
        return Err(Error::ProofAgentCommand(format!(
            "compacted scratch state drifted: expected {} files/{} bytes, observed {} files/{} bytes",
            expected_state.file_count,
            expected_state.total_bytes,
            observed.file_count,
            observed.total_bytes
        )));
    }
    transaction.close().map_err(|source| Error::Write {
        path: parent.to_owned(),
        source,
    })?;
    Ok(observed)
}

pub(super) fn replace_scratch_snapshots(
    root: &Path,
    existing_tree: ScratchTree,
    selected: BTreeMap<PathBuf, ScratchFile>,
) -> Result<ScratchUsage> {
    replace_scratch_snapshots_with_pre_exchange_hook(root, existing_tree, selected, |_| Ok(()))
}

fn persist_round_scratch_snapshots(
    persistent_scratch: &Path,
    existing_tree: ScratchTree,
    staged: Vec<ScratchFile>,
) -> Result<ScratchUsage> {
    let existing = existing_tree
        .files
        .iter()
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    // Compile-clean, host-owned snapshots form the trusted base. The
    // staged non-checked namespace is the current round's complete view: it
    // began as a hydration of prior WIP, so absence represents deletion and
    // current bytes must win over stale persistent bytes.
    let checked = existing
        .values()
        .filter(|snapshot| is_checked_scratch_snapshot(&snapshot.relative_path))
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    let selected = select_scratch_snapshots(checked, staged);
    replace_scratch_snapshots(persistent_scratch, existing_tree, selected)
}

pub(super) fn hydrate_round_scratch(proof_workdir: &Path, stage: &Path) -> Result<ScratchUsage> {
    let retained = validated_scratch_files(&proof_workdir.join("scratch"))?;
    merge_scratch_snapshots(&stage.join("scratch"), retained)
}

pub(super) fn is_checked_scratch_snapshot(path: &Path) -> bool {
    path.components().next()
        == Some(std::path::Component::Normal(std::ffi::OsStr::new(
            CHECKED_SCRATCH_DIRECTORY,
        )))
}

fn checked_scratch_relative_path(relative: &Path, bytes: &[u8]) -> PathBuf {
    if is_checked_scratch_snapshot(relative) {
        return relative.to_owned();
    }
    let nested = Path::new(CHECKED_SCRATCH_DIRECTORY).join(relative);
    if validate_scratch_child_path(&nested).is_ok() {
        nested
    } else {
        // Preserve exact checked bytes if a source path cannot be represented
        // in the reserved namespace for a structural reason.
        Path::new(CHECKED_SCRATCH_DIRECTORY).join(format!("sha256-{}.v", sha256_hex(bytes)))
    }
}

pub(super) fn persist_round_scratch(stage: &Path, proof_workdir: &Path) -> Result<ScratchUsage> {
    // Ordinary scratch .v files are explicitly untrusted work in progress.
    // Preserve them even when the agent never submitted them or their latest
    // diagnostic failed. The reserved checked/ subtree is host-owned: only the
    // digest-bound broker may update those passing snapshots, so an unchecked
    // later edit cannot overwrite the last compile-clean copy. An ordinary .v
    // that is byte-identical to its checked snapshot carries no additional
    // information and is omitted. All other structurally valid WIP is retained;
    // the container-wide writable-storage quota is the only storage bound.
    let persistent_scratch = proof_workdir.join("scratch");
    let retained_tree = validated_scratch_tree(&persistent_scratch)?;
    let retained = retained_tree
        .files
        .iter()
        .cloned()
        .map(|snapshot| (snapshot.relative_path, snapshot.bytes))
        .collect::<BTreeMap<_, _>>();
    let staged_files = validated_staged_scratch_files(&stage.join("scratch"))?;
    let staged = staged_files
        .into_iter()
        .filter(|snapshot| {
            if is_checked_scratch_snapshot(&snapshot.relative_path) {
                return false;
            }
            let extension = snapshot
                .relative_path
                .extension()
                .and_then(|extension| extension.to_str());
            if extension != Some("v") {
                return true;
            }
            let checked = checked_scratch_relative_path(&snapshot.relative_path, &snapshot.bytes);
            match retained.get(&checked) {
                Some(checked_bytes) => checked_bytes != &snapshot.bytes,
                None => true,
            }
        })
        .collect::<Vec<_>>();
    persist_round_scratch_snapshots(&persistent_scratch, retained_tree, staged)
}

pub(super) fn persist_successful_scratch_candidate(
    proof_workdir: &Path,
    candidate_path: &Path,
    bytes: &[u8],
) -> Result<ScratchUsage> {
    let relative = candidate_path.strip_prefix("scratch").map_err(|_| {
        Error::ProofAgentCommand("successful scratch candidate escaped scratch/".to_owned())
    })?;
    if is_checked_scratch_snapshot(relative) {
        return Err(Error::ProofAgentCommand(
            "successful scratch candidate used the reserved checked/ namespace".to_owned(),
        ));
    }
    validate_scratch_child_path(relative).map_err(Error::ProofAgentCommand)?;
    std::str::from_utf8(bytes).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "scratch file {} is not UTF-8: {source}",
            relative.display()
        ))
    })?;
    let checked_relative = checked_scratch_relative_path(relative, bytes);
    validate_scratch_child_path(&checked_relative).map_err(Error::ProofAgentCommand)?;
    let persistent_scratch = proof_workdir.join("scratch");
    let existing_tree = validated_scratch_tree(&persistent_scratch)?;
    let existing = existing_tree
        .files
        .iter()
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    let mut checked = existing
        .values()
        .filter(|snapshot| is_checked_scratch_snapshot(&snapshot.relative_path))
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    checked.insert(
        checked_relative.clone(),
        ScratchFile {
            relative_path: checked_relative,
            bytes: bytes.to_vec(),
        },
    );
    let untrusted = existing
        .values()
        .filter(|snapshot| !is_checked_scratch_snapshot(&snapshot.relative_path))
        .cloned()
        .collect::<Vec<_>>();
    let selected = select_scratch_snapshots(checked, untrusted);
    replace_scratch_snapshots(&persistent_scratch, existing_tree, selected)
}

#[cfg(test)]
pub(super) fn persist_successful_proof_module_candidate(
    proof_workdir: &Path,
    candidate_path: &Path,
    bytes: &[u8],
) -> Result<()> {
    ModulePublication::prepare(proof_workdir, candidate_path, bytes, true)?.commit();
    Ok(())
}

/// A module source is installed in the host workspace immediately before its
/// serialized checker invocation, but remains pending until that exact source
/// has been promoted into the host-only cache. The broker is single-threaded,
/// so no later diagnostic can reuse the pending source; dependency resolution
/// sees only the cache's previously checked `.vo` prefix. On checker failure the
/// newly installed source is removed, while a successful cache publication can
/// never precede durable source installation.
pub(super) struct ModulePublication {
    pub(super) destination: PathBuf,
    pub(super) remove_on_drop: bool,
}

impl ModulePublication {
    pub(super) fn prepare(
        proof_workdir: &Path,
        candidate_path: &Path,
        bytes: &[u8],
        checked_in_cache: bool,
    ) -> Result<Self> {
        let candidate = candidate_path.to_str().ok_or_else(|| {
            Error::ProofAgentCommand("proof module candidate path is not UTF-8".to_owned())
        })?;
        validate_proof_module_candidate_path(candidate).map_err(Error::ProofAgentCommand)?;
        std::str::from_utf8(bytes).map_err(|source| {
            Error::ProofAgentCommand(format!("proof module {candidate} is not UTF-8: {source}"))
        })?;
        let module_root = proof_workdir.join(PROOF_MODULE_DIRECTORY);
        ensure_scratch_directory(&module_root)?;
        let destination = proof_workdir.join(candidate_path);
        match std::fs::symlink_metadata(&destination) {
            Ok(metadata) => {
                if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
                    return Err(Error::ProofAgentCommand(format!(
                        "proof module destination {} is not a regular non-symlink file",
                        destination.display()
                    )));
                }
                if checked_in_cache {
                    let existing = std::fs::read(&destination).map_err(|source| Error::Read {
                        path: destination.clone(),
                        source,
                    })?;
                    if existing != bytes {
                        return Err(Error::ProofAgentCommand(format!(
                            "checked proof module {candidate} is immutable; create a new module name for a revised theorem"
                        )));
                    }
                    return Ok(Self {
                        destination,
                        remove_on_drop: false,
                    });
                }
                // A source absent from the ordered host cache is an orphan from
                // an interrupted, never-successful promotion, not an immutable
                // checked name. Remove it before staging this new diagnostic so
                // a revision can reuse a name that was never published.
                std::fs::remove_file(&destination).map_err(|source| Error::Write {
                    path: destination.clone(),
                    source,
                })?;
            }
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
            Err(source) => {
                return Err(Error::Read {
                    path: destination,
                    source,
                });
            }
        }
        let temporary = module_root.join(format!(
            ".module-write-{}-{}",
            std::process::id(),
            now_ms_since_epoch()
        ));
        let result = (|| -> Result<()> {
            let mut staged = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(&temporary)
                .map_err(|source| Error::Write {
                    path: temporary.clone(),
                    source,
                })?;
            staged.write_all(bytes).map_err(|source| Error::Write {
                path: temporary.clone(),
                source,
            })?;
            staged.flush().map_err(|source| Error::Write {
                path: temporary.clone(),
                source,
            })?;
            drop(staged);
            std::fs::rename(&temporary, &destination).map_err(|source| Error::Write {
                path: destination.clone(),
                source,
            })?;
            Ok(())
        })();
        if result.is_err() {
            let _ = std::fs::remove_file(&temporary);
        }
        result?;
        Ok(Self {
            destination,
            remove_on_drop: !checked_in_cache,
        })
    }

    pub(super) fn commit(mut self) {
        self.remove_on_drop = false;
    }

    pub(super) fn rollback(mut self) -> Result<()> {
        if self.remove_on_drop {
            std::fs::remove_file(&self.destination).map_err(|source| Error::Write {
                path: self.destination.clone(),
                source,
            })?;
            self.remove_on_drop = false;
        }
        Ok(())
    }
}

impl Drop for ModulePublication {
    fn drop(&mut self) {
        if self.remove_on_drop {
            let _ = std::fs::remove_file(&self.destination);
        }
    }
}

pub(super) fn trusted_diagnostic_cache_directory(trusted_checker_path: &Path) -> PathBuf {
    trusted_checker_path
        .parent()
        .and_then(Path::parent)
        .expect("trusted checker is materialized under proof-agent/trusted-launcher")
        .join("trusted-diagnostic-cache")
}

fn collect_trusted_cache_regular_files(
    root: &Path,
    directory: &Path,
    files: &mut BTreeSet<PathBuf>,
) -> Result<()> {
    for entry in std::fs::read_dir(directory).map_err(|source| Error::Read {
        path: directory.to_owned(),
        source,
    })? {
        let entry = entry.map_err(|source| Error::Read {
            path: directory.to_owned(),
            source,
        })?;
        let path = entry.path();
        let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink() {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache contains a symlink: {}",
                path.display()
            )));
        }
        if metadata.is_dir() {
            collect_trusted_cache_regular_files(root, &path, files)?;
            continue;
        }
        if !metadata.file_type().is_file() {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache contains a non-regular entry: {}",
                path.display()
            )));
        }
        let relative = path.strip_prefix(root).map_err(|_| {
            Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache entry escaped its root: {}",
                path.display()
            ))
        })?;
        if relative != Path::new("SHA256SUMS") {
            files.insert(relative.to_owned());
        }
    }
    Ok(())
}

pub(super) fn archive_trusted_diagnostic_cache(
    artifacts: &ArtifactWriter,
    workspace_generation: usize,
) -> Result<TrustedDiagnosticCacheEvidence> {
    if workspace_generation == 0 {
        return Err(Error::TrustedRocqEnvironment(
            "proof workspace generation must be positive".to_owned(),
        ));
    }
    let source_root = artifacts
        .root()
        .join("proof-stage/proof-agent/trusted-diagnostic-cache");
    let source_metadata =
        std::fs::symlink_metadata(&source_root).map_err(|source| Error::Read {
            path: source_root.clone(),
            source,
        })?;
    if source_metadata.file_type().is_symlink() || !source_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted diagnostic cache archive source is unsafe: {}",
            source_root.display()
        )));
    }

    let read_regular = |relative: &Path, allow_empty: bool| -> Result<Vec<u8>> {
        let path = source_root.join(relative);
        let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink()
            || !metadata.file_type().is_file()
            || (!allow_empty && metadata.len() == 0)
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache archive entry is unsafe: {}",
                path.display()
            )));
        }
        std::fs::read(&path).map_err(|source| Error::Read { path, source })
    };
    let module_root = source_root.join(PROOF_MODULE_DIRECTORY);
    let module_metadata =
        std::fs::symlink_metadata(&module_root).map_err(|source| Error::Read {
            path: module_root.clone(),
            source,
        })?;
    if module_metadata.file_type().is_symlink() || !module_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted diagnostic module cache archive source is unsafe: {}",
            module_root.display()
        )));
    }
    let order_relative = PathBuf::from("ProofModules/ORDER");
    let order_bytes = read_regular(&order_relative, true)?;
    let order = std::str::from_utf8(&order_bytes).map_err(|source| {
        Error::TrustedRocqEnvironment(format!("trusted proof module order is not UTF-8: {source}"))
    })?;
    let module_names = order.lines().map(str::to_owned).collect::<Vec<_>>();
    if order
        != module_names
            .iter()
            .map(|name| format!("{name}\n"))
            .collect::<String>()
    {
        return Err(Error::TrustedRocqEnvironment(
            "trusted proof module order is not canonical newline-delimited text".to_owned(),
        ));
    }
    let mut unique_modules = BTreeSet::new();
    for name in &module_names {
        validate_proof_module_candidate_path(&format!("{PROOF_MODULE_DIRECTORY}/{name}"))
            .map_err(Error::TrustedRocqEnvironment)?;
        if !unique_modules.insert(name.clone()) {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted proof module order contains a duplicate entry: {name}"
            )));
        }
    }

    let witness_module_root = source_root.join(WITNESS_MODULE_DIRECTORY);
    let witness_module_metadata =
        std::fs::symlink_metadata(&witness_module_root).map_err(|source| Error::Read {
            path: witness_module_root.clone(),
            source,
        })?;
    if witness_module_metadata.file_type().is_symlink() || !witness_module_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted witness module cache archive source is unsafe: {}",
            witness_module_root.display()
        )));
    }
    let witness_order_relative = PathBuf::from("WitnessModules/ORDER");
    let witness_order_bytes = read_regular(&witness_order_relative, true)?;
    let witness_order = std::str::from_utf8(&witness_order_bytes).map_err(|source| {
        Error::TrustedRocqEnvironment(format!(
            "trusted witness module order is not UTF-8: {source}"
        ))
    })?;
    let witness_module_names = witness_order.lines().map(str::to_owned).collect::<Vec<_>>();
    if witness_order
        != witness_module_names
            .iter()
            .map(|name| format!("{name}\n"))
            .collect::<String>()
    {
        return Err(Error::TrustedRocqEnvironment(
            "trusted witness module order is not canonical newline-delimited text".to_owned(),
        ));
    }
    let mut unique_witness_modules = BTreeSet::new();
    for name in &witness_module_names {
        let valid = name.strip_suffix(".v").is_some_and(|stem| {
            stem.starts_with(|character: char| character.is_ascii_uppercase())
                && stem
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        });
        if !valid || !unique_witness_modules.insert(name.clone()) {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted witness module order contains an invalid or duplicate entry: {name}"
            )));
        }
    }

    let manifest_relative = PathBuf::from("SHA256SUMS");
    let manifest_bytes = read_regular(&manifest_relative, false)?;
    let manifest_text = std::str::from_utf8(&manifest_bytes).map_err(|source| {
        Error::TrustedRocqEnvironment(format!(
            "trusted diagnostic cache manifest is not UTF-8: {source}"
        ))
    })?;
    let mut manifest_entries = BTreeMap::new();
    let mut manifest_order = Vec::new();
    for line in manifest_text.lines() {
        let Some((digest, relative)) = line.split_once("  ") else {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache manifest contains a malformed line: {line:?}"
            )));
        };
        let relative_path = PathBuf::from(relative);
        let components = relative_path
            .components()
            .map(|component| component.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        let filename = components.last().map(String::as_str).unwrap_or_default();
        let allowed_module = filename.ends_with(".v") || filename.ends_with(".vo");
        let allowed_order = components.len() >= 2 && filename == "ORDER";
        if digest.len() != 64
            || !digest
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
            || relative.is_empty()
            || relative_path.is_absolute()
            || components
                .iter()
                .any(|part| matches!(part.as_str(), "" | "." | ".."))
            || (!allowed_module && !allowed_order)
            || manifest_entries
                .insert(relative_path.clone(), digest.to_owned())
                .is_some()
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache manifest contains an unsafe or duplicate entry: {line:?}"
            )));
        }
        manifest_order.push(relative_path);
    }

    let mut actual_entries = BTreeSet::new();
    collect_trusted_cache_regular_files(&source_root, &source_root, &mut actual_entries)?;
    if actual_entries != manifest_entries.keys().cloned().collect() {
        return Err(Error::TrustedRocqEnvironment(
            "trusted diagnostic cache manifest does not cover exactly the regular cache files"
                .to_owned(),
        ));
    }

    let expected_nested_entries = |directory: &str, names: &[String]| {
        let mut expected = BTreeSet::from([PathBuf::from(directory).join("ORDER")]);
        for name in names {
            let stem = name
                .strip_suffix(".v")
                .expect("validated ordered module has a .v suffix");
            expected.insert(PathBuf::from(directory).join(name));
            expected.insert(PathBuf::from(directory).join(format!("{stem}.vo")));
        }
        expected
    };
    for (directory, names) in [
        (PROOF_MODULE_DIRECTORY, module_names.as_slice()),
        (WITNESS_MODULE_DIRECTORY, witness_module_names.as_slice()),
    ] {
        let observed = manifest_entries
            .keys()
            .filter(|path| path.starts_with(directory))
            .cloned()
            .collect::<BTreeSet<_>>();
        if observed != expected_nested_entries(directory, names) {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache {directory} entries do not match its ORDER registry"
            )));
        }
    }
    let sources = manifest_entries
        .keys()
        .filter_map(|path| {
            path.extension()
                .is_some_and(|extension| extension == "v")
                .then(|| path.with_extension(""))
        })
        .collect::<BTreeSet<_>>();
    let objects = manifest_entries
        .keys()
        .filter_map(|path| {
            path.extension()
                .is_some_and(|extension| extension == "vo")
                .then(|| path.with_extension(""))
        })
        .collect::<BTreeSet<_>>();
    if sources.is_empty() || sources != objects {
        return Err(Error::TrustedRocqEnvironment(
            "trusted diagnostic cache modules are not nonempty source/object pairs".to_owned(),
        ));
    }

    let mut files = Vec::new();
    for relative in &manifest_order {
        let bytes = read_regular(
            relative,
            relative == &order_relative || relative == &witness_order_relative,
        )?;
        let observed_digest = sha256_hex(&bytes);
        if manifest_entries.get(relative).map(String::as_str) != Some(observed_digest.as_str()) {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache digest binding is invalid for {}",
                relative.display()
            )));
        }
        files.push((relative.clone(), bytes));
    }
    for (relative, cached_bytes) in files.iter().filter(|(relative, _)| {
        relative
            .extension()
            .is_some_and(|extension| extension == "v")
    }) {
        let live = artifacts
            .root()
            .join("proof-stage/formal-sql")
            .join(relative);
        let live_bytes =
            std::fs::read(&live).map_err(|source| Error::Read { path: live, source })?;
        if *cached_bytes != live_bytes {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache source binding drifted before archive: {}",
                relative.display()
            )));
        }
    }
    files.push((manifest_relative, manifest_bytes.clone()));

    let destination_root = artifacts.root().join(format!(
        "proof-stage/proof-agent/workspace-generations/{workspace_generation:04}/trusted-diagnostic-cache"
    ));
    let destination_parent = destination_root.parent().ok_or_else(|| {
        Error::TrustedRocqEnvironment("trusted cache archive path has no parent".to_owned())
    })?;
    std::fs::create_dir_all(destination_parent).map_err(|source| Error::CreateDir {
        path: destination_parent.to_owned(),
        source,
    })?;
    std::fs::create_dir(&destination_root).map_err(|source| {
        Error::TrustedRocqEnvironment(format!(
            "refusing to replace create-once trusted cache archive {}: {source}",
            destination_root.display()
        ))
    })?;
    for (relative, bytes) in files {
        let path = destination_root.join(relative);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
                path: parent.to_owned(),
                source,
            })?;
        }
        std::fs::write(&path, bytes).map_err(|source| Error::Write { path, source })?;
    }
    let manifest_path = format!(
        "proof-stage/proof-agent/workspace-generations/{workspace_generation:04}/trusted-diagnostic-cache/SHA256SUMS"
    );
    Ok(TrustedDiagnosticCacheEvidence {
        workspace_generation,
        manifest_path,
        manifest_sha256: sha256_hex(&manifest_bytes),
    })
}

pub(super) fn recover_interrupted_trusted_cache_swap(trusted_checker_path: &Path) -> Result<()> {
    let trusted_cache = trusted_diagnostic_cache_directory(trusted_checker_path);
    let cache_parent = trusted_cache
        .parent()
        .expect("trusted diagnostic cache has a parent");
    let parent_metadata =
        std::fs::symlink_metadata(cache_parent).map_err(|source| Error::Read {
            path: cache_parent.to_owned(),
            source,
        })?;
    if parent_metadata.file_type().is_symlink() || !parent_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted diagnostic cache parent is unsafe: {}",
            cache_parent.display()
        )));
    }
    let mut old_candidates = Vec::new();
    let mut stage_candidates = Vec::new();
    for entry in std::fs::read_dir(cache_parent).map_err(|source| Error::Read {
        path: cache_parent.to_owned(),
        source,
    })? {
        let entry = entry.map_err(|source| Error::Read {
            path: cache_parent.to_owned(),
            source,
        })?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let target = if name.starts_with(".logos-trusted-diagnostic-cache-old.") {
            &mut old_candidates
        } else if name.starts_with(".logos-trusted-diagnostic-cache.") {
            &mut stage_candidates
        } else {
            continue;
        };
        let path = entry.path();
        let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(Error::TrustedRocqEnvironment(format!(
                "interrupted trusted-cache artifact is unsafe: {}",
                path.display()
            )));
        }
        target.push(path);
    }
    match std::fs::symlink_metadata(&trusted_cache) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache is unsafe: {}",
                trusted_cache.display()
            )));
        }
        Ok(_) => {}
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => {
            if old_candidates.len() != 1 {
                return Err(Error::TrustedRocqEnvironment(format!(
                    "trusted diagnostic cache is missing with {} recoverable prior caches",
                    old_candidates.len()
                )));
            }
            std::fs::rename(&old_candidates[0], &trusted_cache).map_err(|source| Error::Write {
                path: trusted_cache.clone(),
                source,
            })?;
        }
        Err(source) => {
            return Err(Error::Read {
                path: trusted_cache,
                source,
            });
        }
    }
    for stage in stage_candidates {
        std::fs::remove_dir_all(&stage).map_err(|source| Error::Write {
            path: stage,
            source,
        })?;
    }
    Ok(())
}

/// Return the host-cache source for `candidate_path` only when the ordered
/// module registry says the name is checked and its source/object pair is safe.
/// Absence from ORDER means a same-named workspace file is merely an orphaned
/// pre-publication source and must not acquire append-only status.
pub(super) fn checked_proof_module_cache_source(
    trusted_checker_path: &Path,
    candidate_path: &Path,
) -> Result<Option<Vec<u8>>> {
    let candidate = candidate_path.to_str().ok_or_else(|| {
        Error::TrustedRocqEnvironment("proof module candidate path is not UTF-8".to_owned())
    })?;
    validate_proof_module_candidate_path(candidate).map_err(Error::TrustedRocqEnvironment)?;
    let file_name = candidate_path
        .file_name()
        .and_then(|name| name.to_str())
        .expect("validated proof module path has a UTF-8 file name");
    let stem = file_name
        .strip_suffix(".v")
        .expect("validated proof module source has a .v suffix");
    let cache_root = trusted_diagnostic_cache_directory(trusted_checker_path);
    let module_root = cache_root.join(PROOF_MODULE_DIRECTORY);
    let root_metadata = std::fs::symlink_metadata(&module_root).map_err(|source| Error::Read {
        path: module_root.clone(),
        source,
    })?;
    if root_metadata.file_type().is_symlink() || !root_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted proof module cache is not a regular directory: {}",
            module_root.display()
        )));
    }
    let order_path = module_root.join("ORDER");
    let order_metadata = std::fs::symlink_metadata(&order_path).map_err(|source| Error::Read {
        path: order_path.clone(),
        source,
    })?;
    if order_metadata.file_type().is_symlink() || !order_metadata.file_type().is_file() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted proof module order is not a regular file: {}",
            order_path.display()
        )));
    }
    let order = std::fs::read_to_string(&order_path).map_err(|source| Error::Read {
        path: order_path.clone(),
        source,
    })?;
    let manifest_path = cache_root.join("SHA256SUMS");
    let manifest_metadata =
        std::fs::symlink_metadata(&manifest_path).map_err(|source| Error::Read {
            path: manifest_path.clone(),
            source,
        })?;
    if manifest_metadata.file_type().is_symlink()
        || !manifest_metadata.file_type().is_file()
        || manifest_metadata.len() == 0
    {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted diagnostic cache manifest is unsafe or empty: {}",
            manifest_path.display()
        )));
    }
    let manifest = std::fs::read_to_string(&manifest_path).map_err(|source| Error::Read {
        path: manifest_path.clone(),
        source,
    })?;
    let mut manifest_digests = BTreeMap::new();
    for line in manifest.lines() {
        let Some((digest, relative)) = line.split_once("  ") else {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache manifest contains a malformed line: {line:?}"
            )));
        };
        if digest.len() != 64
            || !digest
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
            || relative.is_empty()
            || manifest_digests
                .insert(relative.to_owned(), digest.to_owned())
                .is_some()
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache manifest contains an invalid or duplicate entry: {line:?}"
            )));
        }
    }
    let expected_order_digest = sha256_hex(order.as_bytes());
    if manifest_digests
        .get("ProofModules/ORDER")
        .map(String::as_str)
        != Some(expected_order_digest.as_str())
    {
        return Err(Error::TrustedRocqEnvironment(
            "trusted proof module order digest is not bound by the cache manifest".to_owned(),
        ));
    }
    let mut names = BTreeSet::new();
    for entry in order.lines().filter(|entry| !entry.is_empty()) {
        validate_proof_module_candidate_path(&format!("{PROOF_MODULE_DIRECTORY}/{entry}"))
            .map_err(|error| {
                Error::TrustedRocqEnvironment(format!(
                    "trusted proof module order contains an invalid entry {entry:?}: {error}"
                ))
            })?;
        if !names.insert(entry.to_owned()) {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted proof module order contains a duplicate entry: {entry}"
            )));
        }
    }
    let source_path = module_root.join(file_name);
    let object_path = module_root.join(format!("{stem}.vo"));
    let source_relative = format!("ProofModules/{file_name}");
    let object_relative = format!("ProofModules/{stem}.vo");
    if !names.contains(file_name) {
        if source_path.exists()
            || std::fs::symlink_metadata(&source_path).is_ok()
            || object_path.exists()
            || std::fs::symlink_metadata(&object_path).is_ok()
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted proof module cache contains an unordered entry for {file_name}"
            )));
        }
        if manifest_digests.contains_key(&source_relative)
            || manifest_digests.contains_key(&object_relative)
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache manifest contains an unordered entry for {file_name}"
            )));
        }
        return Ok(None);
    }
    for path in [&source_path, &object_path] {
        let metadata = std::fs::symlink_metadata(path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink()
            || !metadata.file_type().is_file()
            || metadata.len() == 0
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted proof module cache entry is unsafe or empty: {}",
                path.display()
            )));
        }
    }
    let source = std::fs::read(&source_path).map_err(|source| Error::Read {
        path: source_path,
        source,
    })?;
    let object = std::fs::read(&object_path).map_err(|source| Error::Read {
        path: object_path,
        source,
    })?;
    let source_digest = sha256_hex(&source);
    let object_digest = sha256_hex(&object);
    if manifest_digests.get(&source_relative).map(String::as_str) != Some(source_digest.as_str())
        || manifest_digests.get(&object_relative).map(String::as_str)
            != Some(object_digest.as_str())
    {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted cache source/object digest binding is invalid for {file_name}"
        )));
    }
    Ok(Some(source))
}
