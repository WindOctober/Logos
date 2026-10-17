// Included by the private diagnostic_inputs module, not a standalone test crate.
use super::*;
use std::os::unix::fs::{MetadataExt, symlink};

fn fixture() -> (tempfile::TempDir, PathBuf) {
    let root = tempfile::tempdir().unwrap();
    let workspace = root.path().join("workspace");
    fs::create_dir_all(workspace.join("WitnessModules")).unwrap();
    for name in COMMON_FILES {
        fs::write(workspace.join(name), format!("(* {name} *)\n")).unwrap();
    }
    fs::write(workspace.join("WitnessModules/ORDER"), "Facts.v\n").unwrap();
    fs::write(
        workspace.join("WitnessModules/Facts.v"),
        "Lemma fact : True.\n",
    )
    .unwrap();
    (root, workspace)
}

#[test]
fn shared_inputs_reuse_private_inodes_across_requests_and_rounds() {
    let (root, workspace) = fixture();
    let inputs = SharedInputs::prepare(root.path(), &workspace, 1).unwrap();
    let first = tempfile::tempdir_in(root.path()).unwrap();
    let second = tempfile::tempdir_in(root.path()).unwrap();
    inputs.link_into(first.path()).unwrap();
    let reopened = SharedInputs::prepare(root.path(), &workspace, 1).unwrap();
    reopened.link_into(second.path()).unwrap();
    for path in &inputs.files {
        let original = fs::metadata(workspace.join(path)).unwrap();
        let saved = fs::metadata(inputs.root.join(path)).unwrap();
        assert_ne!(original.ino(), saved.ino(), "never link live inputs");
        assert_eq!(saved.permissions().mode() & 0o222, 0);
        for snapshot in [first.path(), second.path()] {
            let linked = fs::symlink_metadata(snapshot.join(path)).unwrap();
            assert!(linked.is_file());
            assert_eq!((linked.dev(), linked.ino()), (saved.dev(), saved.ino()));
        }
    }
    let reference: serde_json::Value =
        serde_json::from_slice(&fs::read(first.path().join("shared-inputs.json")).unwrap())
            .unwrap();
    let manifest = fs::read(root.path().join(reference["path"].as_str().unwrap())).unwrap();
    assert_eq!(reference["sha256"], sha256_hex(&manifest));
    assert_eq!(reference["bytes"], manifest.len());
    let manifest: serde_json::Value = serde_json::from_slice(&manifest).unwrap();
    assert_eq!(manifest["workspaceGeneration"], 1);
    for file in manifest["files"].as_array().unwrap() {
        let bytes = fs::read(root.path().join(file["path"].as_str().unwrap())).unwrap();
        assert_eq!(file["sha256"], sha256_hex(&bytes));
        assert_eq!(file["bytes"], bytes.len());
    }
    drop(first);
    assert_eq!(
        read_inputs(second.path(), true).unwrap(),
        read_inputs(&workspace, false).unwrap()
    );
    assert!(inputs.root.join("Schema.v").is_file());
}

#[test]
fn shared_inputs_isolate_live_changes_and_new_generations() {
    let (root, workspace) = fixture();
    let old = SharedInputs::prepare(root.path(), &workspace, 1).unwrap();
    let bytes = fs::read(old.root.join("Witness.v")).unwrap();
    fs::write(workspace.join("Witness.v"), "(* replacement witness *)\n").unwrap();
    let view = tempfile::tempdir_in(root.path()).unwrap();
    old.link_into(view.path()).unwrap();
    assert_eq!(fs::read(view.path().join("Witness.v")).unwrap(), bytes);
    assert!(SharedInputs::prepare(root.path(), &workspace, 1).is_err());
    let new = SharedInputs::prepare(root.path(), &workspace, 2).unwrap();
    assert_ne!(old.root, new.root);
    assert_ne!(
        fs::metadata(old.root.join("Schema.v")).unwrap().ino(),
        fs::metadata(new.root.join("Schema.v")).unwrap().ino()
    );
    assert_eq!(fs::read(old.root.join("Witness.v")).unwrap(), bytes);
    assert_eq!(
        read_inputs(&new.root, true).unwrap(),
        read_inputs(&workspace, false).unwrap()
    );
}

#[test]
fn shared_inputs_reject_persisted_corruption_and_writable_files() {
    for name in ["Schema.v", "WitnessModules/Facts.v", "manifest.json"] {
        let (root, workspace) = fixture();
        let inputs = SharedInputs::prepare(root.path(), &workspace, 1).unwrap();
        let path = inputs.root.join(name);
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        assert!(SharedInputs::prepare(root.path(), &workspace, 1).is_err());
        fs::write(&path, "corrupt").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o400)).unwrap();
        assert!(SharedInputs::prepare(root.path(), &workspace, 1).is_err());
        assert_eq!(
            fs::read(&path).unwrap(),
            b"corrupt",
            "never silently rebuild evidence"
        );
    }
}

#[test]
fn shared_inputs_reject_symlinks_and_witness_file_set_drift() {
    for name in ["Schema.v", "WitnessModules", "WitnessModules/Facts.v"] {
        let (root, workspace) = fixture();
        let original = workspace.join(name);
        let moved = root.path().join("moved");
        fs::rename(&original, &moved).unwrap();
        symlink(&moved, &original).unwrap();
        assert!(SharedInputs::prepare(root.path(), &workspace, 1).is_err());
        assert!(
            !root
                .path()
                .join("proof-stage/proof-agent/diagnostic-inputs/0001")
                .exists()
        );
    }
    let (root, workspace) = fixture();
    let inputs = SharedInputs::prepare(root.path(), &workspace, 1).unwrap();
    write_readonly(&inputs.root.join("WitnessModules/Extra.v"), b"extra").unwrap();
    assert!(SharedInputs::prepare(root.path(), &workspace, 1).is_err());
    fs::remove_file(inputs.root.join("WitnessModules/Extra.v")).unwrap();
    fs::write(workspace.join("WitnessModules/Extra.v"), b"extra").unwrap();
    assert!(SharedInputs::prepare(root.path(), &workspace, 1).is_err());
}

#[test]
fn shared_inputs_never_overwrite_existing_diagnostic_files() {
    let (root, workspace) = fixture();
    let inputs = SharedInputs::prepare(root.path(), &workspace, 1).unwrap();
    let view = tempfile::tempdir_in(root.path()).unwrap();
    fs::write(view.path().join("Goal.v"), b"existing").unwrap();
    assert!(inputs.link_into(view.path()).is_err());
    assert_eq!(fs::read(view.path().join("Goal.v")).unwrap(), b"existing");
    assert_eq!(
        read_inputs(&inputs.root, true).unwrap(),
        read_inputs(&workspace, false).unwrap()
    );
}

#[test]
fn shared_inputs_reject_redirected_or_nonprivate_generations() {
    let (root, workspace) = fixture();
    let inputs = SharedInputs::prepare(root.path(), &workspace, 1).unwrap();
    fs::set_permissions(&inputs.root, fs::Permissions::from_mode(0o777)).unwrap();
    assert!(SharedInputs::prepare(root.path(), &workspace, 1).is_err());
    fs::set_permissions(&inputs.root, fs::Permissions::from_mode(0o700)).unwrap();
    let moved = root.path().join("moved-generation");
    fs::rename(&inputs.root, &moved).unwrap();
    symlink(&moved, &inputs.root).unwrap();
    assert!(SharedInputs::prepare(root.path(), &workspace, 1).is_err());
}
