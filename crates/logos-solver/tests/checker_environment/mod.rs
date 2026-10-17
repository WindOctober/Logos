// Included by the private checker module, not a standalone test crate.
use super::*;

#[test]
fn validation_receipts_are_explicit_private_and_not_reused_after_restart() {
    let root = tempfile::tempdir().unwrap();
    let environment = DiagnosticEnvironment::new(root.path()).unwrap();
    let receipt_dir = environment.0.path().to_owned();
    assert_eq!(
        std::fs::metadata(&receipt_dir)
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o700
    );
    std::fs::write(receipt_dir.join("authority.valid"), b"").unwrap();
    let restarted = DiagnosticEnvironment::new(root.path()).unwrap();
    assert_ne!(restarted.0.path(), receipt_dir);
    assert_eq!(std::fs::read_dir(restarted.0.path()).unwrap().count(), 0);

    let mut command = trusted_rocq_check_command(
        &root.path().join("checker.sh"),
        &root.path().join("workspace"),
        &root.path().join("authority"),
        None,
        Duration::from_secs(1),
        CheckMode::ProblemDiagnostic { timeout_seconds: 1 },
    );
    assert!(
        !command
            .get_envs()
            .any(|(name, _)| name == "LOGOS_ROCQ_VALIDATION_SESSION")
    );
    environment.configure(&mut command);
    assert!(
        command
            .get_envs()
            .any(|(name, value)| name == "LOGOS_ROCQ_VALIDATION_SESSION"
                && value == Some(receipt_dir.as_os_str()))
    );
    drop(environment);
    assert!(!receipt_dir.exists());
    assert!(restarted.0.path().exists());
}
