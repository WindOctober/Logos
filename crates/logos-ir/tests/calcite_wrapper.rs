use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use logos_ir::calcite::CalciteFile;
use logos_ir::convert_raw_file;
use logos_ir::ir::{RelExpr, ScalarAst};

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_submillisecond_timestamp_cast() {
    let repo = repo_root();
    let temp = std::env::temp_dir().join(format!(
        "logos-ir-calcite-wrapper-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).unwrap();
    }
    fs::create_dir_all(&temp).unwrap();
    let schema = temp.join("schema.sql");
    let query = temp.join("query.sql");
    fs::write(&schema, "create table R(id int);\n").unwrap();
    fs::write(
        &query,
        "select cast('1970-01-01 00:00:01.123456' as timestamp(6)) as ts from R;\n",
    )
    .unwrap();

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema)
        .arg("--sql")
        .arg(&query)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let calcite: CalciteFile = serde_json::from_slice(&output.stdout).unwrap();
    let ir = convert_raw_file(calcite).unwrap();
    let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
        panic!("expected top-level project");
    };
    assert_eq!(
        exprs[0].parsed,
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Literal {
                raw: "1970-01-01 00:00:01.123456".to_owned()
            }),
            ty: "TIMESTAMP(6)".to_owned()
        }
    );
    fs::remove_dir_all(&temp).unwrap();
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("logos-ir must live under Logos/crates/logos-ir")
        .to_path_buf()
}
