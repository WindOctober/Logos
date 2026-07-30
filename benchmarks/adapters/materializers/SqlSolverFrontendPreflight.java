import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Base64;
import java.util.List;

import org.apache.calcite.jdbc.CalciteSchema;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.tools.Planner;

import sqlsolver.sql.SqlSupport;
import sqlsolver.sql.calcite.CalciteSupport;
import sqlsolver.sql.preprocess.rewrite.SqlNodePreprocess;
import sqlsolver.sql.schema.Schema;

/**
 * Parser/validator/planner-only preflight against SQLSolver's actual frontend.
 *
 * This deliberately mirrors VerificationImpl.readPairs through RelNode
 * construction and stops before plan comparison or proof search.  Machine
 * output is tab-separated with Base64 fields so the Python wrapper can produce
 * stable JSON without depending on a second Java JSON library.
 */
public final class SqlSolverFrontendPreflight {
  private SqlSolverFrontendPreflight() {}

  public static void main(String[] args) throws Exception {
    if (args.length != 3) {
      System.err.println("usage: SqlSolverFrontendPreflight <schema> <sql1> <sql2>");
      System.exit(2);
    }

    final String schemaSql = Files.readString(Path.of(args[0]));
    final String sql1 = oneQueryLine(Path.of(args[1]));
    final String sql2 = oneQueryLine(Path.of(args[2]));
    final Schema schema;
    final CalciteSchema calciteSchema;
    try {
      schema = CalciteSupport.getSchema(schemaSql);
      if (schema == null) throw new IllegalArgumentException("schema parser returned null");
      calciteSchema = CalciteSupport.getCalciteSchema(schema);
      if (calciteSchema == null) throw new IllegalArgumentException("Calcite schema returned null");
    } catch (Throwable error) {
      emit("schema", "unsupported", "schema", error, null, List.of());
      return;
    }

    SqlNodePreprocess.setSchema(schema);
    CalciteSupport.USER_DEFINED_FUNCTIONS.clear();
    CalciteSupport.addUserDefinedFunctions(List.of(sql1, sql2));
    preflight("before", sql1, calciteSchema);
    preflight("after", sql2, calciteSchema);
  }

  private static String oneQueryLine(Path path) throws Exception {
    final List<String> lines = Files.readAllLines(path);
    if (lines.size() != 1) {
      throw new IllegalArgumentException(path + " must contain exactly one query line");
    }
    return lines.get(0);
  }

  private static void preflight(String side, String original, CalciteSchema schema) {
    String preprocessed = null;
    try {
      preprocessed = SqlSupport.parsePreprocess(
          original, CalciteSupport.getPlanner(schema));
    } catch (Throwable error) {
      emit(side, "unsupported", "preprocess", error, preprocessed, List.of());
      return;
    }

    final Planner planner = CalciteSupport.getPlanner(schema);
    final SqlNode parsed;
    try {
      parsed = planner.parse(preprocessed);
    } catch (Throwable error) {
      emit(side, "unsupported", "parser", error, preprocessed, List.of());
      return;
    }

    final SqlNode validated;
    try {
      validated = planner.validate(parsed);
    } catch (Throwable error) {
      emit(side, "unsupported", "validator", error, preprocessed, List.of());
      return;
    }

    final RelNode plan;
    try {
      plan = planner.rel(validated).rel;
      if (plan == null) throw new IllegalStateException("planner returned null RelNode");
    } catch (Throwable error) {
      emit(side, "unsupported", "planner", error, preprocessed, List.of());
      return;
    }
    emit(
        side,
        "planned",
        "planner",
        null,
        preprocessed,
        plan.getRowType().getFieldNames());
  }

  private static void emit(
      String side,
      String status,
      String stage,
      Throwable error,
      String preprocessed,
      List<String> outputFields) {
    final String message;
    if (error == null) {
      message = "";
    } else {
      final String detail = error.getMessage();
      message = error.getClass().getName() + (detail == null ? "" : ": " + detail);
    }
    System.out.println(
        side + "\t" + status + "\t" + stage + "\t"
            + base64(message) + "\t" + base64(preprocessed == null ? "" : preprocessed)
            + "\t" + base64(String.join("\u0000", outputFields)));
  }

  private static String base64(String value) {
    return Base64.getEncoder().encodeToString(value.getBytes(StandardCharsets.UTF_8));
  }
}
