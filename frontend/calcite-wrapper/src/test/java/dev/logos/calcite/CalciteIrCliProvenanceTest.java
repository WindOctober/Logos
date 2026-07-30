package dev.logos.calcite;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

final class CalciteIrCliProvenanceTest {
  private static final Pattern SOURCE_TABLE_OCCURRENCE = Pattern.compile(
      "\\\"sourceTable\\\":\\{[^{}]*?\\\"relationOccurrenceId\\\":\\\"([^\\\"]+)\\\"",
      Pattern.DOTALL);
  private static final Pattern COLUMN_ALIAS = Pattern.compile(
      "\\{\\\"outputIndex\\\":(\\d+),\\\"nodeId\\\":\\\"([^\\\"]+)\\\","
          + "\\\"text\\\":\\\"([^\\\"]*(?:\\\\\\\"[^\\\"]*)*)\\\","
          + "\\\"names\\\":\\[\\\"([^\\\"]+)\\\"\\]",
      Pattern.DOTALL);

  @TempDir
  Path tempDir;

  @Test
  void emitsExactOrderedFullAndPartialBaseRelationColumnLineage() throws Exception {
    String schema = "create table base_row (a integer, b integer, c integer);";
    String full = runCli(
        schema,
        "select r.\"x\", r.\"y\", r.\"z\" "
            + "from base_row as r (\"x\", \"y\", \"z\");");
    assertFalse(full.contains("\"error\""), full);
    assertTrue(full.contains("\"relationOccurrenceId\""), full);
    assertTrue(full.contains("\"visibleColumnName\":\"x\""), full);
    assertTrue(full.contains("\"visibleColumnName\":\"y\""), full);
    assertTrue(full.contains("\"visibleColumnName\":\"z\""), full);
    assertEquals(List.of(0, 1, 2), columnAliasOrdinals(full));

    String partial = runCli(
        schema,
        "select r.\"x\", r.b, r.c from base_row as r (\"x\");");
    assertFalse(partial.contains("\"error\""), partial);
    assertEquals(List.of(0), columnAliasOrdinals(partial));
    assertTrue(partial.contains(
        "\"baseColumnName\":\"a\",\"visibleColumnName\":\"x\","
            + "\"generatedFieldName\":\"a\",\"explicitColumnAlias\":true"), partial);
    assertTrue(partial.contains(
        "\"baseColumnName\":\"b\",\"visibleColumnName\":\"b\","
            + "\"generatedFieldName\":\"b\",\"explicitColumnAlias\":false"), partial);
    assertTrue(partial.contains(
        "\"baseColumnName\":\"c\",\"visibleColumnName\":\"c\","
            + "\"generatedFieldName\":\"c\",\"explicitColumnAlias\":false"), partial);
  }

  @Test
  void repeatedScansAndSameTextAliasesKeepDistinctOccurrenceAndSpanBindings() throws Exception {
    String output = runCli(
        "create table base_row (a integer, b integer);",
        "select * from base_row as left_row (x, y) "
            + "join base_row as right_row (x, y) on left_row.x = right_row.x;");
    assertFalse(output.contains("\"error\""), output);

    List<String> occurrences = sourceTableOccurrences(output);
    assertEquals(2, occurrences.size(), output);
    assertNotEquals(occurrences.get(0), occurrences.get(1), output);

    List<AliasBinding> aliases = columnAliases(output);
    assertEquals(4, aliases.size(), output);
    assertEquals(List.of(0, 1, 0, 1), aliases.stream().map(AliasBinding::ordinal).toList());
    assertEquals(4, aliases.stream().map(AliasBinding::nodeId).distinct().count(), output);
    assertEquals(List.of("x", "y", "x", "y"),
        aliases.stream().map(AliasBinding::name).toList(), output);
  }

  @Test
  void nestedSubqueryEmitsClosedOperatorLocalCompositionalCorrespondence() throws Exception {
    String output = runCli(
        "create table base_row (a integer, b integer, c integer);",
        "select outer_row.\"x\" from base_row as outer_row (\"x\", \"y\", \"z\") "
            + "where exists (select inner_row.\"x\" "
            + "from base_row as inner_row (\"x\", \"y\", \"z\") "
            + "where inner_row.\"y\" = outer_row.\"y\");");
    assertFalse(output.contains("\"error\""), output);
    assertTrue(output.contains(
        "\"sourceRelCorrespondence\":{"
            + "\"kind\":\"COMPOSITIONAL_RELATION_CORRESPONDENCE_V1\""), output);
    assertTrue(output.contains("\"generatedType\":\"LogicalFilter\""), output);
    assertTrue(output.contains("\"generatedType\":\"LogicalTableScan\""), output);
    assertTrue(output.contains(
        "\"kind\":\"PASSTHROUGH\",\"generatedFieldName\":\"a\""), output);
    assertTrue(output.contains(
        "\"kind\":\"BASE_COLUMN\",\"generatedFieldName\":\"a\""), output);
    assertEquals(2, sourceTableOccurrences(output).stream().distinct().count(), output);
    List<AliasBinding> crossBlockAliases = columnAliases(output);
    assertEquals(6, crossBlockAliases.size(), output);
    assertEquals(6,
        crossBlockAliases.stream().map(AliasBinding::nodeId).distinct().count(), output);
  }

  @Test
  void normalizedProjectExpressionKeepsAllOrderedInputDependencies() throws Exception {
    String output = runCli(
        "create table base_row (a integer, b integer, c integer);",
        "select outer_row.a from base_row as outer_row "
            + "where outer_row.a in (select cast(coalesce(inner_row.b, inner_row.c) "
            + "as integer) from base_row as inner_row);");
    assertFalse(output.contains("\"error\""), output);
    assertTrue(output.contains("\"generatedType\":\"LogicalProject\""), output);
    assertTrue(output.contains("\"kind\":\"SOURCE_EXPRESSION\""), output);
    assertTrue(output.contains(
        "\"inputs\":[{\"inputOrdinal\":0,\"inputOutputIndex\":1},"
            + "{\"inputOrdinal\":0,\"inputOutputIndex\":2}]"), output);
  }

  @Test
  void malformedOrAmbiguousAliasBindingsFailClosed() throws Exception {
    String tooMany = runCli(
        "create table base_row (a integer, b integer);",
        "select * from base_row as r (x, y, fabricated);");
    assertTrue(tooMany.contains("\"error\""), tooMany);
    assertFalse(tooMany.contains("\"rel\""), tooMany);

    String borrowedQualifier = runCli(
        "create table base_row (a integer, b integer);",
        "select borrowed.x from base_row as actual (x, y);");
    assertTrue(borrowedQualifier.contains("\"error\""), borrowedQualifier);
    assertFalse(borrowedQualifier.contains("\"sourceTable\""), borrowedQualifier);

    String ambiguous = runCli(
        "create table base_row (a integer, b integer);",
        "select x from base_row as left_row (x, y), base_row as right_row (x, y);");
    assertTrue(ambiguous.contains("\"error\""), ambiguous);
    assertFalse(ambiguous.contains("\"sourceRelCorrespondence\""), ambiguous);

    String duplicateAlias = runCli(
        "create table base_row (a integer, b integer);",
        "select * from base_row as duplicated (x, x);");
    assertTrue(duplicateAlias.contains("\"error\""), duplicateAlias);
    assertFalse(duplicateAlias.contains("\"rel\""), duplicateAlias);
  }

  private List<Integer> columnAliasOrdinals(String output) {
    return columnAliases(output).stream().map(AliasBinding::ordinal).toList();
  }

  private List<AliasBinding> columnAliases(String output) {
    List<AliasBinding> result = new ArrayList<>();
    Matcher matcher = COLUMN_ALIAS.matcher(output);
    while (matcher.find()) {
      result.add(new AliasBinding(
          Integer.parseInt(matcher.group(1)), matcher.group(2), matcher.group(4)));
    }
    return result;
  }

  private List<String> sourceTableOccurrences(String output) {
    List<String> result = new ArrayList<>();
    Matcher matcher = SOURCE_TABLE_OCCURRENCE.matcher(output);
    while (matcher.find()) {
      result.add(matcher.group(1));
    }
    return result;
  }

  private String runCli(String schemaSql, String querySql) throws Exception {
    Path schemaPath = tempDir.resolve("schema-" + Math.abs(schemaSql.hashCode()) + ".sql");
    Path queryPath = tempDir.resolve("query-" + Math.abs(querySql.hashCode()) + ".sql");
    Files.writeString(schemaPath, schemaSql, StandardCharsets.UTF_8);
    Files.writeString(queryPath, querySql, StandardCharsets.UTF_8);

    ByteArrayOutputStream captured = new ByteArrayOutputStream();
    synchronized (CalciteIrCli.class) {
      PrintStream original = System.out;
      try (PrintStream replacement = new PrintStream(captured, true, StandardCharsets.UTF_8)) {
        System.setOut(replacement);
        CalciteIrCli.main(new String[] {
            "--schema", schemaPath.toString(),
            "--sql", queryPath.toString()
        });
      } finally {
        System.setOut(original);
      }
    }
    return captured.toString(StandardCharsets.UTF_8);
  }

  private record AliasBinding(int ordinal, String nodeId, String name) {}
}
