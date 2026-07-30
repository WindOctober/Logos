package dev.logos.calcite;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

final class CalciteIrCliIntegrityTest {
  @TempDir
  Path tempDir;

  @Test
  void transportsEverySupportedCreateTableConstraintSeparately() throws Exception {
    String schema = """
        create table tenant_scope (
          tenant_id integer,
          region integer,
          alias text,
          constraint tenant_scope_pk primary key (tenant_id, region),
          constraint tenant_scope_alias unique (alias, region)
        );
        create table child_row (
          tenant_id integer not null,
          region integer,
          id integer,
          note text,
          email text,
          active boolean,
          kind integer,
          parent_category_id integer,
          constraint child_row_pk primary key (id, tenant_id),
          constraint child_row_note unique (note, tenant_id),
          constraint child_row_fk foreign key (tenant_id, region)
            references tenant_scope (tenant_id, region) match simple
            on delete cascade on update cascade,
          constraint child_row_check check (active or note is null)
        );
        create unique index child_row_email_active_idx on child_row
          (lower((email)::text) varchar_pattern_ops, id desc)
          where (active and (kind = any (array[3, 4])));
        create unique index child_row_parent_note_idx on child_row
          (coalesce(parent_category_id, '-1'::integer), note);
        """;

    String output = runCli(schema, "select tenant_id, id from child_row;");

    assertTrue(output.contains("\"notNull\":[\"tenant_id\",\"region\"]"));
    assertTrue(output.contains("\"primaryKey\":[\"tenant_id\",\"region\"]"));
    assertTrue(output.contains(
        "\"unique\":[{\"name\":\"tenant_scope_alias\","
            + "\"columns\":[\"alias\",\"region\"]}]"));
    assertTrue(output.contains("\"primaryKey\":[\"id\",\"tenant_id\"]"));
    assertTrue(output.contains(
        "\"name\":\"child_row_fk\",\"columns\":[\"tenant_id\",\"region\"],"
            + "\"referencedTable\":\"tenant_scope\","
            + "\"referencedColumns\":[\"tenant_id\",\"region\"],"
            + "\"matchType\":\"simple\","
            + "\"referentialActions\":\"ON DELETE CASCADE ON UPDATE CASCADE\""));
    assertTrue(output.contains(
        "\"checks\":[{\"name\":\"child_row_check\","
            + "\"expression\":\"active or note is null\"}]"));
    assertTrue(output.contains(
        "\"name\":\"child_row_email_active_idx\","
            + "\"terms\":[\"lower((email)::text) varchar_pattern_ops\",\"id desc\"],"
            + "\"predicate\":\"(active and (kind = any (array[3, 4])))\""), output);
    assertTrue(output.contains(
        "\"name\":\"child_row_parent_note_idx\","
            + "\"terms\":[\"coalesce(parent_category_id, '-1'::integer)\",\"note\"]"));
  }

  @Test
  void rejectsMalformedConstraintInsteadOfDroppingIt() {
    IllegalArgumentException error = assertThrows(
        IllegalArgumentException.class,
        () -> runCli(
            "create table broken (id integer, constraint broken_unique unique (missing));",
            "select id from broken;"));

    assertTrue(error.getMessage().contains("UNIQUE for table broken names unknown column missing"));
  }

  @Test
  void rejectsHeterogeneousStringForeignKeyEquality() {
    IllegalArgumentException error = assertThrows(
        IllegalArgumentException.class,
        () -> runCli(
            """
            create table parent_row (id char(4) primary key);
            create table child_row (
              id text,
              constraint child_row_fk foreign key (id) references parent_row(id)
            );
            """,
            "select id from child_row;"));

    assertTrue(
        error.getMessage().contains("FOREIGN KEY equality types are incompatible"),
        error.getMessage());

    IllegalArgumentException widthError = assertThrows(
        IllegalArgumentException.class,
        () -> runCli(
            """
            create table parent_row (id varchar(5) primary key);
            create table child_row (
              id varchar(4),
              constraint child_row_fk foreign key (id) references parent_row(id)
            );
            """,
            "select id from child_row;"));
    assertTrue(
        widthError.getMessage().contains("FOREIGN KEY equality types are incompatible"),
        widthError.getMessage());
  }

  @Test
  void acceptsSupportedForeignKeyAndPatternOperatorTypes() throws Exception {
    String output = runCli(
        """
        create table parent_row (id bigint primary key);
        create table child_row (
          id integer,
          code varchar(16),
          constraint child_row_fk foreign key (id) references parent_row(id)
        );
        create unique index child_row_code_idx on child_row (code varchar_pattern_ops);
        """,
        "select id, code from child_row;");

    assertTrue(output.contains("\"referencedTable\":\"parent_row\""), output);
    assertTrue(output.contains("code varchar_pattern_ops"), output);
  }

  @Test
  void rejectsVarcharPatternOpsForCharacter() {
    IllegalArgumentException error = assertThrows(
        IllegalArgumentException.class,
        () -> runCli(
            """
            create table item (code char(4));
            create unique index item_code_idx on item (code varchar_pattern_ops);
            """,
            "select code from item;"));

    assertTrue(error.getMessage().contains(
        "varchar_pattern_ops does not accept PostgreSQL type char"));

    IllegalArgumentException coalesceError = assertThrows(
        IllegalArgumentException.class,
        () -> runCli(
            """
            create table item (code char(4));
            create unique index item_code_idx on item
              (coalesce(code, code) varchar_pattern_ops);
            """,
            "select code from item;"));
    assertTrue(
        coalesceError.getMessage().contains(
            "varchar_pattern_ops does not accept PostgreSQL type char"),
        coalesceError.getMessage());

    IllegalArgumentException mixedCharacterError = assertThrows(
        IllegalArgumentException.class,
        () -> runCli(
            """
            create table item (fixed_code char(4), raw_code bpchar);
            create unique index item_code_idx on item
              (coalesce(fixed_code, raw_code) varchar_pattern_ops);
            """,
            "select fixed_code from item;"));
    assertTrue(
        mixedCharacterError.getMessage().contains(
            "varchar_pattern_ops does not accept PostgreSQL type bpchar"),
        mixedCharacterError.getMessage());
  }

  private String runCli(String schemaSql, String querySql) throws Exception {
    Path schemaPath = tempDir.resolve("schema.sql");
    Path queryPath = tempDir.resolve("query.sql");
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
}
