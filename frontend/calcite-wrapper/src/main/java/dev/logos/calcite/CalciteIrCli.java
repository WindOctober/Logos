package dev.logos.calcite;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.calcite.config.Lex;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.rel.RelFieldCollation;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.RelRoot;
import org.apache.calcite.rel.RelCollation;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.Filter;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rel.core.Sort;
import org.apache.calcite.rel.core.TableScan;
import org.apache.calcite.rel.core.SetOp;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.impl.AbstractTable;
import org.apache.calcite.sql.SqlCall;
import org.apache.calcite.sql.SqlIdentifier;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlNodeList;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.sql.validate.SqlConformanceEnum;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.Planner;

public final class CalciteIrCli {
  private CalciteIrCli() {}

  public static void main(String[] args) throws Exception {
    Map<String, String> opts = parseArgs(args);
    if (!opts.containsKey("schema") || !opts.containsKey("sql")) {
      usage();
      System.exit(2);
    }

    String schemaSql = Files.readString(Path.of(opts.get("schema")));
    String querySql = Files.readString(Path.of(opts.get("sql")));

    SchemaPlus rootSchema = Frameworks.createRootSchema(true);
    List<TableDef> tables = parseCreateTables(schemaSql);
    for (TableDef table : tables) {
      rootSchema.add(table.name, new StaticTable(table));
    }

    SqlParser.Config parserConfig = SqlParser.config()
        .withLex(Lex.MYSQL_ANSI)
        .withConformance(SqlConformanceEnum.DEFAULT)
        .withCaseSensitive(false);
    FrameworkConfig config = Frameworks.newConfigBuilder()
        .parserConfig(parserConfig)
        .defaultSchema(rootSchema)
        .build();

    List<String> queries = splitQueries(querySql);
    Json out = new Json();
    out.beginObject();
    out.name("schema");
    emitSchema(out, tables);
    out.comma();
    out.name("queries");
    out.beginArray();

    boolean first = true;
    for (String query : queries) {
      if (!first) {
        out.comma();
      }
      first = false;
      emitQuery(config, query, out);
    }

    out.endArray();
    out.endObject();
    System.out.println(out);
  }

  private static void emitQuery(FrameworkConfig config, String query, Json out) {
    out.beginObject();
    out.name("sql").value(query);
    try {
      Planner planner = Frameworks.getPlanner(config);
      SqlNode parsed = planner.parse(query);
      out.comma();
      out.name("sqlAst");
      emitSqlNode(out, parsed);

      SqlNode validated = planner.validate(parsed);
      RelRoot relRoot = planner.rel(validated);
      out.comma();
      out.name("rel");
      emitRelNode(out, relRoot.rel);
      out.comma();
      out.name("relText").value(RelOptUtil.toString(relRoot.rel));
    } catch (Exception e) {
      out.comma();
      out.name("error").value(e.getClass().getName() + ": " + e.getMessage());
    }
    out.endObject();
  }

  private static void emitSchema(Json out, List<TableDef> tables) {
    out.beginArray();
    for (int i = 0; i < tables.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      TableDef table = tables.get(i);
      out.beginObject();
      out.name("name").value(table.name);
      out.comma();
      out.name("columns");
      out.beginArray();
      for (int j = 0; j < table.columns.size(); j++) {
        if (j > 0) {
          out.comma();
        }
        ColumnDef column = table.columns.get(j);
        out.beginObject();
        out.name("name").value(column.name);
        out.comma();
        out.name("type").value(column.type.getName());
        out.endObject();
      }
      out.endArray();
      out.endObject();
    }
    out.endArray();
  }

  private static void emitSqlNode(Json out, SqlNode node) {
    if (node == null) {
      out.nullValue();
      return;
    }

    out.beginObject();
    out.name("kind").value(node.getKind().name());
    out.comma();
    out.name("class").value(node.getClass().getSimpleName());
    out.comma();
    out.name("text").value(node.toString());

    if (node instanceof SqlIdentifier id) {
      out.comma();
      out.name("names");
      out.beginArray();
      for (int i = 0; i < id.names.size(); i++) {
        if (i > 0) {
          out.comma();
        }
        out.value(id.names.get(i));
      }
      out.endArray();
    } else if (node instanceof SqlCall call) {
      out.comma();
      out.name("operator").value(call.getOperator().getName());
      out.comma();
      out.name("operands");
      out.beginArray();
      for (int i = 0; i < call.getOperandList().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        emitSqlNode(out, call.getOperandList().get(i));
      }
      out.endArray();
    } else if (node instanceof SqlNodeList list) {
      out.comma();
      out.name("items");
      out.beginArray();
      for (int i = 0; i < list.size(); i++) {
        if (i > 0) {
          out.comma();
        }
        emitSqlNode(out, list.get(i));
      }
      out.endArray();
    }

    out.endObject();
  }

  private static void emitRelNode(Json out, RelNode rel) {
    out.beginObject();
    out.name("type").value(rel.getRelTypeName());
    out.comma();
    out.name("rowType");
    emitRowType(out, rel.getRowType());

    if (rel instanceof TableScan scan) {
      out.comma();
      out.name("table");
      out.beginArray();
      List<String> qn = scan.getTable().getQualifiedName();
      for (int i = 0; i < qn.size(); i++) {
        if (i > 0) {
          out.comma();
        }
        out.value(qn.get(i));
      }
      out.endArray();
    } else if (rel instanceof Project project) {
      out.comma();
      out.name("projects");
      out.beginArray();
      for (int i = 0; i < project.getProjects().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        out.value(project.getProjects().get(i).toString());
      }
      out.endArray();
    } else if (rel instanceof Filter filter) {
      out.comma();
      out.name("condition").value(filter.getCondition().toString());
    } else if (rel instanceof Join join) {
      out.comma();
      out.name("joinType").value(join.getJoinType().name());
      out.comma();
      out.name("condition").value(join.getCondition().toString());
    } else if (rel instanceof Aggregate aggregate) {
      out.comma();
      out.name("groupSet").value(String.valueOf(aggregate.getGroupSet()));
      out.comma();
      out.name("aggCalls");
      out.beginArray();
      for (int i = 0; i < aggregate.getAggCallList().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        out.value(aggregate.getAggCallList().get(i).toString());
      }
      out.endArray();
    } else if (rel instanceof SetOp setOp) {
      out.comma();
      out.name("setOp").value(setOp.kind.name());
      out.comma();
      out.name("all").value(setOp.all);
    } else if (rel instanceof Sort sort) {
      out.comma();
      out.name("collation");
      emitCollation(out, sort.getCollation());
      if (sort.fetch != null) {
        out.comma();
        out.name("fetch").value(sort.fetch.toString());
      }
      if (sort.offset != null) {
        out.comma();
        out.name("offset").value(sort.offset.toString());
      }
    }

    out.comma();
    out.name("inputs");
    out.beginArray();
    List<RelNode> inputs = rel.getInputs();
    for (int i = 0; i < inputs.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      emitRelNode(out, inputs.get(i));
    }
    out.endArray();
    out.endObject();
  }

  private static void emitRowType(Json out, RelDataType rowType) {
    out.beginArray();
    for (int i = 0; i < rowType.getFieldList().size(); i++) {
      if (i > 0) {
        out.comma();
      }
      var field = rowType.getFieldList().get(i);
      out.beginObject();
      out.name("name").value(field.getName());
      out.comma();
      out.name("type").value(field.getType().getSqlTypeName().getName());
      out.comma();
      out.name("nullable").value(field.getType().isNullable());
      out.endObject();
    }
    out.endArray();
  }

  private static void emitCollation(Json out, RelCollation collation) {
    out.beginArray();
    List<RelFieldCollation> fields = collation.getFieldCollations();
    for (int i = 0; i < fields.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      RelFieldCollation field = fields.get(i);
      out.beginObject();
      out.name("fieldIndex").value(field.getFieldIndex());
      out.comma();
      out.name("direction").value(field.getDirection().name());
      out.endObject();
    }
    out.endArray();
  }

  private static List<TableDef> parseCreateTables(String schemaSql) {
    List<TableDef> tables = new ArrayList<>();
    String identifier = "(?:[A-Za-z_][A-Za-z0-9_]*|\"[^\"]+\"|`[^`]+`)";
    Pattern tableStartPattern = Pattern.compile(
        "(?is)create\\s+table\\s+(?:" + identifier + "\\s*\\.\\s*)?(" + identifier
            + ")\\s*\\(");
    Matcher matcher = tableStartPattern.matcher(schemaSql);
    while (matcher.find()) {
      String tableName = matcher.group(1);
      int bodyStart = matcher.end();
      int bodyEnd = findMatchingParen(schemaSql, bodyStart - 1);
      if (bodyEnd < 0) {
        continue;
      }
      String body = schemaSql.substring(bodyStart, bodyEnd);
      List<ColumnDef> columns = new ArrayList<>();
      for (String part : splitTopLevelCommas(body)) {
        String trimmed = part.trim();
        if (trimmed.isEmpty() || isTableConstraint(trimmed)) {
          continue;
        }
        String[] pieces = trimmed.split("\\s+", 3);
        if (pieces.length < 2) {
          continue;
        }
        columns.add(new ColumnDef(stripIdentifierQuotes(pieces[0]), toSqlTypeName(pieces[1])));
      }
      tables.add(new TableDef(stripIdentifierQuotes(tableName), columns));
      matcher.region(bodyEnd + 1, schemaSql.length());
    }
    return tables;
  }

  private static int findMatchingParen(String text, int openIndex) {
    int depth = 0;
    boolean inSingleQuote = false;
    boolean inDoubleQuote = false;
    for (int i = openIndex; i < text.length(); i++) {
      char c = text.charAt(i);
      if (c == '\'' && !inDoubleQuote) {
        inSingleQuote = !inSingleQuote;
      } else if (c == '"' && !inSingleQuote) {
        inDoubleQuote = !inDoubleQuote;
      } else if (!inSingleQuote && !inDoubleQuote) {
        if (c == '(') {
          depth++;
        } else if (c == ')') {
          depth--;
          if (depth == 0) {
            return i;
          }
        }
      }
    }
    return -1;
  }

  private static List<String> splitTopLevelCommas(String text) {
    List<String> parts = new ArrayList<>();
    int depth = 0;
    int start = 0;
    for (int i = 0; i < text.length(); i++) {
      char c = text.charAt(i);
      if (c == '(') {
        depth++;
      } else if (c == ')') {
        depth--;
      } else if (c == ',' && depth == 0) {
        parts.add(text.substring(start, i));
        start = i + 1;
      }
    }
    parts.add(text.substring(start));
    return parts;
  }

  private static boolean isTableConstraint(String text) {
    String lower = text.toLowerCase(Locale.ROOT);
    return lower.startsWith("primary ")
        || lower.startsWith("foreign ")
        || lower.startsWith("unique ")
        || lower.startsWith("key ")
        || lower.startsWith("index ")
        || lower.startsWith("fulltext ")
        || lower.startsWith("spatial ")
        || lower.startsWith("constraint ")
        || lower.startsWith("check ");
  }

  private static SqlTypeName toSqlTypeName(String rawType) {
    String type = rawType.toUpperCase(Locale.ROOT);
    if (type.startsWith("VARCHAR") || type.startsWith("CHAR") || type.startsWith("TEXT")
        || type.startsWith("STRING")) {
      return SqlTypeName.VARCHAR;
    }
    if (type.startsWith("BIGINT")) {
      return SqlTypeName.BIGINT;
    }
    if (type.startsWith("INT") || type.startsWith("INTEGER") || type.startsWith("SMALLINT")
        || type.startsWith("TINYINT")) {
      return SqlTypeName.INTEGER;
    }
    if (type.startsWith("DECIMAL") || type.startsWith("NUMERIC")) {
      return SqlTypeName.DECIMAL;
    }
    if (type.startsWith("DOUBLE")) {
      return SqlTypeName.DOUBLE;
    }
    if (type.startsWith("FLOAT") || type.startsWith("REAL")) {
      return SqlTypeName.FLOAT;
    }
    if (type.startsWith("BOOL")) {
      return SqlTypeName.BOOLEAN;
    }
    if (type.startsWith("DATE")) {
      return SqlTypeName.DATE;
    }
    if (type.startsWith("TIMESTAMP") || type.startsWith("DATETIME")) {
      return SqlTypeName.TIMESTAMP;
    }
    return SqlTypeName.ANY;
  }

  private static String stripIdentifierQuotes(String name) {
    if ((name.startsWith("\"") && name.endsWith("\""))
        || (name.startsWith("`") && name.endsWith("`"))) {
      return name.substring(1, name.length() - 1);
    }
    return name;
  }

  private static List<String> splitQueries(String sql) {
    List<String> queries = new ArrayList<>();
    int start = 0;
    boolean inSingleQuote = false;
    boolean inDoubleQuote = false;
    for (int i = 0; i < sql.length(); i++) {
      char c = sql.charAt(i);
      if (c == '\'' && !inDoubleQuote) {
        if (inSingleQuote && i + 1 < sql.length() && sql.charAt(i + 1) == '\'') {
          i++;
        } else {
          inSingleQuote = !inSingleQuote;
        }
      } else if (c == '"' && !inSingleQuote) {
        inDoubleQuote = !inDoubleQuote;
      } else if (c == ';' && !inSingleQuote && !inDoubleQuote) {
        addQuery(sql.substring(start, i), queries);
        start = i + 1;
      }
    }
    addQuery(sql.substring(start), queries);
    return queries;
  }

  private static void addQuery(String query, List<String> queries) {
    String trimmed = query.trim();
    if (!trimmed.isEmpty()) {
      queries.add(trimmed);
    }
  }

  private static Map<String, String> parseArgs(String[] args) {
    Map<String, String> opts = new LinkedHashMap<>();
    for (int i = 0; i < args.length; i++) {
      String arg = args[i];
      if (arg.startsWith("--") && i + 1 < args.length) {
        opts.put(arg.substring(2), args[++i]);
      }
    }
    return opts;
  }

  private static void usage() {
    System.err.println("Usage: calcite-ir --schema <schema.sql> --sql <query.sql>");
  }

  private record TableDef(String name, List<ColumnDef> columns) {}

  private record ColumnDef(String name, SqlTypeName type) {}

  private static final class StaticTable extends AbstractTable {
    private final TableDef table;

    private StaticTable(TableDef table) {
      this.table = table;
    }

    @Override
    public RelDataType getRowType(RelDataTypeFactory typeFactory) {
      RelDataTypeFactory.Builder builder = typeFactory.builder();
      for (ColumnDef column : table.columns) {
        builder.add(column.name, typeFactory.createSqlType(column.type)).nullable(true);
      }
      return builder.build();
    }
  }

  private static final class Json {
    private final StringBuilder sb = new StringBuilder();

    Json beginObject() {
      sb.append('{');
      return this;
    }

    Json endObject() {
      sb.append('}');
      return this;
    }

    Json beginArray() {
      sb.append('[');
      return this;
    }

    Json endArray() {
      sb.append(']');
      return this;
    }

    Json name(String name) {
      quote(name);
      sb.append(':');
      return this;
    }

    Json value(String value) {
      quote(value);
      return this;
    }

    Json value(boolean value) {
      sb.append(value);
      return this;
    }

    Json value(int value) {
      sb.append(value);
      return this;
    }

    Json nullValue() {
      sb.append("null");
      return this;
    }

    Json comma() {
      sb.append(',');
      return this;
    }

    private void quote(String value) {
      sb.append('"');
      for (int i = 0; i < value.length(); i++) {
        char c = value.charAt(i);
        switch (c) {
          case '"' -> sb.append("\\\"");
          case '\\' -> sb.append("\\\\");
          case '\b' -> sb.append("\\b");
          case '\f' -> sb.append("\\f");
          case '\n' -> sb.append("\\n");
          case '\r' -> sb.append("\\r");
          case '\t' -> sb.append("\\t");
          default -> {
            if (c < 0x20) {
              sb.append(String.format("\\u%04x", (int) c));
            } else {
              sb.append(c);
            }
          }
        }
      }
      sb.append('"');
    }

    @Override
    public String toString() {
      return sb.toString();
    }
  }
}
