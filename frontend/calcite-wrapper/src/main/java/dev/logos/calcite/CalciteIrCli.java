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

import com.google.common.collect.Range;

import org.apache.calcite.config.Lex;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.rel.RelFieldCollation;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.RelRoot;
import org.apache.calcite.rel.RelCollation;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.Correlate;
import org.apache.calcite.rel.core.CorrelationId;
import org.apache.calcite.rel.core.Filter;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rel.core.Sort;
import org.apache.calcite.rel.core.TableScan;
import org.apache.calcite.rel.core.SetOp;
import org.apache.calcite.rel.core.Values;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.rel.type.RelDataTypeSystemImpl;
import org.apache.calcite.rex.RexCall;
import org.apache.calcite.rex.RexCorrelVariable;
import org.apache.calcite.rex.RexFieldAccess;
import org.apache.calcite.rex.RexFieldCollation;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexLiteral;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexOver;
import org.apache.calcite.rex.RexSubQuery;
import org.apache.calcite.rex.RexWindow;
import org.apache.calcite.rex.RexWindowBound;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.impl.AbstractTable;
import org.apache.calcite.sql.SqlCall;
import org.apache.calcite.sql.SqlIdentifier;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlNodeList;
import org.apache.calcite.sql.SqlSelect;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.sql.validate.SqlConformanceEnum;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.Planner;
import org.apache.calcite.util.Sarg;
import org.apache.calcite.util.TimestampString;

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
        .typeSystem(LOGOS_TYPE_SYSTEM)
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
      emitRelNode(out, relRoot.rel, parsed);
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
        out.name("type").value(column.outputTypeName());
        out.comma();
        out.name("fullType").value(column.fullTypeString());
        out.comma();
        out.name("precision").value(column.precision);
        out.comma();
        out.name("scale").value(column.scale);
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

  private static void emitRelNode(Json out, RelNode rel, SqlNode sourceSql) {
    out.beginObject();
    out.name("type").value(rel.getRelTypeName());
    out.comma();
    out.name("rowType");
    emitRowType(out, rel.getRowType());
    emitCorrelationMetadata(out, rel);

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
      out.comma();
      out.name("projectRex");
      out.beginArray();
      List<SqlNode> sourceProjects = topLevelSelectItems(sourceSql);
      for (int i = 0; i < project.getProjects().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        SqlNode sourceProject = i < sourceProjects.size() ? sourceProjects.get(i) : null;
        emitRexNode(out, project.getProjects().get(i), sourceProject);
      }
      out.endArray();
    } else if (rel instanceof Filter filter) {
      out.comma();
      out.name("condition").value(filter.getCondition().toString());
      out.comma();
      out.name("conditionRex");
      emitRexNode(out, filter.getCondition(), topLevelWhere(sourceSql));
    } else if (rel instanceof Join join) {
      out.comma();
      out.name("joinType").value(join.getJoinType().name());
      out.comma();
      out.name("condition").value(join.getCondition().toString());
      out.comma();
      out.name("conditionRex");
      emitRexNode(out, join.getCondition());
    } else if (rel instanceof Aggregate aggregate) {
      out.comma();
      out.name("groupSet").value(String.valueOf(aggregate.getGroupSet()));
      out.comma();
      out.name("groupSets");
      out.beginArray();
      var groupSets = aggregate.getGroupSets();
      if (groupSets == null) {
        out.value(String.valueOf(aggregate.getGroupSet()));
      } else {
        for (int i = 0; i < groupSets.size(); i++) {
          if (i > 0) {
            out.comma();
          }
          out.value(String.valueOf(groupSets.get(i)));
        }
      }
      out.endArray();
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
      out.comma();
      out.name("aggCallDetails");
      out.beginArray();
      for (int i = 0; i < aggregate.getAggCallList().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        emitAggregateCall(out, aggregate.getAggCallList().get(i));
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
        out.comma();
        out.name("fetchRex");
        emitRexNode(out, sort.fetch);
      }
      if (sort.offset != null) {
        out.comma();
        out.name("offset").value(sort.offset.toString());
        out.comma();
        out.name("offsetRex");
        emitRexNode(out, sort.offset);
      }
    } else if (rel instanceof Values values) {
      out.comma();
      out.name("tuples");
      out.beginArray();
      for (int i = 0; i < values.getTuples().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        out.beginArray();
        var tuple = values.getTuples().get(i);
        for (int j = 0; j < tuple.size(); j++) {
          if (j > 0) {
            out.comma();
          }
          emitRexNode(out, tuple.get(j));
        }
        out.endArray();
      }
      out.endArray();
    }

    out.comma();
    out.name("inputs");
    out.beginArray();
    List<RelNode> inputs = rel.getInputs();
    for (int i = 0; i < inputs.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      emitRelNode(out, inputs.get(i), null);
    }
    out.endArray();
    out.endObject();
  }

  private static void emitCorrelationMetadata(Json out, RelNode rel) {
    if (!rel.getVariablesSet().isEmpty()) {
      out.comma();
      out.name("variablesSet");
      out.beginArray();
      int index = 0;
      for (CorrelationId id : rel.getVariablesSet()) {
        if (index++ > 0) {
          out.comma();
        }
        out.value(id.getName());
      }
      out.endArray();
    }
    if (rel instanceof Correlate correlate) {
      out.comma();
      out.name("correlationId").value(correlate.getCorrelationId().getName());
      out.comma();
      out.name("requiredColumns");
      out.beginArray();
      int index = 0;
      for (int column : correlate.getRequiredColumns()) {
        if (index++ > 0) {
          out.comma();
        }
        out.value(column);
      }
      out.endArray();
    }
  }

  private static void emitRexNode(Json out, RexNode rex) {
    emitRexNode(out, rex, null);
  }

  private static void emitRexNode(Json out, RexNode rex, SqlNode sourceSql) {
    if (rex == null) {
      out.nullValue();
      return;
    }

    out.beginObject();
    out.name("kind").value(rex.getKind().name());
    out.comma();
    out.name("class").value(rex.getClass().getSimpleName());
    out.comma();
    out.name("text").value(rex.toString());
    out.comma();
    out.name("type").value(rex.getType().getSqlTypeName().getName());
    out.comma();
    out.name("nullable").value(rex.getType().isNullable());
    emitTypeMetadata(out, rex.getType());
    if (sourceSql != null) {
      out.comma();
      out.name("sourceSql").value(sourceSql.toString());
    }

    if (rex instanceof RexInputRef inputRef) {
      out.comma();
      out.name("index").value(inputRef.getIndex());
    } else if (rex instanceof RexFieldAccess fieldAccess) {
      out.comma();
      out.name("fieldName").value(fieldAccess.getField().getName());
      out.comma();
      out.name("fieldIndex").value(fieldAccess.getField().getIndex());
      out.comma();
      out.name("referenceExpr");
      emitRexNode(out, fieldAccess.getReferenceExpr());
    } else if (rex instanceof RexCorrelVariable correl) {
      out.comma();
      out.name("correlationId").value(correl.id.getId());
      out.comma();
      out.name("correlationName").value(correl.id.getName());
    } else if (rex instanceof RexLiteral literal) {
      emitRexLiteralFields(out, literal);
    } else if (rex instanceof RexSubQuery subQuery) {
      emitRexCallFields(out, subQuery, sourceSql);
      out.comma();
      out.name("subqueryRel");
      emitRelNode(out, subQuery.rel, null);
    } else if (rex instanceof RexOver over) {
      emitRexCallFields(out, over, sourceSql);
      out.comma();
      out.name("window");
      emitRexWindow(out, over.getWindow());
      out.comma();
      out.name("distinct").value(over.isDistinct());
      out.comma();
      out.name("ignoreNulls").value(over.ignoreNulls());
    } else if (rex instanceof RexCall call) {
      emitRexCallFields(out, call, sourceSql);
    }

    out.endObject();
  }

  private static void emitRexCallFields(Json out, RexCall call, SqlNode sourceSql) {
    out.comma();
    out.name("operator").value(call.getOperator().getName());
    out.comma();
    out.name("opKind").value(call.getOperator().getKind().name());
    out.comma();
    out.name("operands");
    out.beginArray();
    List<SqlNode> sourceOperands = sourceOperands(sourceSql);
    for (int i = 0; i < call.getOperands().size(); i++) {
      if (i > 0) {
        out.comma();
      }
      SqlNode sourceOperand = i < sourceOperands.size() ? sourceOperands.get(i) : null;
      emitRexNode(out, call.getOperands().get(i), sourceOperand);
    }
    out.endArray();
  }

  private static void emitRexWindow(Json out, RexWindow window) {
    out.beginObject();
    out.name("partitionKeys");
    out.beginArray();
    for (int i = 0; i < window.partitionKeys.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      emitRexNode(out, window.partitionKeys.get(i));
    }
    out.endArray();
    out.comma();
    out.name("orderKeys");
    out.beginArray();
    for (int i = 0; i < window.orderKeys.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      emitRexFieldCollation(out, window.orderKeys.get(i));
    }
    out.endArray();
    out.comma();
    out.name("isRows").value(window.isRows());
    out.comma();
    out.name("lowerBound");
    emitRexWindowBound(out, window.getLowerBound());
    out.comma();
    out.name("upperBound");
    emitRexWindowBound(out, window.getUpperBound());
    out.comma();
    out.name("exclude").value(window.getExclude().name());
    out.endObject();
  }

  private static void emitRexFieldCollation(Json out, RexFieldCollation field) {
    out.beginObject();
    out.name("expr");
    emitRexNode(out, field.left);
    out.comma();
    out.name("direction").value(field.getDirection().name());
    out.comma();
    out.name("nullDirection").value(field.getNullDirection().name());
    out.endObject();
  }

  private static void emitRexWindowBound(Json out, RexWindowBound bound) {
    out.beginObject();
    out.name("text").value(bound.toString());
    out.comma();
    out.name("unbounded").value(bound.isUnbounded());
    out.comma();
    out.name("unboundedPreceding").value(bound.isUnboundedPreceding());
    out.comma();
    out.name("unboundedFollowing").value(bound.isUnboundedFollowing());
    out.comma();
    out.name("preceding").value(bound.isPreceding());
    out.comma();
    out.name("following").value(bound.isFollowing());
    out.comma();
    out.name("currentRow").value(bound.isCurrentRow());
    RexNode offset = bound.getOffset();
    if (offset != null) {
      out.comma();
      out.name("offset");
      emitRexNode(out, offset);
    }
    out.endObject();
  }

  private static List<SqlNode> topLevelSelectItems(SqlNode sourceSql) {
    if (!(sourceSql instanceof SqlSelect select)) {
      return List.of();
    }
    SqlNodeList selectList = select.getSelectList();
    if (selectList == null) {
      return List.of();
    }
    List<SqlNode> items = new ArrayList<>();
    for (SqlNode item : selectList) {
      items.add(stripAlias(item));
    }
    return items;
  }

  private static SqlNode stripAlias(SqlNode node) {
    if (node instanceof SqlCall call && call.getKind().name().equals("AS")
        && !call.getOperandList().isEmpty()) {
      return call.getOperandList().get(0);
    }
    return node;
  }

  private static SqlNode topLevelWhere(SqlNode sourceSql) {
    if (sourceSql instanceof SqlSelect select) {
      return select.getWhere();
    }
    return null;
  }

  private static List<SqlNode> sourceOperands(SqlNode sourceSql) {
    if (!(sourceSql instanceof SqlCall call)) {
      return List.of();
    }
    return call.getOperandList();
  }

  private static void emitRexLiteralFields(Json out, RexLiteral literal) {
    out.comma();
    out.name("literalTypeName").value(literal.getTypeName().getName());
    out.comma();
    out.name("literalValue").value(nullableToString(literal.getValue()));
    out.comma();
    out.name("literalValue2").value(nullableToString(literal.getValue2()));
    String valueAsString = literalValueAsString(literal);
    if (valueAsString != null) {
      out.comma();
      out.name("literalValueAsString").value(valueAsString);
    }

    String timestampLiteral = timestampLiteralValue(literal);
    if (timestampLiteral != null) {
      out.comma();
      out.name("timestampLiteral").value(timestampLiteral);
    }

    if (literal.getTypeName().getName().startsWith("INTERVAL")) {
      out.comma();
      out.name("intervalTypeName").value(literal.getTypeName().getName());
      if (valueAsString != null) {
        out.comma();
        out.name("intervalLiteral").value(valueAsString);
      }
      out.comma();
      out.name("intervalInternalValue").value(nullableToString(literal.getValue()));
      String unit = intervalUnit(literal.getTypeName());
      if (unit != null) {
        out.comma();
        out.name("intervalUnit").value(unit);
      }
    }

    Object value = literal.getValue();
    if (value instanceof Sarg<?> sarg) {
      out.comma();
      out.name("sarg");
      emitSarg(out, sarg);
    }
  }

  private static void emitSarg(Json out, Sarg<?> sarg) {
    out.beginObject();
    out.name("text").value(sarg.toString());
    out.comma();
    out.name("nullAs").value(sarg.nullAs.name());
    out.comma();
    out.name("pointCount").value(sarg.pointCount);
    out.comma();
    out.name("isAll").value(sarg.isAll());
    out.comma();
    out.name("isNone").value(sarg.isNone());
    out.comma();
    out.name("isPoints").value(sarg.isPoints());
    out.comma();
    out.name("isComplementedPoints").value(sarg.isComplementedPoints());
    out.comma();
    out.name("ranges");
    out.beginArray();
    int index = 0;
    for (Range<?> range : sarg.rangeSet.asRanges()) {
      if (index++ > 0) {
        out.comma();
      }
      emitRange(out, range);
    }
    out.endArray();
    out.endObject();
  }

  private static void emitRange(Json out, Range<?> range) {
    out.beginObject();
    out.name("text").value(range.toString());
    out.comma();
    out.name("hasLowerBound").value(range.hasLowerBound());
    if (range.hasLowerBound()) {
      out.comma();
      out.name("lower").value(String.valueOf(range.lowerEndpoint()));
      out.comma();
      out.name("lowerBoundType").value(range.lowerBoundType().name());
    }
    out.comma();
    out.name("hasUpperBound").value(range.hasUpperBound());
    if (range.hasUpperBound()) {
      out.comma();
      out.name("upper").value(String.valueOf(range.upperEndpoint()));
      out.comma();
      out.name("upperBoundType").value(range.upperBoundType().name());
    }
    out.endObject();
  }

  private static String literalValueAsString(RexLiteral literal) {
    try {
      return literal.getValueAs(String.class);
    } catch (RuntimeException | AssertionError e) {
      return null;
    }
  }

  private static String timestampLiteralValue(RexLiteral literal) {
    SqlTypeName typeName = literal.getTypeName();
    if (typeName != SqlTypeName.TIMESTAMP && typeName != SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE) {
      return null;
    }
    try {
      TimestampString value = literal.getValueAs(TimestampString.class);
      return value == null ? null : value.toString(literal.getType().getPrecision());
    } catch (RuntimeException | AssertionError e) {
      return null;
    }
  }

  private static String intervalUnit(SqlTypeName typeName) {
    String name = typeName.getName();
    if (!name.startsWith("INTERVAL_")) {
      return null;
    }
    return name.substring("INTERVAL_".length());
  }

  private static String nullableToString(Object value) {
    return value == null ? "null" : value.toString();
  }

  private static void emitAggregateCall(Json out, org.apache.calcite.rel.core.AggregateCall call) {
    out.beginObject();
    out.name("text").value(call.toString());
    out.comma();
    out.name("function").value(call.getAggregation().getName());
    out.comma();
    out.name("kind").value(call.getAggregation().getKind().name());
    out.comma();
    out.name("distinct").value(call.isDistinct());
    out.comma();
    out.name("approximate").value(call.isApproximate());
    out.comma();
    out.name("ignoreNulls").value(call.ignoreNulls());
    out.comma();
    out.name("filterArg").value(call.filterArg);
    out.comma();
    out.name("argList");
    out.beginArray();
    for (int i = 0; i < call.getArgList().size(); i++) {
      if (i > 0) {
        out.comma();
      }
      out.value(call.getArgList().get(i));
    }
    out.endArray();
    if (call.distinctKeys != null) {
      out.comma();
      out.name("distinctKeys");
      out.beginArray();
      int index = 0;
      for (int key : call.distinctKeys) {
        if (index++ > 0) {
          out.comma();
        }
        out.value(key);
      }
      out.endArray();
    }
    if (call.getCollation() != null) {
      out.comma();
      out.name("collation");
      emitCollation(out, call.getCollation());
    }
    if (call.getType() != null) {
      out.comma();
      out.name("type").value(call.getType().getSqlTypeName().getName());
      emitTypeMetadata(out, call.getType());
    }
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
      emitTypeMetadata(out, field.getType());
      out.endObject();
    }
    out.endArray();
  }

  private static void emitTypeMetadata(Json out, RelDataType type) {
    out.comma();
    out.name("fullType").value(type.getFullTypeString());
    out.comma();
    out.name("precision").value(type.getPrecision());
    out.comma();
    out.name("scale").value(type.getScale());
    if (type.getCharset() != null) {
      out.comma();
      out.name("charset").value(type.getCharset().name());
    }
    if (type.getCollation() != null) {
      out.comma();
      out.name("typeCollation").value(type.getCollation().toString());
    }
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
      out.comma();
      out.name("nullDirection").value(field.nullDirection.name());
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
        columns.add(ColumnDef.parse(stripIdentifierQuotes(pieces[0]), columnTypeDeclaration(trimmed)));
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

  private static String columnTypeDeclaration(String columnDeclaration) {
    String[] pieces = columnDeclaration.trim().split("\\s+", 2);
    if (pieces.length < 2) {
      return "";
    }
    return pieces[1];
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
    if (type.startsWith("DOUBLE") || type.startsWith("FLOAT8")) {
      return SqlTypeName.DOUBLE;
    }
    if (type.startsWith("REAL") || type.startsWith("FLOAT4")) {
      return SqlTypeName.FLOAT;
    }
    if (type.startsWith("FLOAT")) {
      int precision = parseTypePrecision(rawType);
      if (precision == RelDataType.PRECISION_NOT_SPECIFIED) {
        return SqlTypeName.DOUBLE;
      }
      if (precision >= 1 && precision <= 24) {
        return SqlTypeName.FLOAT;
      }
      if (precision <= 53) {
        return SqlTypeName.DOUBLE;
      }
      throw new IllegalArgumentException("FLOAT precision must be between 1 and 53");
    }
    if (type.startsWith("BOOL")) {
      return SqlTypeName.BOOLEAN;
    }
    if (type.startsWith("DATE")) {
      return SqlTypeName.DATE;
    }
    if (isTimestampWithTimeZone(rawType)) {
      return SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE;
    }
    if (type.startsWith("TIMESTAMP") || type.startsWith("TIMESTAMPTZ")
        || type.startsWith("TIMESTAMPZ") || type.startsWith("DATETIME")) {
      return SqlTypeName.TIMESTAMP;
    }
    if (type.startsWith("TIME")) {
      return SqlTypeName.TIME;
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

  private record ColumnDef(
      String name, SqlTypeName type, int precision, int scale, boolean timestampWithTimeZone) {
    static ColumnDef parse(String name, String rawType) {
      boolean timestampWithTimeZone = isTimestampWithTimeZone(rawType);
      int precision = parseTypePrecision(rawType);
      SqlTypeName type = toSqlTypeName(rawType);
      if (type == SqlTypeName.FLOAT || type == SqlTypeName.DOUBLE) {
        precision = RelDataType.PRECISION_NOT_SPECIFIED;
      }
      if ((type == SqlTypeName.TIMESTAMP || type == SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE)
          && precision == RelDataType.PRECISION_NOT_SPECIFIED) {
        precision = 6;
      }
      if ((type == SqlTypeName.TIMESTAMP || type == SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE)
          && precision > 6) {
        throw new IllegalArgumentException("TIMESTAMP precision must be between 0 and 6");
      }
      return new ColumnDef(
          name,
          type,
          precision,
          parseTypeScale(rawType),
          timestampWithTimeZone);
    }

    String outputTypeName() {
      if (timestampWithTimeZone) {
        return "TIMESTAMP_WITH_TIME_ZONE";
      }
      return type.getName();
    }

    String fullTypeString() {
      if (timestampWithTimeZone) {
        return appendPrecision("TIMESTAMP_WITH_TIME_ZONE");
      }
      return appendPrecision(type.getName());
    }

    private String appendPrecision(String typeName) {
      if (precision >= 0 && scale >= 0) {
        return typeName + "(" + precision + ", " + scale + ")";
      }
      if (precision >= 0) {
        return typeName + "(" + precision + ")";
      }
      return typeName;
    }
  }

  private static boolean isTimestampWithTimeZone(String rawType) {
    String type = rawType.toUpperCase(Locale.ROOT);
    return type.startsWith("TIMESTAMPTZ")
        || type.startsWith("TIMESTAMPZ")
        || (type.startsWith("TIMESTAMP")
            && (type.contains("WITH TIME ZONE") || type.contains("WITH LOCAL TIME ZONE")));
  }

  private static int parseTypePrecision(String rawType) {
    List<Integer> args = parseTypeNumericArguments(rawType);
    return args.isEmpty() ? RelDataType.PRECISION_NOT_SPECIFIED : args.get(0);
  }

  private static int parseTypeScale(String rawType) {
    List<Integer> args = parseTypeNumericArguments(rawType);
    return args.size() < 2 ? RelDataType.SCALE_NOT_SPECIFIED : args.get(1);
  }

  private static List<Integer> parseTypeNumericArguments(String rawType) {
    int start = rawType.indexOf('(');
    int end = rawType.indexOf(')', start + 1);
    if (start < 0 || end < 0) {
      return List.of();
    }
    List<Integer> values = new ArrayList<>();
    for (String part : rawType.substring(start + 1, end).split(",")) {
      try {
        values.add(Integer.parseInt(part.trim()));
      } catch (NumberFormatException ignored) {
        return List.of();
      }
    }
    return values;
  }

  private static final class StaticTable extends AbstractTable {
    private final TableDef table;

    private StaticTable(TableDef table) {
      this.table = table;
    }

    @Override
    public RelDataType getRowType(RelDataTypeFactory typeFactory) {
      RelDataTypeFactory.Builder builder = typeFactory.builder();
      for (ColumnDef column : table.columns) {
        RelDataType ty;
        if (column.precision >= 0 && column.scale >= 0) {
          ty = typeFactory.createSqlType(column.type, column.precision, column.scale);
        } else if (column.precision >= 0) {
          ty = typeFactory.createSqlType(column.type, column.precision);
        } else {
          ty = typeFactory.createSqlType(column.type);
        }
        builder.add(column.name, ty).nullable(true);
      }
      return builder.build();
    }
  }

  private static final RelDataTypeSystemImpl LOGOS_TYPE_SYSTEM =
      new RelDataTypeSystemImpl() {
        @Override public int getMaxPrecision(SqlTypeName typeName) {
          if (typeName == SqlTypeName.TIMESTAMP
              || typeName == SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE) {
            return 6;
          }
          return super.getMaxPrecision(typeName);
        }

        @Override public int getDefaultPrecision(SqlTypeName typeName) {
          if (typeName == SqlTypeName.TIMESTAMP
              || typeName == SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE) {
            return 6;
          }
          return super.getDefaultPrecision(typeName);
        }
      };

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
