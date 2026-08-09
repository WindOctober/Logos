package dev.logos.calcite;

import java.math.BigDecimal;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.calcite.avatica.util.Casing;
import org.apache.calcite.avatica.util.Quoting;
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
import org.apache.calcite.sql.SqlJoin;
import org.apache.calcite.sql.SqlLiteral;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlNodeList;
import org.apache.calcite.sql.SqlOrderBy;
import org.apache.calcite.sql.SqlSelect;
import org.apache.calcite.sql.SqlSetOperator;
import org.apache.calcite.sql.SqlWith;
import org.apache.calcite.sql.SqlWithItem;
import org.apache.calcite.sql.SqlWindow;
import org.apache.calcite.sql.parser.SqlParseException;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.parser.SqlParserPos;
import org.apache.calcite.sql.fun.SqlCase;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.sql.validate.SqlConformanceEnum;
import org.apache.calcite.sql2rel.SqlToRelConverter;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.Planner;
import org.apache.calcite.util.DateString;
import org.apache.calcite.util.TimeString;
import org.apache.calcite.util.TimestampString;

public final class CalciteIrCli {
  /**
   * Calcite reserves these words even though PostgreSQL accepts them as bare,
   * lowercase identifiers (RETURNS is non-reserved and ONE is not a keyword).
   * Keep this allowlist intentionally closed: quoting any broader class after
   * a parse failure could reinterpret actual SQL syntax.
   */
  private static final Set<String> POSTGRES_IDENTIFIER_RETRY_WORDS =
      Set.of("ONE", "RETURNS");

  private static final Set<String> CLI_OPTIONS = Set.of(
      "schema",
      "sql",
      "default-collation",
      "character-classification",
      "locale-provider",
      "server-encoding");

  /**
   * PostgreSQL 17 keyword categories R (reserved) and T (reserved for type or
   * function names). PostgreSQL rejects these spellings as bare schema-object
   * identifiers, while quoted identifiers retain their ordinary meaning.
   */
  private static final Set<String> POSTGRES_BARE_SCHEMA_IDENTIFIER_KEYWORDS = Set.of(
      "all", "analyse", "analyze", "and", "any", "array", "as", "asc", "asymmetric",
      "authorization", "binary", "both", "case", "cast", "check", "collate", "collation",
      "column", "concurrently", "constraint", "create", "cross", "current_catalog",
      "current_date", "current_role", "current_schema", "current_time", "current_timestamp",
      "current_user", "default", "deferrable", "desc", "distinct", "do", "else", "end",
      "except", "false", "fetch", "for", "foreign", "freeze", "from", "full", "grant",
      "group", "having", "ilike", "in", "initially", "inner", "intersect", "into", "is",
      "isnull", "join", "lateral", "leading", "left", "like", "limit", "localtime",
      "localtimestamp", "natural", "not", "notnull", "null", "offset", "on", "only", "or",
      "order", "outer", "overlaps", "placing", "primary", "references", "returning", "right",
      "select", "session_user", "similar", "some", "symmetric", "system_user", "table",
      "tablesample", "then", "to", "trailing", "true", "union", "unique", "user", "using",
      "variadic", "verbose", "when", "where", "window", "with");

  /** PostgreSQL base-table system columns participate in FROM-name lookup even
   * though Calcite's catalog row type contains only user-declared fields. */
  private static final Set<String> POSTGRES_SYSTEM_COLUMN_NAMES =
      Set.of("tableoid", "xmin", "cmin", "xmax", "cmax", "ctid");

  private static final String POSTGRES_BOOLEAN_INTEGER_EQUALITY_UNDEFINED_FUNCTION =
      "POSTGRES_BOOLEAN_INTEGER_EQUALITY_UNDEFINED_FUNCTION";
  private static final String POSTGRES_ORDER_BY_ALIAS_EXPRESSION_UNDEFINED_COLUMN =
      "POSTGRES_ORDER_BY_ALIAS_EXPRESSION_UNDEFINED_COLUMN";

  private static final String POSTGRES_UNQUALIFIED_DERIVED_OUTPUT_AMBIGUOUS_COLUMN =
      "POSTGRES_UNQUALIFIED_DERIVED_OUTPUT_AMBIGUOUS_COLUMN";

  private static final String POSTGRES_IN_SUBQUERY_LOST_ORDER_BY =
      "POSTGRES_IN_SUBQUERY_LOST_ORDER_BY";

  private CalciteIrCli() {}

  private static boolean isPostgresSqlWhitespace(int codePoint) {
    return switch (codePoint) {
      case ' ', '\t', '\n', '\r', '\f', 0x0b -> true;
      default -> false;
    };
  }

  private static int skipPostgresSqlWhitespace(String text, int index) {
    while (index < text.length() && isPostgresSqlWhitespace(text.charAt(index))) {
      index++;
    }
    return index;
  }

  private static String trimPostgresSqlWhitespace(String text) {
    int start = skipPostgresSqlWhitespace(text, 0);
    int end = text.length();
    while (end > start && isPostgresSqlWhitespace(text.charAt(end - 1))) {
      end--;
    }
    return start == 0 && end == text.length() ? text : text.substring(start, end);
  }

  /**
   * Reject text characters that PostgreSQL's SQL lexer cannot safely treat as
   * ordinary content or one of its six whitespace characters. This check is
   * deliberately quote- and comment-independent so protected text cannot hide
   * a NUL, control, Unicode separator, or invisible format character.
   */
  private static void validatePostgresSqlText(String sql, String source) {
    for (int index = 0; index < sql.length();) {
      int codePoint = sql.codePointAt(index);
      if (codePoint == 0) {
        throw new IllegalArgumentException(
            "PostgreSQL " + source + " SQL text must not contain NUL");
      }
      if (!isPostgresSqlWhitespace(codePoint)
          && (Character.isISOControl(codePoint)
              || Character.isWhitespace(codePoint)
              || Character.isSpaceChar(codePoint)
              || Character.getType(codePoint) == Character.FORMAT)) {
        throw new IllegalArgumentException(
            "unsupported PostgreSQL " + source + " SQL text character "
                + String.format(Locale.ROOT, "U+%04X", codePoint));
      }
      index += Character.charCount(codePoint);
    }
  }

  /**
   * PostgreSQL nests block comments, while Calcite ends an outer comment at
   * the first inner terminator and can expose text PostgreSQL still comments
   * out. Reject a real nested opener before Calcite sees the query. Delimiter
   * text inside protected SQL tokens is not syntax.
   */
  private static void rejectNestedPostgresQueryBlockComments(String sql) {
    for (int index = 0; index < sql.length();) {
      char current = sql.charAt(index);
      char next = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;
      if (current == '-' && next == '-') {
        index += 2;
        while (index < sql.length() && sql.charAt(index) != '\n' && sql.charAt(index) != '\r') {
          index++;
        }
        continue;
      }
      if (current == '\'' || current == '"' || current == '`') {
        index = quotedTokenEnd(sql, index, current);
        continue;
      }
      if (current == '[') {
        index = bracketQuotedTokenEnd(sql, index);
        continue;
      }
      if (current == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(sql, index);
        if (delimiterEnd >= 0) {
          String delimiter = sql.substring(index, delimiterEnd);
          int close = sql.indexOf(delimiter, delimiterEnd);
          if (close < 0) {
            throw new IllegalArgumentException("unterminated dollar-quoted SQL string");
          }
          index = close + delimiter.length();
          continue;
        }
      }
      if (current == '/' && next == '*') {
        int end = index + 2;
        boolean closed = false;
        while (end < sql.length()) {
          char block = sql.charAt(end);
          char blockNext = end + 1 < sql.length() ? sql.charAt(end + 1) : 0;
          if (block == '/' && blockNext == '*') {
            throw new IllegalArgumentException(
                "nested PostgreSQL block comments are not supported by the Calcite query frontend");
          }
          if (block == '*' && blockNext == '/') {
            index = end + 2;
            closed = true;
            break;
          }
          end++;
        }
        if (!closed) {
          throw new IllegalArgumentException("unterminated block comment in SQL query file");
        }
        continue;
      }
      index++;
    }
  }

  public static void main(String[] args) throws Exception {
    List<String> sqlPaths = new ArrayList<>();
    Map<String, String> opts = parseArgs(args, sqlPaths);
    if (!opts.containsKey("schema") || sqlPaths.isEmpty()) {
      usage();
      System.exit(2);
    }

    String schemaSql = Files.readString(Path.of(opts.get("schema")));
    validatePostgresSqlText(schemaSql, "schema");
    List<String> queryDocuments = new ArrayList<>();
    for (String sqlPath : sqlPaths) {
      String querySql = Files.readString(Path.of(sqlPath));
      validatePostgresSqlText(querySql, "query");
      rejectNestedPostgresQueryBlockComments(querySql);
      queryDocuments.add(querySql);
    }
    String defaultCollation = canonicalDefaultCollation(
        opts.getOrDefault("default-collation", "unspecified"));
    String characterClassification = canonicalCharacterClassification(
        opts.getOrDefault("character-classification", "unspecified"));
    String localeProvider = canonicalLocaleProvider(
        opts.getOrDefault("locale-provider", "unspecified"));
    String serverEncoding = canonicalServerEncoding(
        opts.getOrDefault("server-encoding", "unspecified"));

    SchemaPlus rootSchema = Frameworks.createRootSchema(true);
    List<TableDef> tables = parseCreateTables(schemaSql);
    for (TableDef table : tables) {
      rootSchema.add(table.name, new StaticTable(table));
    }

    SqlParser.Config parserConfig = SqlParser.config()
        // PostgreSQL folds unquoted identifiers to lower case but preserves
        // quoted spelling and compares quoted identifiers case-sensitively.
        // Lex.MYSQL_ANSI with caseSensitive(false) erased that observable
        // distinction and could resolve a query PostgreSQL rejects.
        .withQuoting(Quoting.DOUBLE_QUOTE)
        .withUnquotedCasing(Casing.TO_LOWER)
        .withQuotedCasing(Casing.UNCHANGED)
        .withConformance(SqlConformanceEnum.DEFAULT)
        .withCaseSensitive(true);
    FrameworkConfig config = Frameworks.newConfigBuilder()
        .parserConfig(parserConfig)
        .typeSystem(LOGOS_TYPE_SYSTEM)
        // PostgreSQL resolves set-operation common types along the source tree;
        // flattening constant UNIONs into Values loses that association.
        .sqlToRelConverterConfig(
            SqlToRelConverter.config()
                .withRelBuilderConfigTransform(
                    builder -> builder.withSimplify(false).withSimplifyValues(false)))
        .defaultSchema(rootSchema)
        .build();

    List<String> queries = new ArrayList<>();
    for (String queryDocument : queryDocuments) {
      queries.addAll(splitQueries(queryDocument));
    }
    Json out = new Json();
    out.beginObject();
    out.name("environment");
    out.beginObject();
    out.name("defaultCollation").value(defaultCollation);
    out.comma();
    out.name("characterClassification").value(characterClassification);
    out.comma();
    out.name("localeProvider").value(localeProvider);
    out.comma();
    out.name("serverEncoding").value(serverEncoding);
    out.endObject();
    out.comma();
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
      emitQuery(config, tables, query, out);
    }

    out.endArray();
    out.endObject();
    System.out.println(out);
  }

  private static void emitQuery(
      FrameworkConfig config, List<TableDef> tables, String query, Json out) {
    Json transaction = new Json();
    try {
      transaction.beginObject();
      transaction.name("sql").value(query);
      ParserSql parserInput = postgresCompatibleParseSql(config, query);
      String parseSql = parserInput.sql();
      SourcePositionMap sourcePositions = parserInput.sourcePositions();
      if (containsExplicitRowInGroupBy(parseSql)) {
        throw new UnsupportedOperationException(
            "PostgreSQL explicit ROW grouping expressions are not representable after "
                + "Calcite erases their distinction from grouping-list syntax");
      }
      // Calcite validation mutates the parsed SqlNode by inserting coercion
      // CASTs. Keep an independently parsed source AST as the authority for
      // distinguishing user-written casts from validator-generated casts.
      Planner sourcePlanner = Frameworks.getPlanner(config);
      SqlNode sourceParsed = sourcePlanner.parse(parseSql);
      if (containsExplicitExpressionCollation(sourceParsed)) {
        throw new UnsupportedOperationException(
            "PostgreSQL expression-level COLLATE is not modeled; refusing to let Calcite "
                + "erase or replace its observable collation semantics");
      }
      String validationSql = calciteValidationSqlWithPostgresPartialRelationAliases(
          sourceParsed, parseSql, tables);
      Planner planner = Frameworks.getPlanner(config);
      SqlNode parsed = planner.parse(validationSql);
      SqlNode validated = planner.validate(parsed);
      RelRoot relRoot = planner.rel(validated);
      RelNode resultRel = relRoot.project();
      boolean syntheticRootOutputProject = resultRel != relRoot.rel;
      if (syntheticRootOutputProject
          && (!(resultRel instanceof Project project) || project.getInput() != relRoot.rel)) {
        throw new IllegalStateException(
            "RelRoot.project() returned an unexpected visible-result shape");
      }
      SourceQueryAnalysisError sourceAnalysisError =
          sourceOrderByAliasExpressionAnalysisError(sourceParsed, resultRel, sourcePositions);
      SourceAmbiguousColumnError sourceAmbiguousColumnError =
          sourceAmbiguousDerivedOutputColumnError(
              sourceParsed, resultRel, sourcePositions);
      if (sourceAnalysisError != null) {
        transaction.comma();
        transaction.name("sourceAnalysisError");
        transaction.beginObject();
        transaction.name("kind").value(sourceAnalysisError.kind());
        transaction.comma();
        transaction.name("sqlState").value(sourceAnalysisError.sqlState());
        transaction.comma();
        transaction.name("queryBlockId").value(sourceAnalysisError.queryBlockId());
        transaction.comma();
        transaction.name("sourceQueryBlockSql")
            .value(sourceAnalysisError.sourceQueryBlockSql());
        transaction.comma();
        transaction.name("sourceOrderItemNodeId")
            .value(sourceAnalysisError.sourceOrderItemNodeId());
        transaction.comma();
        transaction.name("sourceOrderItemSql").value(sourceAnalysisError.sourceOrderItemSql());
        transaction.comma();
        transaction.name("sourceOrderListNodeId")
            .value(sourceAnalysisError.sourceOrderListNodeId());
        transaction.comma();
        transaction.name("sourceOrderListSql").value(sourceAnalysisError.sourceOrderListSql());
        transaction.comma();
        transaction.name("sourceOrderExpressionNodeId")
            .value(sourceAnalysisError.sourceOrderExpressionNodeId());
        transaction.comma();
        transaction.name("sourceOrderExpressionSql")
            .value(sourceAnalysisError.sourceOrderExpressionSql());
        transaction.comma();
        transaction.name("sourceAliasReferenceNodeId")
            .value(sourceAnalysisError.sourceAliasReferenceNodeId());
        transaction.comma();
        transaction.name("sourceAliasReferenceSql")
            .value(sourceAnalysisError.sourceAliasReferenceSql());
        transaction.comma();
        transaction.name("sourceOutputAliasNodeId")
            .value(sourceAnalysisError.sourceOutputAliasNodeId());
        transaction.comma();
        transaction.name("sourceOutputAliasSql")
            .value(sourceAnalysisError.sourceOutputAliasSql());
        transaction.comma();
        transaction.name("sourceFromNodeId")
            .value(sourceAnalysisError.sourceFromNodeId());
        transaction.comma();
        transaction.name("sourceFromSql").value(sourceAnalysisError.sourceFromSql());
        transaction.comma();
        transaction.name("outputAlias").value(sourceAnalysisError.outputAlias());
        transaction.comma();
        transaction.name("inputBindings");
        transaction.beginArray();
        for (int i = 0; i < sourceAnalysisError.inputBindings().size(); i++) {
          if (i > 0) {
            transaction.comma();
          }
          SourceOrderAliasInputBinding binding = sourceAnalysisError.inputBindings().get(i);
          transaction.beginObject();
          transaction.name("sourceRelationNodeId").value(binding.sourceRelationNodeId());
          transaction.comma();
          transaction.name("sourceRelationSql").value(binding.sourceRelationSql());
          transaction.comma();
          transaction.name("sourceTableNodeId").value(binding.sourceTableNodeId());
          transaction.comma();
          transaction.name("sourceTableSql").value(binding.sourceTableSql());
          if (binding.sourceAliasNodeId() != null) {
            transaction.comma();
            transaction.name("sourceAliasNodeId").value(binding.sourceAliasNodeId());
            transaction.comma();
            transaction.name("sourceAliasSql").value(binding.sourceAliasSql());
          }
          transaction.comma();
          transaction.name("baseTable");
          transaction.beginArray();
          for (int j = 0; j < binding.baseTable().size(); j++) {
            if (j > 0) {
              transaction.comma();
            }
            transaction.value(binding.baseTable().get(j));
          }
          transaction.endArray();
          transaction.endObject();
        }
        transaction.endArray();
        transaction.endObject();
      }
      if (sourceAmbiguousColumnError != null) {
        emitSourceAmbiguousColumnError(transaction, sourceAmbiguousColumnError);
      }
      transaction.comma();
      transaction.name("rel");
      emitRelNode(
          transaction, resultRel, SourceContext.root(sourceParsed, sourcePositions),
          syntheticRootOutputProject);
      transaction.endObject();
    } catch (Exception e) {
      // Rel/SQL emission is intentionally transactional. A Calcite accessor
      // can fail after an arbitrarily deep prefix has been written; appending
      // an error member to that prefix would produce malformed JSON and hide
      // the actual frontend exception from the importer.
      transaction = new Json();
      transaction.beginObject();
      transaction.name("sql").value(query);
      transaction.comma();
      transaction.name("error").value(e.getClass().getName() + ": " + e.getMessage());
      transaction.endObject();
    }
    out.rawJson(transaction.toString());
  }

  /**
   * Reject every source expression COLLATE from the independently parsed SQL
   * tree before validation/Rex conversion. Calcite 1.42's RelDataType
   * collation is a Java type-factory default even during PostgreSQL C-locale
   * runs, so neither that metadata nor a simplified Rex node can authorize an
   * explicit PostgreSQL collation override.
   */
  private static boolean containsExplicitExpressionCollation(SqlNode node) {
    if (node == null) {
      return false;
    }
    if (node instanceof SqlCall call) {
      if (call.getKind().name().equalsIgnoreCase("COLLATE")
          || call.getOperator().getName().equalsIgnoreCase("COLLATE")) {
        return true;
      }
      for (SqlNode operand : call.getOperandList()) {
        if (containsExplicitExpressionCollation(operand)) {
          return true;
        }
      }
      return false;
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        if (containsExplicitExpressionCollation(item)) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * PostgreSQL permits a SELECT output alias in ORDER BY only as the complete
   * ordering expression (with ASC/DESC and NULLS decoration). It does not
   * substitute that alias inside CASE, arithmetic, or another expression;
   * an otherwise unresolved name is SQLSTATE 42703. Calcite accepts and
   * expands that non-PostgreSQL syntax, so retain an independent query-level
   * marker after validation has supplied the exact catalog input row types.
   * Emit 42703 only when every source FROM item is a direct base relation,
   * those relations align one-for-one with the generated TableScans, and no
   * input field has the referenced PostgreSQL identifier value. Derived-table,
   * CTE, incomplete, and otherwise ambiguous scopes are rejected without a
   * 42703 marker so Calcite's output-alias substitution cannot fall through as
   * executable PostgreSQL IR.
   */
  private static SourceQueryAnalysisError sourceOrderByAliasExpressionAnalysisError(
      SqlNode root, RelNode rel, SourcePositionMap sourcePositions) {
    SqlNode orderedQuery = root instanceof SqlOrderBy outerOrder ? outerOrder.query : root;
    if (!(root instanceof SqlOrderBy orderBy)
        || orderBy.orderList == null
        || orderBy.orderList.isEmpty()
        || !(sourceQueryBody(root) instanceof SqlSelect select)
        || select.getSelectList() == null) {
      return null;
    }
    Set<String> aliases = new HashSet<>();
    Set<String> duplicateAliases = new HashSet<>();
    Map<String, SqlIdentifier> aliasNodes = new HashMap<>();
    for (SqlNode item : select.getSelectList()) {
      if (!(item instanceof SqlCall call)
          || !call.getKind().name().equals("AS")
          || call.getOperandList().size() < 2
          || !(call.getOperandList().get(1) instanceof SqlIdentifier alias)
          || !alias.isSimple()) {
        continue;
      }
      String name = alias.names.get(0);
      if (!aliases.add(name)) {
        duplicateAliases.add(name);
        aliasNodes.remove(name);
      } else {
        aliasNodes.put(name, alias);
      }
    }
    if (aliases.isEmpty()) {
      return null;
    }
    List<SourceOrderAliasReference> references = new ArrayList<>();
    for (SqlNode orderItem : orderBy.orderList) {
      SqlNode expression = stripOrderByDecoration(orderItem);
      if (expression instanceof SqlIdentifier identifier
          && identifier.isSimple()
          && aliases.contains(identifier.names.get(0))) {
        if (duplicateAliases.contains(identifier.names.get(0))) {
          throw new UnsupportedOperationException(
              "ambiguous duplicate PostgreSQL SELECT alias in ORDER BY: "
                  + identifier.names.get(0));
        }
        continue;
      }
      List<SqlIdentifier> nestedAliases = new ArrayList<>();
      collectNestedOutputAliasReferences(expression, aliases, nestedAliases);
      for (SqlIdentifier matched : nestedAliases) {
        references.add(new SourceOrderAliasReference(
            orderItem, expression, matched, matched.names.get(0)));
      }
    }
    if (references.isEmpty()) {
      return null;
    }
    if (orderedQuery instanceof SqlWith) {
      throw new UnsupportedOperationException(
          "cannot resolve a nested PostgreSQL ORDER BY name against a CTE input scope "
              + "after Calcite output-alias substitution");
    }
    List<AlignedOrderByInput> inputScans = alignedDirectOrderByInputScans(select.getFrom(), rel);
    if (inputScans == null) {
      throw new UnsupportedOperationException(
          "cannot resolve a nested PostgreSQL ORDER BY name against a direct base-table "
              + "input scope after Calcite output-alias substitution");
    }
    for (SourceOrderAliasReference reference : references) {
      if (sourceInputNameMatchCount(select.getFrom(), inputScans, reference.name()) != 0) {
        continue;
      }
      ExactSourceIdentity queryBlockIdentity = sourcePositions == null
          ? null
          : sourcePositions.queryBlockIdentity(select);
      String queryBlockId = queryBlockIdentity == null ? null : queryBlockIdentity.nodeId();
      String orderItemNodeId = sourceNodeId(sourcePositions, reference.orderItem());
      String orderListNodeId = sourceNodeId(sourcePositions, orderBy.orderList);
      String orderExpressionNodeId = sourceNodeId(sourcePositions, reference.expression());
      String aliasReferenceNodeId = sourceNodeId(sourcePositions, reference.reference());
      SqlIdentifier outputAlias = aliasNodes.get(reference.name());
      String outputAliasNodeId = sourceNodeId(sourcePositions, outputAlias);
      String queryBlockSql = queryBlockIdentity == null ? null : queryBlockIdentity.text();
      String orderItemSql = sourceTextAtNode(sourcePositions, reference.orderItem());
      String orderListSql = sourceTextAtNode(sourcePositions, orderBy.orderList);
      String orderExpressionSql = sourceTextAtNode(sourcePositions, reference.expression());
      String aliasReferenceSql = sourceTextAtNode(sourcePositions, reference.reference());
      String outputAliasSql = sourceTextAtNode(sourcePositions, outputAlias);
      List<SqlNode> directRelations = new ArrayList<>();
      for (AlignedOrderByInput input : inputScans) {
        directRelations.add(input.relation());
      }
      ExactSourceIdentity fromIdentity = sourcePositions.coveringIdentity(directRelations);
      String fromNodeId = fromIdentity == null ? null : fromIdentity.nodeId();
      String fromSql = fromIdentity == null ? null : fromIdentity.text();
      if (queryBlockId == null
          || orderItemNodeId == null
          || orderListNodeId == null
          || orderExpressionNodeId == null
          || aliasReferenceNodeId == null
          || outputAlias == null
          || outputAliasNodeId == null
          || queryBlockSql == null
          || orderItemSql == null
          || orderListSql == null
          || orderExpressionSql == null
          || aliasReferenceSql == null
          || outputAliasSql == null
          || fromNodeId == null
          || fromSql == null) {
        throw new UnsupportedOperationException(
            "missing exact source span for a PostgreSQL ORDER BY alias analysis error");
      }
      List<SourceOrderAliasInputBinding> inputBindings = new ArrayList<>();
      for (AlignedOrderByInput input : inputScans) {
        String relationNodeId = sourceNodeId(sourcePositions, input.relation());
        String relationSql = sourceTextAtNode(sourcePositions, input.relation());
        String tableNodeId = sourceNodeId(sourcePositions, input.source().table());
        String tableSql = sourceTextAtNode(sourcePositions, input.source().table());
        String aliasNodeId = sourceNodeId(sourcePositions, input.source().alias());
        String aliasSql = sourceTextAtNode(sourcePositions, input.source().alias());
        if (relationNodeId == null || relationSql == null
            || tableNodeId == null || tableSql == null
            || (input.source().alias() != null && (aliasNodeId == null || aliasSql == null))) {
          throw new UnsupportedOperationException(
              "missing exact direct-input span for a PostgreSQL ORDER BY alias analysis error");
        }
        inputBindings.add(new SourceOrderAliasInputBinding(
            relationNodeId, relationSql, tableNodeId, tableSql,
            aliasNodeId, aliasSql, List.copyOf(input.scan().getTable().getQualifiedName())));
      }
      return new SourceQueryAnalysisError(
          POSTGRES_ORDER_BY_ALIAS_EXPRESSION_UNDEFINED_COLUMN,
          "42703",
          queryBlockId,
          queryBlockSql,
          orderItemNodeId,
          orderItemSql,
          orderListNodeId,
          orderListSql,
          orderExpressionNodeId,
          orderExpressionSql,
          aliasReferenceNodeId,
          aliasReferenceSql,
          outputAliasNodeId,
          outputAliasSql,
          fromNodeId,
          fromSql,
          reference.name(),
          List.copyOf(inputBindings));
    }

    SourceOrderAliasReference reference = references.get(0);
    int inputMatches = sourceInputNameMatchCount(
        select.getFrom(), inputScans, reference.name());
    throw new UnsupportedOperationException(
        inputMatches == 1
            ? "nested PostgreSQL ORDER BY name '" + reference.name()
                + "' resolves as an input column, but Calcite substituted the SELECT output "
                + "alias expression"
            : "nested PostgreSQL ORDER BY name '" + reference.name()
                + "' has an ambiguous input-column scope, but Calcite substituted the SELECT "
                + "output alias expression");
  }

  /**
   * PostgreSQL resolves an unqualified SELECT identifier against every public
   * column of its FROM namespace and reports SQLSTATE 42702 when more than one
   * column has that name. Calcite instead uniquifies duplicate derived-table
   * field names (for example, {@code sal} and {@code sal0}) and can silently
   * bind the source identifier to one arbitrary position.
   *
   * <p>Retain a marker only for one closed shape whose exact source namespace
   * can be reconstructed without trusting those uniquified names: a simple
   * outer SELECT over one aliased derived set operation, where every set arm
   * is a simple unqualified-wildcard SELECT. Each wildcard input is aligned to
   * the corresponding generated TableScan/Join/identity Project, every set
   * arm has the same arity and exact generated types, and the first arm (which
   * defines PostgreSQL's set-output names) contains every reported match. Any
   * qualified reference, explicit projection, column alias list, coercing set
   * arm, non-cross join, or incomplete exact span withholds the marker.</p>
   */
  private static SourceAmbiguousColumnError sourceAmbiguousDerivedOutputColumnError(
      SqlNode root, RelNode rel, SourcePositionMap sourcePositions) {
    if (sourcePositions == null
        || !(root instanceof SqlSelect select)
        || !isSimpleSelectClauseShape(select)
        || select.getSelectList() == null
        || select.getSelectList().size() != 1
        || !(select.getSelectList().get(0) instanceof SqlIdentifier identifier)
        || !identifier.isSimple()
        || identifier.isStar()
        || !(select.getFrom() instanceof SqlCall derivedAlias)
        || !derivedAlias.getKind().name().equals("AS")
        || derivedAlias.getOperandList().size() != 2
        || !(derivedAlias.getOperandList().get(0) instanceof SqlCall sourceSet)
        || !(sourceSet.getOperator() instanceof SqlSetOperator)
        || !(derivedAlias.getOperandList().get(1) instanceof SqlIdentifier relationAlias)
        || !relationAlias.isSimple()
        || !(rel instanceof Project project)
        || !project.getVariablesSet().isEmpty()
        || project.getInputs().size() != 1
        || project.getProjects().size() != 1
        || !(project.getProjects().get(0) instanceof RexInputRef selectedInput)
        || project.getRowType().getFieldCount() != 1
        || !(project.getInput() instanceof SetOp setOp)
        || !sourceSetOperationMatches(setOp, sourceSet)) {
      return null;
    }

    List<SourceDerivedPublicOutput> publicOutputs =
        exactWildcardSetPublicOutputs(sourceSet, setOp, sourcePositions);
    if (publicOutputs == null
        || selectedInput.getIndex() < 0
        || selectedInput.getIndex() >= publicOutputs.size()
        || selectedInput.getIndex() >= setOp.getRowType().getFieldCount()
        || !selectedInput.getType().equals(
            setOp.getRowType().getFieldList().get(selectedInput.getIndex()).getType())
        || !selectedInput.getType().equals(
            project.getRowType().getFieldList().get(0).getType())
        || !project.getRowType().getFieldList().get(0).getName()
            .equals(identifier.names.get(0))) {
      return null;
    }

    List<Integer> matchingIndexes = new ArrayList<>();
    String identifierName = identifier.names.get(0);
    for (int index = 0; index < publicOutputs.size(); index++) {
      if (publicOutputs.get(index).outputName().equals(identifierName)) {
        matchingIndexes.add(index);
      }
    }
    if (matchingIndexes.size() < 2
        || !matchingIndexes.contains(selectedInput.getIndex())) {
      return null;
    }

    ExactSourceIdentity queryBlock = sourcePositions.queryBlockIdentity(select);
    ExactSourceIdentity sourceIdentifier = sourcePositions.exactIdentity(identifier);
    ExactSourceIdentity sourceRelation = sourcePositions.relationIdentity(select.getFrom());
    if (queryBlock == null
        || sourceIdentifier == null
        || sourceRelation == null
        || queryBlock.text().isEmpty()
        || sourceIdentifier.text().isEmpty()
        || sourceRelation.text().isEmpty()) {
      return null;
    }

    List<SourceAmbiguousColumnOutput> matchingOutputs = new ArrayList<>();
    Set<String> matchedOriginNodeIds = new HashSet<>();
    for (int outputIndex : matchingIndexes) {
      SourceDerivedPublicOutput output = publicOutputs.get(outputIndex);
      ExactSourceIdentity outputItem =
          sourcePositions.exactIdentity(output.sourceOutputItem());
      ExactSourceIdentity originRelation =
          sourcePositions.relationIdentity(output.sourceOriginRelation());
      if (outputItem == null
          || originRelation == null
          || outputItem.text().isEmpty()
          || originRelation.text().isEmpty()
          || !matchedOriginNodeIds.add(originRelation.nodeId())) {
        return null;
      }
      matchingOutputs.add(new SourceAmbiguousColumnOutput(
          outputIndex,
          output.outputName(),
          outputItem.nodeId(),
          outputItem.text(),
          originRelation.nodeId(),
          originRelation.text()));
    }

    boolean identifierQuoted;
    try {
      identifierQuoted = sourcePositions.sourceIdentifierComponentQuoted(identifier, 0);
    } catch (UnsupportedOperationException error) {
      return null;
    }
    return new SourceAmbiguousColumnError(
        POSTGRES_UNQUALIFIED_DERIVED_OUTPUT_AMBIGUOUS_COLUMN,
        "42702",
        queryBlock.nodeId(),
        queryBlock.text(),
        sourceIdentifier.nodeId(),
        sourceIdentifier.text(),
        sourceRelation.nodeId(),
        sourceRelation.text(),
        identifierName,
        identifierQuoted,
        matchingOutputs.size(),
        List.copyOf(matchingOutputs));
  }

  /** Reject clauses that could insert relational operators between the exact
   * outer SELECT role and the generated Project/SetOp edge. */
  private static boolean isSimpleSelectClauseShape(SqlSelect select) {
    return select != null
        && !select.isDistinct()
        && select.getFrom() != null
        && select.getWhere() == null
        && select.getHaving() == null
        && select.getQualify() == null
        && select.getOffset() == null
        && select.getFetch() == null
        && !select.hasHints()
        && !hasSourceItems(select.getGroup())
        && !hasSourceItems(select.getWindowList())
        && !hasSourceItems(select.getOrderList());
  }

  /** Derive PostgreSQL set-output names from the exact first arm while using
   * every generated arm to close arity and type consistency. */
  private static List<SourceDerivedPublicOutput> exactWildcardSetPublicOutputs(
      SqlCall sourceSet, SetOp setOp, SourcePositionMap sourcePositions) {
    List<SqlNode> sourceArms = sourceSet.getOperandList();
    if (!sourceSetOperationMatches(setOp, sourceSet)
        || sourceArms.size() < 2
        || sourceArms.size() != setOp.getInputs().size()
        || sourcePositions.declarativeQueryIdentity(sourceSet) == null) {
      return null;
    }
    List<SourceDerivedPublicOutput> firstArm = null;
    for (int armIndex = 0; armIndex < sourceArms.size(); armIndex++) {
      List<SourceDerivedPublicOutput> arm = exactWildcardSelectPublicOutputs(
          stripAlias(sourceArms.get(armIndex)),
          setOp.getInput(armIndex),
          sourcePositions);
      if (arm == null
          || arm.size() != setOp.getRowType().getFieldCount()) {
        return null;
      }
      if (firstArm == null) {
        firstArm = arm;
      }
      if (arm.size() != firstArm.size()) {
        return null;
      }
      for (int outputIndex = 0; outputIndex < arm.size(); outputIndex++) {
        RelDataType armType = arm.get(outputIndex).outputType();
        RelDataType firstType = firstArm.get(outputIndex).outputType();
        RelDataType setType =
            setOp.getRowType().getFieldList().get(outputIndex).getType();
        if (!armType.equals(firstType) || !armType.equals(setType)) {
          return null;
        }
      }
    }
    return firstArm == null ? null : List.copyOf(firstArm);
  }

  /** Return the ordered public outputs of one exact {@code SELECT *}. */
  private static List<SourceDerivedPublicOutput> exactWildcardSelectPublicOutputs(
      SqlNode sourceNode, RelNode rel, SourcePositionMap sourcePositions) {
    if (!(sourceNode instanceof SqlSelect select)
        || !isSimpleSelectClauseShape(select)
        || select.getSelectList() == null
        || select.getSelectList().size() != 1
        || !(select.getSelectList().get(0) instanceof SqlIdentifier wildcard)
        || !wildcard.isStar()
        || wildcard.names.size() != 1
        || !(rel instanceof Project project)
        || !project.getVariablesSet().isEmpty()
        || project.getInputs().size() != 1
        || project.getProjects().size() != project.getInput().getRowType().getFieldCount()
        || project.getRowType().getFieldCount() != project.getProjects().size()
        || sourcePositions.exactIdentity(wildcard) == null
        || sourcePositions.queryBlockIdentity(select) == null) {
      return null;
    }
    for (int index = 0; index < project.getProjects().size(); index++) {
      if (!(project.getProjects().get(index) instanceof RexInputRef inputRef)
          || inputRef.getIndex() != index
          || !inputRef.getType().equals(
              project.getInput().getRowType().getFieldList().get(index).getType())
          || !inputRef.getType().equals(
              project.getRowType().getFieldList().get(index).getType())) {
        return null;
      }
    }
    List<SourceDerivedPublicOutput> relationOutputs =
        exactWildcardRelationOutputs(select.getFrom(), project.getInput(), sourcePositions);
    if (relationOutputs == null
        || relationOutputs.size() != project.getProjects().size()) {
      return null;
    }
    List<SourceDerivedPublicOutput> outputs = new ArrayList<>();
    for (int index = 0; index < relationOutputs.size(); index++) {
      SourceDerivedPublicOutput relationOutput = relationOutputs.get(index);
      RelDataType outputType =
          project.getRowType().getFieldList().get(index).getType();
      if (!relationOutput.outputType().equals(outputType)) {
        return null;
      }
      outputs.add(new SourceDerivedPublicOutput(
          relationOutput.outputName(),
          wildcard,
          relationOutput.sourceOriginRelation(),
          outputType));
    }
    return List.copyOf(outputs);
  }

  /** Align the FROM namespace underlying one unqualified wildcard. Aliased
   * subqueries retain their public alias relation as the exact output origin,
   * so two identically shaped inputs still have distinct source anchors. */
  private static List<SourceDerivedPublicOutput> exactWildcardRelationOutputs(
      SqlNode sourceRelation, RelNode rel, SourcePositionMap sourcePositions) {
    if (sourceRelation == null
        || rel == null
        || sourcePositions.relationIdentity(sourceRelation) == null) {
      return null;
    }
    if (sourceRelation instanceof SqlJoin sourceJoin) {
      if (!sourceJoin.getJoinType().name().equals("COMMA")
          || !sourceJoin.getConditionType().name().equals("NONE")
          || !(rel instanceof Join join)
          || !join.getJoinType().name().equals("INNER")
          || !join.getCondition().isAlwaysTrue()
          || !join.getVariablesSet().isEmpty()
          || join.getInputs().size() != 2) {
        return null;
      }
      List<SourceDerivedPublicOutput> left = exactWildcardRelationOutputs(
          sourceJoin.getLeft(), join.getLeft(), sourcePositions);
      List<SourceDerivedPublicOutput> right = exactWildcardRelationOutputs(
          sourceJoin.getRight(), join.getRight(), sourcePositions);
      if (left == null || right == null
          || left.size() + right.size() != join.getRowType().getFieldCount()) {
        return null;
      }
      List<SourceDerivedPublicOutput> outputs = new ArrayList<>(left.size() + right.size());
      outputs.addAll(left);
      outputs.addAll(right);
      for (int index = 0; index < outputs.size(); index++) {
        if (!outputs.get(index).outputType().equals(
            join.getRowType().getFieldList().get(index).getType())) {
          return null;
        }
      }
      return List.copyOf(outputs);
    }

    SqlNode unaliased = sourceRelation;
    boolean hasAlias = false;
    if (sourceRelation instanceof SqlCall alias
        && alias.getKind().name().equals("AS")) {
      if (alias.getOperandList().size() != 2
          || !(alias.getOperandList().get(1) instanceof SqlIdentifier name)
          || !name.isSimple()) {
        return null;
      }
      unaliased = alias.getOperandList().get(0);
      hasAlias = true;
    }

    if (unaliased instanceof SqlIdentifier) {
      if (!(rel instanceof TableScan scan)
          || directTableSource(sourceRelation, scan) == null
          || !rel.getInputs().isEmpty()) {
        return null;
      }
      List<SourceDerivedPublicOutput> outputs = new ArrayList<>();
      for (var field : scan.getRowType().getFieldList()) {
        outputs.add(new SourceDerivedPublicOutput(
            field.getName(), null, sourceRelation, field.getType()));
      }
      return List.copyOf(outputs);
    }

    if (unaliased instanceof SqlSelect innerSelect && hasAlias) {
      List<SourceDerivedPublicOutput> inner = exactWildcardSelectPublicOutputs(
          innerSelect, rel, sourcePositions);
      if (inner == null) {
        return null;
      }
      List<SourceDerivedPublicOutput> outputs = new ArrayList<>();
      for (SourceDerivedPublicOutput output : inner) {
        outputs.add(new SourceDerivedPublicOutput(
            output.outputName(), null, sourceRelation, output.outputType()));
      }
      return List.copyOf(outputs);
    }
    return null;
  }

  private static void emitSourceAmbiguousColumnError(
      Json out, SourceAmbiguousColumnError error) {
    out.comma();
    out.name("sourceAmbiguousColumnError");
    out.beginObject();
    out.name("kind").value(error.kind());
    out.comma();
    out.name("sqlState").value(error.sqlState());
    out.comma();
    out.name("queryBlockId").value(error.queryBlockId());
    out.comma();
    out.name("sourceQueryBlockSql").value(error.sourceQueryBlockSql());
    out.comma();
    out.name("sourceIdentifierNodeId").value(error.sourceIdentifierNodeId());
    out.comma();
    out.name("sourceIdentifierSql").value(error.sourceIdentifierSql());
    out.comma();
    out.name("sourceRelationNodeId").value(error.sourceRelationNodeId());
    out.comma();
    out.name("sourceRelationSql").value(error.sourceRelationSql());
    out.comma();
    out.name("identifierName").value(error.identifierName());
    out.comma();
    out.name("identifierQuoted").value(error.identifierQuoted());
    out.comma();
    out.name("duplicateCount").value(error.duplicateCount());
    out.comma();
    out.name("matchingOutputs");
    out.beginArray();
    for (int index = 0; index < error.matchingOutputs().size(); index++) {
      if (index > 0) {
        out.comma();
      }
      SourceAmbiguousColumnOutput output = error.matchingOutputs().get(index);
      out.beginObject();
      out.name("outputIndex").value(output.outputIndex());
      out.comma();
      out.name("outputName").value(output.outputName());
      out.comma();
      out.name("sourceOutputItemNodeId").value(output.sourceOutputItemNodeId());
      out.comma();
      out.name("sourceOutputItemSql").value(output.sourceOutputItemSql());
      out.comma();
      out.name("sourceOriginRelationNodeId")
          .value(output.sourceOriginRelationNodeId());
      out.comma();
      out.name("sourceOriginRelationSql").value(output.sourceOriginRelationSql());
      out.endObject();
    }
    out.endArray();
    out.endObject();
  }

  private static List<AlignedOrderByInput> alignedDirectOrderByInputScans(
      SqlNode from, RelNode rel) {
    List<SqlNode> sourceRelations = new ArrayList<>();
    if (!collectDirectOrderByInputRelations(from, sourceRelations)) {
      return null;
    }
    List<TableScan> generatedScans = new ArrayList<>();
    collectRelInputTableScans(rel, generatedScans);
    if (sourceRelations.size() != generatedScans.size()) {
      return null;
    }

    boolean[] used = new boolean[generatedScans.size()];
    List<AlignedOrderByInput> aligned = new ArrayList<>();
    for (SqlNode sourceRelation : sourceRelations) {
      int matched = -1;
      DirectTableSource matchedSource = null;
      for (int i = 0; i < generatedScans.size(); i++) {
        DirectTableSource candidate = !used[i]
            ? directTableSource(sourceRelation, generatedScans.get(i))
            : null;
        if (candidate != null) {
          matched = i;
          matchedSource = candidate;
          break;
        }
      }
      if (matched < 0) {
        return null;
      }
      used[matched] = true;
      aligned.add(new AlignedOrderByInput(
          sourceRelation, matchedSource, generatedScans.get(matched)));
    }
    return aligned;
  }

  private static boolean collectDirectOrderByInputRelations(
      SqlNode node, List<SqlNode> relations) {
    if (node == null) {
      return true;
    }
    if (node instanceof SqlJoin join) {
      return collectDirectOrderByInputRelations(join.getLeft(), relations)
          && collectDirectOrderByInputRelations(join.getRight(), relations);
    }
    if (node instanceof SqlCall alias && alias.getKind().name().equals("AS")) {
      if (alias.getOperandList().size() != 2
          || !(alias.getOperandList().get(0) instanceof SqlIdentifier table)
          || table.isStar()
          || !(alias.getOperandList().get(1) instanceof SqlIdentifier correlation)
          || !correlation.isSimple()) {
        return false;
      }
      relations.add(node);
      return true;
    }
    if (node instanceof SqlIdentifier table && !table.isStar()) {
      relations.add(node);
      return true;
    }
    return false;
  }

  private static void collectRelInputTableScans(RelNode rel, List<TableScan> scans) {
    if (rel instanceof TableScan scan) {
      scans.add(scan);
      return;
    }
    for (RelNode input : rel.getInputs()) {
      collectRelInputTableScans(input, scans);
    }
  }

  private static int sourceInputNameMatchCount(
      SqlNode from, List<AlignedOrderByInput> scans, String name) {
    int matches = 0;
    for (AlignedOrderByInput input : scans) {
      TableScan scan = input.scan();
      if (POSTGRES_SYSTEM_COLUMN_NAMES.contains(name)) {
        matches++;
      }
      for (var field : scan.getRowType().getFieldList()) {
        if (field.getName().equals(name)) {
          matches++;
        }
      }
    }
    return matches + sourceWholeRowNameMatchCount(from, name);
  }

  private static int sourceWholeRowNameMatchCount(SqlNode node, String name) {
    if (node == null) {
      return 0;
    }
    if (node instanceof SqlJoin join) {
      return sourceWholeRowNameMatchCount(join.getLeft(), name)
          + sourceWholeRowNameMatchCount(join.getRight(), name);
    }
    if (node instanceof SqlCall alias && alias.getKind().name().equals("AS")
        && alias.getOperandList().size() == 2
        && alias.getOperandList().get(1) instanceof SqlIdentifier correlation
        && correlation.isSimple()) {
      return correlation.names.get(0).equals(name) ? 1 : 0;
    }
    if (node instanceof SqlIdentifier table && !table.names.isEmpty()) {
      return table.names.get(table.names.size() - 1).equals(name) ? 1 : 0;
    }
    return 0;
  }

  private static SqlNode stripOrderByDecoration(SqlNode node) {
    SqlNode current = node;
    while (current instanceof SqlCall call
        && call.getOperandList().size() == 1
        && (call.getKind().name().equals("DESCENDING")
            || call.getKind().name().equals("NULLS_FIRST")
            || call.getKind().name().equals("NULLS_LAST"))) {
      current = call.getOperandList().get(0);
    }
    return current;
  }

  private static void collectNestedOutputAliasReferences(
      SqlNode node, Set<String> aliases, List<SqlIdentifier> matches) {
    if (node instanceof SqlIdentifier identifier) {
      if (identifier.isSimple()
          && aliases.contains(identifier.names.get(0))
          && matches.stream().noneMatch(existing ->
              existing.names.get(0).equals(identifier.names.get(0)))) {
        matches.add(identifier);
      }
      return;
    }
    if (node instanceof SqlSelect || node instanceof SqlOrderBy || node instanceof SqlWith) {
      return;
    }
    if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        collectNestedOutputAliasReferences(operand, aliases, matches);
      }
    } else if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectNestedOutputAliasReferences(item, aliases, matches);
      }
    }
  }

  /**
   * Retry only Calcite-reserved identifiers whose quoted spelling has exactly
   * the same PostgreSQL meaning as the original lowercase bare identifier.
   * The returned text is parser input only; JSON continues to retain the
   * byte-for-byte original statement in its {@code sql} field.
   */
  private static ParserSql postgresCompatibleParseSql(FrameworkConfig config, String query)
      throws SqlParseException {
    SqlParser.Config parserConfig = config.getParserConfig();
    var metadata = SqlParser.create("", parserConfig).getMetadata();
    // PostgreSQL treats vertical tab as ordinary SQL whitespace, but
    // Calcite's generated lexer rejects it outside protected tokens. Replace
    // only lexical whitespace in the private parser copy; quoted content,
    // comments, JSON, and downstream statement authority retain `query`.
    SourcePositionMap sourcePositions =
        SourcePositionMap.identity(query).withCalciteWhitespace();
    String parseSql = sourcePositions.parserSql();
    SqlParseException last = null;
    for (int attempt = 0; attempt <= POSTGRES_IDENTIFIER_RETRY_WORDS.size() * 16; attempt++) {
      try {
        // Use the same Planner entry point as the ordinary wrapper path so a
        // non-eligible failure (notably PostgreSQL DISTINCT ON) retains the
        // exact Calcite SqlParseException class and message.
        Frameworks.getPlanner(config).parse(parseSql);
        return new ParserSql(parseSql, sourcePositions);
      } catch (SqlParseException error) {
        last = error;
        boolean identifierExpected = error.getExpectedTokenNames().stream()
            .anyMatch(token -> token.contains("IDENTIFIER"));
        IdentifierSpan span = identifierExpected
            ? bareIdentifierAt(parseSql, error.getPos())
            : null;
        if (span == null) {
          throw error;
        }
        String word = parseSql.substring(span.start(), span.end());
        String upper = word.toUpperCase(Locale.ROOT);
        if (!POSTGRES_IDENTIFIER_RETRY_WORDS.contains(upper)
            || !metadata.isReservedWord(upper)
            || !word.equals(word.toLowerCase(Locale.ROOT))) {
          throw error;
        }
        sourcePositions = sourcePositions.quoteBareIdentifier(span);
        parseSql = sourcePositions.parserSql();
      }
    }
    throw last;
  }

  /**
   * Calcite requires a base-table relation alias column list to have exactly
   * the table degree, while PostgreSQL permits an ordered proper prefix.  Pad
   * only Calcite's private validation copy with the inherited schema names.
   * The independently parsed source AST and its position map continue to
   * reference the untouched statement, so inserted names can never become
   * source provenance.  Ambiguous inherited namespaces fail closed.
   */
  private static String calciteValidationSqlWithPostgresPartialRelationAliases(
      SqlNode sourceRoot, String parserSql, List<TableDef> tables) {
    List<ParserInsertion> insertions = new ArrayList<>();
    collectPartialBaseRelationAliasInsertions(
        sourceRoot, parserSql, tables, new IdentityHashMap<>(), insertions);
    if (insertions.isEmpty()) {
      return parserSql;
    }
    insertions.sort((left, right) -> Integer.compare(right.offset(), left.offset()));
    StringBuilder validationSql = new StringBuilder(parserSql);
    Integer previous = null;
    for (ParserInsertion insertion : insertions) {
      if (insertion.offset() < 0
          || insertion.offset() > validationSql.length()
          || previous != null && previous.equals(insertion.offset())) {
        throw new UnsupportedOperationException(
            "partial base relation alias lists have ambiguous parser insertion points");
      }
      validationSql.insert(insertion.offset(), insertion.text());
      previous = insertion.offset();
    }
    return validationSql.toString();
  }

  private static void collectPartialBaseRelationAliasInsertions(
      SqlNode node,
      String parserSql,
      List<TableDef> tables,
      IdentityHashMap<SqlNode, Boolean> visited,
      List<ParserInsertion> insertions) {
    if (node == null || visited.put(node, Boolean.TRUE) != null) {
      return;
    }
    if (node instanceof SqlCall call) {
      if (call.getKind().name().equals("AS")
          && call.getOperandList().size() > 2
          && call.getOperandList().get(0) instanceof SqlIdentifier table
          && call.getOperandList().get(1) instanceof SqlIdentifier alias
          && alias.isSimple()) {
        TableDef definition = uniqueTableDefinition(table, tables);
        if (definition != null) {
          int explicitCount = call.getOperandList().size() - 2;
          if (explicitCount > definition.columns().size()) {
            throw new UnsupportedOperationException(
                "base relation alias column list is wider than its source table");
          }
          if (explicitCount < definition.columns().size()) {
            Set<String> visibleNames = new HashSet<>();
            for (int i = 2; i < call.getOperandList().size(); i++) {
              if (!(call.getOperandList().get(i) instanceof SqlIdentifier columnAlias)
                  || !columnAlias.isSimple()
                  || !visibleNames.add(columnAlias.names.get(0))) {
                throw new UnsupportedOperationException(
                    "partial base relation alias column list is malformed or ambiguous");
              }
            }
            StringBuilder inherited = new StringBuilder();
            for (int i = explicitCount; i < definition.columns().size(); i++) {
              String name = definition.columns().get(i).name();
              if (!visibleNames.add(name)) {
                throw new UnsupportedOperationException(
                    "partial base relation alias list collides with an inherited column name");
              }
              inherited.append(", ").append(quoteCalciteIdentifier(name));
            }
            SqlNode lastAlias = call.getOperandList().get(call.getOperandList().size() - 1);
            int insertion = partialAliasListClosingParen(parserSql, lastAlias.getParserPosition());
            if (insertion < 0) {
              throw new UnsupportedOperationException(
                  "partial base relation alias list has no exact closing delimiter");
            }
            insertions.add(new ParserInsertion(insertion, inherited.toString()));
          }
        }
      }
      for (SqlNode operand : call.getOperandList()) {
        collectPartialBaseRelationAliasInsertions(
            operand, parserSql, tables, visited, insertions);
      }
    } else if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectPartialBaseRelationAliasInsertions(
            item, parserSql, tables, visited, insertions);
      }
    }
  }

  private static TableDef uniqueTableDefinition(
      SqlIdentifier table, List<TableDef> tables) {
    if (table.isStar() || table.names.isEmpty()) {
      return null;
    }
    String name = table.names.get(table.names.size() - 1);
    TableDef matched = null;
    for (TableDef candidate : tables) {
      if (!candidate.name().equals(name)) {
        continue;
      }
      if (matched != null) {
        return null;
      }
      matched = candidate;
    }
    return matched;
  }

  private static int partialAliasListClosingParen(
      String parserSql, SqlParserPos lastAliasPosition) {
    int last = calciteLineColumnOffset(
        parserSql,
        lastAliasPosition.getEndLineNum(),
        lastAliasPosition.getEndColumnNum());
    if (last < 0 || last >= parserSql.length()) {
      return -1;
    }
    int cursor = last + 1;
    while (cursor < parserSql.length()) {
      char current = parserSql.charAt(cursor);
      char next = cursor + 1 < parserSql.length() ? parserSql.charAt(cursor + 1) : 0;
      if (isPostgresSqlWhitespace(current)) {
        cursor++;
      } else if (current == '-' && next == '-') {
        cursor += 2;
        while (cursor < parserSql.length()
            && parserSql.charAt(cursor) != '\n'
            && parserSql.charAt(cursor) != '\r') {
          cursor++;
        }
      } else if (current == '/' && next == '*') {
        int close = parserSql.indexOf("*/", cursor + 2);
        if (close < 0) {
          return -1;
        }
        cursor = close + 2;
      } else {
        return current == ')' ? cursor : -1;
      }
    }
    return -1;
  }

  private static String quoteCalciteIdentifier(String name) {
    return '"' + name.replace("\"", "\"\"") + '"';
  }

  private record ParserInsertion(int offset, String text) {}

  private static String postgresWhitespaceForCalcite(String sql) {
    if (sql.indexOf('\u000b') < 0) {
      return sql;
    }
    StringBuilder normalized = new StringBuilder(sql.length());
    for (int index = 0; index < sql.length();) {
      char current = sql.charAt(index);
      char next = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;
      if (current == '-' && next == '-') {
        int end = index + 2;
        while (end < sql.length() && sql.charAt(end) != '\n' && sql.charAt(end) != '\r') {
          end++;
        }
        normalized.append(sql, index, end);
        index = end;
        continue;
      }
      if (current == '/' && next == '*') {
        int end = index + 2;
        int depth = 1;
        while (end < sql.length() && depth > 0) {
          char block = sql.charAt(end);
          char blockNext = end + 1 < sql.length() ? sql.charAt(end + 1) : 0;
          if (block == '/' && blockNext == '*') {
            depth++;
            end += 2;
          } else if (block == '*' && blockNext == '/') {
            depth--;
            end += 2;
          } else {
            end++;
          }
        }
        if (depth != 0) {
          throw new IllegalArgumentException("unterminated block comment in SQL query file");
        }
        normalized.append(sql, index, end);
        index = end;
        continue;
      }
      if (current == '\'' || current == '"' || current == '`') {
        int end = quotedTokenEnd(sql, index, current);
        normalized.append(sql, index, end);
        index = end;
        continue;
      }
      if (current == '[') {
        int end = bracketQuotedTokenEnd(sql, index);
        normalized.append(sql, index, end);
        index = end;
        continue;
      }
      if (current == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(sql, index);
        if (delimiterEnd >= 0) {
          String delimiter = sql.substring(index, delimiterEnd);
          int close = sql.indexOf(delimiter, delimiterEnd);
          if (close < 0) {
            throw new IllegalArgumentException("unterminated dollar-quoted SQL string");
          }
          int end = close + delimiter.length();
          normalized.append(sql, index, end);
          index = end;
          continue;
        }
      }
      normalized.append(current == '\u000b' ? ' ' : current);
      index++;
    }
    return normalized.toString();
  }

  private static IdentifierSpan bareIdentifierAt(String sql, SqlParserPos position) {
    int target = lineColumnOffset(sql, position.getLineNum(), position.getColumnNum());
    if (target < 0) {
      return null;
    }
    for (int index = 0; index < sql.length();) {
      char current = sql.charAt(index);
      char next = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;

      if (current == '-' && next == '-') {
        index += 2;
        while (index < sql.length() && sql.charAt(index) != '\n') {
          index++;
        }
        continue;
      }
      if (current == '/' && next == '*') {
        int depth = 1;
        index += 2;
        while (index < sql.length() && depth > 0) {
          char block = sql.charAt(index);
          char blockNext = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;
          if (block == '/' && blockNext == '*') {
            depth++;
            index += 2;
          } else if (block == '*' && blockNext == '/') {
            depth--;
            index += 2;
          } else {
            index++;
          }
        }
        if (depth != 0) {
          return null;
        }
        continue;
      }
      if (current == '\'' || current == '"' || current == '`') {
        try {
          index = quotedTokenEnd(sql, index, current);
        } catch (IllegalArgumentException error) {
          return null;
        }
        continue;
      }
      if (current == '[') {
        index++;
        boolean closed = false;
        while (index < sql.length()) {
          if (sql.charAt(index++) == ']') {
            if (index < sql.length() && sql.charAt(index) == ']') {
              index++;
            } else {
              closed = true;
              break;
            }
          }
        }
        if (!closed) {
          return null;
        }
        continue;
      }
      if (current == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(sql, index);
        if (delimiterEnd >= 0) {
          String delimiter = sql.substring(index, delimiterEnd);
          int close = sql.indexOf(delimiter, delimiterEnd);
          if (close < 0) {
            return null;
          }
          index = close + delimiter.length();
          continue;
        }
      }
      if (isBareIdentifierStart(current)) {
        int end = index + 1;
        while (end < sql.length() && isBareIdentifierPart(sql.charAt(end))) {
          end++;
        }
        if (target >= index && target < end) {
          return new IdentifierSpan(index, end);
        }
        index = end;
        continue;
      }
      index++;
    }
    return null;
  }

  private static int lineColumnOffset(String sql, int targetLine, int targetColumn) {
    return calciteLineColumnOffset(sql, targetLine, targetColumn);
  }

  private static int dollarQuoteDelimiterEnd(String sql, int start) {
    if (start > 0) {
      char previous = sql.charAt(start - 1);
      // PostgreSQL requires whitespace or punctuation before a dollar-quoted
      // string that follows an identifier/keyword. Otherwise `$tag$` is an
      // ordinary part of the unquoted identifier. Treat a high-bit character
      // conservatively as a possible PostgreSQL identifier continuation.
      if (isBareIdentifierPart(previous) || previous >= 0x80) {
        return -1;
      }
    }
    int index = start + 1;
    if (index < sql.length() && sql.charAt(index) >= 0x80) {
      throw new IllegalArgumentException(
          "non-ASCII PostgreSQL dollar-quote tags are not supported");
    }
    if (index < sql.length() && sql.charAt(index) == '$') {
      return index + 1;
    }
    if (index >= sql.length() || !isBareIdentifierStart(sql.charAt(index))) {
      return -1;
    }
    index++;
    while (index < sql.length()
        && (isBareIdentifierStart(sql.charAt(index)) || Character.isDigit(sql.charAt(index)))) {
      index++;
    }
    if (index < sql.length() && sql.charAt(index) >= 0x80) {
      throw new IllegalArgumentException(
          "non-ASCII PostgreSQL dollar-quote tags are not supported");
    }
    return index < sql.length() && sql.charAt(index) == '$' ? index + 1 : -1;
  }

  private static boolean isBareIdentifierStart(char value) {
    return (value >= 'A' && value <= 'Z')
        || (value >= 'a' && value <= 'z')
        || value == '_';
  }

  private static boolean isBareIdentifierPart(char value) {
    return isBareIdentifierStart(value)
        || (value >= '0' && value <= '9')
        || value == '$';
  }

  private record IdentifierSpan(int start, int end) {}

  private record ParserSql(String sql, SourcePositionMap sourcePositions) {
    ParserSql {
      Objects.requireNonNull(sql, "sql");
      Objects.requireNonNull(sourcePositions, "sourcePositions");
      if (!sql.equals(sourcePositions.parserSql())) {
        throw new IllegalArgumentException(
            "parser SQL differs from its source-position map");
      }
    }
  }

  private record SourceSpan(int start, int end) {
    SourceSpan {
      if (start < 0 || end <= start) {
        throw new IllegalArgumentException("source span must be nonempty and ordered");
      }
    }
  }

  /**
   * A closed, monotone map from every UTF-16 boundary in Calcite's private
   * parser copy back to a boundary in the byte-for-byte submitted statement.
   *
   * <p>The parser copy has exactly two permitted transformations: replacing
   * an unprotected PostgreSQL vertical-tab whitespace character by one ASCII
   * space, and inserting a pair of quotes around one allowlisted lowercase
   * identifier.  The former retains the identity boundary map.  Each inserted
   * quote maps to the adjacent original identifier boundary, so both a parser
   * span that includes the quotes and one that excludes them recover the same
   * bare identifier. No source lookup or spelling search participates in
   * provenance recovery.</p>
   */
  private static final class SourcePositionMap {
    private final String originalSql;
    private final String parserSql;
    private final int[] originalBoundary;

    private SourcePositionMap(
        String originalSql, String parserSql, int[] originalBoundary) {
      this.originalSql = Objects.requireNonNull(originalSql, "originalSql");
      this.parserSql = Objects.requireNonNull(parserSql, "parserSql");
      this.originalBoundary = Objects.requireNonNull(
          originalBoundary, "originalBoundary").clone();
      verify();
    }

    static SourcePositionMap identity(String sql) {
      int[] boundaries = new int[sql.length() + 1];
      for (int index = 0; index <= sql.length(); index++) {
        boundaries[index] = index;
      }
      return new SourcePositionMap(sql, sql, boundaries);
    }

    String parserSql() {
      return parserSql;
    }

    String originalSql() {
      return originalSql;
    }

    SourcePositionMap withCalciteWhitespace() {
      String normalized = postgresWhitespaceForCalcite(parserSql);
      if (normalized.length() != parserSql.length()) {
        throw new IllegalStateException(
            "Calcite whitespace normalization changed parser-copy width");
      }
      for (int index = 0; index < parserSql.length(); index++) {
        char before = parserSql.charAt(index);
        char after = normalized.charAt(index);
        if (before != after && !(before == '\u000b' && after == ' ')) {
          throw new IllegalStateException(
              "Calcite whitespace normalization performed an unrecognized edit");
        }
      }
      return normalized.equals(parserSql)
          ? this
          : new SourcePositionMap(originalSql, normalized, originalBoundary);
    }

    SourcePositionMap quoteBareIdentifier(IdentifierSpan span) {
      if (span == null
          || span.start() < 0
          || span.end() <= span.start()
          || span.end() > parserSql.length()) {
        throw new IllegalStateException("invalid parser identifier rewrite span");
      }
      // The retry must consume an unchanged original token. This rejects an
      // accidental retry inside an earlier insertion and any edit drift in
      // the parser copy instead of attempting to recover by text search.
      for (int index = span.start(); index < span.end(); index++) {
        int original = originalBoundary[index];
        if (originalBoundary[index + 1] != original + 1
            || original < 0
            || original >= originalSql.length()
            || parserSql.charAt(index) != originalSql.charAt(original)) {
          throw new IllegalStateException(
              "identifier retry span is not an exact original-statement token");
        }
      }

      StringBuilder quoted = new StringBuilder(parserSql.length() + 2);
      quoted.append(parserSql, 0, span.start());
      quoted.append('"');
      quoted.append(parserSql, span.start(), span.end());
      quoted.append('"');
      quoted.append(parserSql, span.end(), parserSql.length());

      int[] boundaries = new int[quoted.length() + 1];
      System.arraycopy(originalBoundary, 0, boundaries, 0, span.start() + 1);
      boundaries[span.start() + 1] = originalBoundary[span.start()];
      for (int oldBoundary = span.start() + 1;
          oldBoundary <= span.end(); oldBoundary++) {
        boundaries[oldBoundary + 1] = originalBoundary[oldBoundary];
      }
      boundaries[span.end() + 2] = originalBoundary[span.end()];
      if (span.end() < parserSql.length()) {
        System.arraycopy(
            originalBoundary,
            span.end() + 1,
            boundaries,
            span.end() + 3,
            parserSql.length() - span.end());
      }
      return new SourcePositionMap(originalSql, quoted.toString(), boundaries);
    }

    SourceSpan sourceSpan(SqlParserPos position) {
      if (position == null || position.equals(SqlParserPos.ZERO)) {
        return null;
      }
      int parserStart = calciteLineColumnOffset(
          parserSql, position.getLineNum(), position.getColumnNum());
      int parserEndLast = calciteLineColumnOffset(
          parserSql, position.getEndLineNum(), position.getEndColumnNum());
      if (parserStart < 0
          || parserEndLast < parserStart
          || parserEndLast >= parserSql.length()) {
        return null;
      }
      int originalStart = originalBoundary[parserStart];
      int originalEnd = originalBoundary[parserEndLast + 1];
      if (originalEnd <= originalStart) {
        return null;
      }
      return new SourceSpan(originalStart, originalEnd);
    }

    String sourceText(SqlNode node) {
      SourceSpan span = node == null ? null : sourceSpan(node.getParserPosition());
      return span == null ? null : originalSql.substring(span.start(), span.end());
    }

    String sourceNodeId(SqlNode node) {
      SourceSpan span = node == null ? null : sourceSpan(node.getParserPosition());
      return span == null ? null : sourceIdentity(span).nodeId();
    }

    ExactSourceIdentity exactIdentity(SqlNode node) {
      SourceSpan span = node == null ? null : sourceSpan(node.getParserPosition());
      return span == null ? null : sourceIdentity(span);
    }

    boolean exactlyContains(SqlNode parent, SqlNode child) {
      SourceSpan parentSpan = parent == null
          ? null
          : sourceSpan(parent.getParserPosition());
      SourceSpan childSpan = child == null
          ? null
          : sourceSpan(child.getParserPosition());
      return parentSpan != null
          && childSpan != null
          && parentSpan.start() <= childSpan.start()
          && childSpan.end() <= parentSpan.end();
    }

    ExactSourceIdentity orderedQueryIdentity(SqlNode query) {
      SourceSpan span = sourceQueryExtentSpan(query);
      return span == null ? null : sourceIdentity(span);
    }

    ExactSourceIdentity queryBlockIdentity(SqlSelect select) {
      SourceSpan span = directSelectExtentSpan(select);
      return span == null ? null : sourceIdentity(span);
    }

    ExactSourceIdentity relationalSourceIdentity(SqlNode node) {
      SourceSpan span = isQuerySourceNode(node)
          ? sourceQueryExtentSpan(node)
          : node == null ? null : sourceSpan(node.getParserPosition());
      return span == null ? null : sourceIdentity(span);
    }

    ExactSourceIdentity expressionIdentity(SqlNode node) {
      SourceSpan span = sourceExpressionExtentSpan(node);
      return span == null ? null : sourceIdentity(span);
    }

    /**
     * Calcite represents a source CASE with no ELSE as if it had a terminal
     * SQL NULL.  That synthetic SqlLiteral borrows the owning CASE parser
     * position, whereas a source-written ELSE NULL has its own exact NULL
     * position.  Close that distinction against the original statement: the
     * borrowed identity must equal the CASE identity and the exact text after
     * the final THEN result must contain only the mandatory END keyword.
     */
    boolean exactImplicitCaseElse(SqlCase sourceCase) {
      if (sourceCase == null
          || sourceCase.getWhenOperands() == null
          || sourceCase.getThenOperands() == null
          || sourceCase.getWhenOperands().isEmpty()
          || sourceCase.getWhenOperands().size()
              != sourceCase.getThenOperands().size()
          || !(sourceCase.getElseOperand() instanceof SqlLiteral sourceElse)
          || sourceElse.getTypeName() != SqlTypeName.NULL) {
        return false;
      }
      SourceSpan owner = sourceExpressionExtentSpan(sourceCase);
      SourceSpan terminal = sourceExpressionExtentSpan(sourceElse);
      SqlNode finalResult = sourceCase.getThenOperands().get(
          sourceCase.getThenOperands().size() - 1);
      SourceSpan finalResultSpan = sourceExpressionExtentSpan(finalResult);
      if (owner == null
          || terminal == null
          || finalResultSpan == null
          || !owner.equals(terminal)
          || finalResultSpan.start() < owner.start()
          || finalResultSpan.end() >= owner.end()) {
        return false;
      }
      int end = consumeSourceKeyword(
          skipSourceTrivia(finalResultSpan.end()), "END");
      return end == owner.end();
    }

    /**
     * Calcite's parser positions for {@link SqlWithItem}, the WITH list, and
     * {@link SqlWith} itself are not covering positions.  In Calcite 1.42 an
     * item can point only at its name, while both the list and owner can end
     * before the main body.  Recover these composite extents from exact child
     * anchors and the original PostgreSQL punctuation instead of widening a
     * parser position or searching for repeated SQL text.
     */
    ExactSourceIdentity cteItemIdentity(SqlWithItem item) {
      SourceSpan span = cteItemSpan(item);
      return span == null ? null : sourceIdentity(span);
    }

    ExactSourceIdentity cteListIdentity(SqlWith with) {
      SourceSpan span = cteListSpan(with);
      return span == null ? null : sourceIdentity(span);
    }

    ExactSourceIdentity cteQueryIdentity(SqlNode query) {
      SourceSpan span = sourceQueryExtentSpan(query);
      return span == null ? null : sourceIdentity(span);
    }

    ExactSourceIdentity declarativeQueryIdentity(SqlNode query) {
      SourceSpan span = sourceQueryExtentSpan(query);
      return span == null ? null : sourceIdentity(span);
    }

    ExactSourceIdentity cteWithIdentity(SqlWith with) {
      SourceSpan span = cteWithSpan(with);
      return span == null ? null : sourceIdentity(span);
    }

    ExactSourceIdentity cteReferenceScopeIdentity(SqlNode scope) {
      SourceSpan span = scope instanceof SqlWithItem item
          ? cteItemSpan(item)
          : sourceQueryExtentSpan(scope);
      return span == null ? null : sourceIdentity(span);
    }

    private SourceSpan sourceQueryExtentSpan(SqlNode query) {
      if (query instanceof SqlOrderBy orderBy) {
        return orderedQueryExtentSpan(orderBy);
      }
      if (query instanceof SqlWith nested) {
        return cteWithSpan(nested);
      }
      if (query instanceof SqlSelect select) {
        return directSelectExtentSpan(select);
      }
      if (query instanceof SqlCall call
          && call.getOperator() instanceof SqlSetOperator setOperator) {
        return setQueryExtentSpan(call, setOperator);
      }
      return query == null ? null : sourceSpan(query.getParserPosition());
    }

    private SourceSpan sourceExpressionExtentSpan(SqlNode expression) {
      if (expression instanceof SqlCall call) {
        SourceSpan queryPredicate = queryPredicateExtentSpan(call);
        if (queryPredicate != null) {
          return queryPredicate;
        }
        SourceSpan negatedQueryPredicate = negatedQueryPredicateExtentSpan(call);
        if (negatedQueryPredicate != null) {
          return negatedQueryPredicate;
        }
        SourceSpan composite = compositeExpressionExtentSpan(call);
        if (composite != null) {
          return composite;
        }
      }
      return expression == null ? null : sourceSpan(expression.getParserPosition());
    }

    /**
     * Complete an IN/NOT IN/EXISTS expression from its exact AST operands.
     * Calcite 1.42 ends an IN-subquery call at the query's final token and
     * omits the mandatory closing parenthesis.  The independently parsed
     * query extent and its directly matching wrapper recover that delimiter;
     * the bounded gap must still contain exactly the owning predicate syntax.
     */
    private SourceSpan queryPredicateExtentSpan(SqlCall call) {
      String kind = call.getKind().name();
      boolean in = kind.equals("IN") || kind.equals("NOT_IN");
      boolean exists = kind.equals("EXISTS");
      int queryIndex = in ? 1 : exists ? 0 : -1;
      if (queryIndex < 0 || call.getOperandList().size() <= queryIndex) {
        return null;
      }
      SqlNode rawQuery = call.getOperandList().get(queryIndex);
      SqlNode query = stripAlias(rawQuery);
      if (!isQuerySourceNode(query)) {
        return null;
      }
      SourceSpan querySpan = sourceQueryExtentSpan(query);
      if (querySpan == null) {
        return null;
      }
      SourceSpan wrappedQuery = directParenthesizedQueryOperandSpan(querySpan);
      if (wrappedQuery.start() >= originalSql.length()
          || originalSql.charAt(wrappedQuery.start()) != '(') {
        return null;
      }

      int start;
      int cursor;
      if (in) {
        if (call.getOperandList().isEmpty()) {
          return null;
        }
        SourceSpan value = sourceExpressionExtentSpan(call.getOperandList().get(0));
        if (value == null) {
          return null;
        }
        start = value.start();
        cursor = skipSourceTrivia(value.end());
        if (kind.equals("NOT_IN")) {
          cursor = consumeSourceKeyword(cursor, "NOT");
          if (cursor < 0) {
            return null;
          }
          cursor = skipSourceTrivia(cursor);
        }
        cursor = consumeSourceKeyword(cursor, "IN");
      } else {
        SourceSpan parserSpan = sourceSpan(call.getParserPosition());
        if (parserSpan == null) {
          return null;
        }
        start = skipSourceTrivia(parserSpan.start());
        cursor = consumeSourceKeyword(start, "EXISTS");
      }
      return cursor >= 0 && skipSourceTrivia(cursor) == wrappedQuery.start()
          ? new SourceSpan(start, wrappedQuery.end())
          : null;
    }

    private SourceSpan negatedQueryPredicateExtentSpan(SqlCall call) {
      if (!call.getKind().name().equals("NOT")
          || call.getOperandList().size() != 1
          || !(call.getOperandList().get(0) instanceof SqlCall child)
          || queryPredicateExtentSpan(child) == null) {
        return null;
      }
      SourceSpan childSpan = sourceExpressionExtentSpan(child);
      SourceSpan wrappedChild = childSpan == null
          ? null
          : directParenthesizedQueryOperandSpan(childSpan);
      SourceSpan parserSpan = sourceSpan(call.getParserPosition());
      if (wrappedChild == null || parserSpan == null) {
        return null;
      }
      int start = skipSourceTrivia(parserSpan.start());
      int cursor = consumeSourceKeyword(start, "NOT");
      return cursor >= 0 && skipSourceTrivia(cursor) == wrappedChild.start()
          ? new SourceSpan(start, wrappedChild.end())
          : null;
    }

    /**
     * Propagate a proved query-predicate closing delimiter through its direct
     * scalar AST owners. Calcite can give an enclosing AND/OR the same
     * truncated end as its final IN-subquery child. Widen only when every
     * direct operand's own parser span is already contained by the parent and
     * one recursively completed child extends that same final boundary.
     */
    private SourceSpan compositeExpressionExtentSpan(SqlCall call) {
      SourceSpan parserSpan = sourceSpan(call.getParserPosition());
      if (parserSpan == null || call.getOperandList().isEmpty()) {
        return null;
      }
      int end = parserSpan.end();
      boolean completedChild = false;
      for (SqlNode operand : call.getOperandList()) {
        if (operand == null) {
          continue;
        }
        SourceSpan rawChild = sourceSpan(operand.getParserPosition());
        if (rawChild == null
            || rawChild.start() < parserSpan.start()
            || rawChild.end() > parserSpan.end()) {
          return null;
        }
        SourceSpan child = sourceExpressionExtentSpan(operand);
        if (child == null || child.start() < rawChild.start()) {
          return null;
        }
        if (child.end() > end) {
          end = child.end();
          completedChild = true;
        }
      }
      return completedChild ? new SourceSpan(parserSpan.start(), end) : null;
    }

    /**
     * Calcite can include a direct parenthesis wrapper in one SELECT parser
     * position but omit the corresponding wrapper from its sibling. Strip
     * only wrappers whose exact matching close is the end of this very AST
     * node, then require the node-owned SELECT token at the resulting start.
     */
    private SourceSpan directSelectExtentSpan(SqlSelect select) {
      SourceSpan parserSpan = select == null
          ? null
          : sourceSpan(select.getParserPosition());
      if (parserSpan == null) {
        return null;
      }
      int start = parserSpan.start();
      int end = parserSpan.end();
      for (int fuel = 0; fuel < 16; fuel++) {
        start = skipSourceTrivia(start);
        if (start >= end || originalSql.charAt(start) != '(') {
          break;
        }
        int close = matchingSourceCloseParen(start);
        if (close < 0 || close + 1 != end) {
          break;
        }
        start++;
        end = close;
      }
      start = skipSourceTrivia(start);
      return consumeSourceKeyword(start, "SELECT") < 0 || start >= end
          ? null
          : new SourceSpan(start, end);
    }

    /**
     * Build a set-query extent from its direct AST operands. Calcite 1.42 can
     * assign a UNION/EXCEPT call the span from the first branch's final ONLY
     * token through the second branch, or can include only one sibling's
     * parenthesis. Direct child extents plus their immediately matching
     * parenthesis wrappers give a balanced, branch-local range; the bounded
     * gap must be exactly this SqlSetOperator and quantifier.
     */
    private SourceSpan setQueryExtentSpan(SqlCall call, SqlSetOperator operator) {
      if (call == null || call.getOperandList().size() < 2) {
        return null;
      }
      List<SourceSpan> operands = new ArrayList<>();
      for (SqlNode operand : call.getOperandList()) {
        SourceSpan child = sourceQueryExtentSpan(operand);
        if (child == null) {
          return null;
        }
        operands.add(directParenthesizedQueryOperandSpan(child));
      }
      for (int index = 1; index < operands.size(); index++) {
        SourceSpan left = operands.get(index - 1);
        SourceSpan right = operands.get(index);
        if (left.end() >= right.start()
            || !hasExactSetOperatorBoundary(
                left.end(), right.start(), call.getKind().name(), operator.isAll())) {
          return null;
        }
      }
      return new SourceSpan(
          operands.get(0).start(), operands.get(operands.size() - 1).end());
    }

    private SourceSpan directParenthesizedQueryOperandSpan(SourceSpan child) {
      int start = child.start();
      int end = child.end();
      for (int fuel = 0; fuel < 16 && start > 0; fuel++) {
        int open = start - 1;
        while (open >= 0 && isPostgresSqlWhitespace(originalSql.charAt(open))) {
          open--;
        }
        if (open < 0 || originalSql.charAt(open) != '(') {
          break;
        }
        int close = matchingSourceCloseParen(open);
        if (close < 0 || skipSourceTrivia(end) != close) {
          break;
        }
        start = open;
        end = close + 1;
      }
      return new SourceSpan(start, end);
    }

    private boolean hasExactSetOperatorBoundary(
        int leftEnd, int rightStart, String kind, boolean all) {
      String keyword = switch (kind) {
        case "UNION" -> "UNION";
        case "INTERSECT" -> "INTERSECT";
        case "MINUS", "EXCEPT" -> "EXCEPT";
        default -> null;
      };
      if (keyword == null) {
        return false;
      }
      int cursor = skipSourceTrivia(leftEnd);
      cursor = consumeSourceKeyword(cursor, keyword);
      if (cursor < 0) {
        return false;
      }
      cursor = skipSourceTrivia(cursor);
      int allEnd = consumeSourceKeyword(cursor, "ALL");
      int distinctEnd = consumeSourceKeyword(cursor, "DISTINCT");
      if (all) {
        if (allEnd < 0) {
          return false;
        }
        cursor = allEnd;
      } else if (allEnd >= 0) {
        return false;
      } else if (distinctEnd >= 0) {
        cursor = distinctEnd;
      }
      return skipSourceTrivia(cursor) == rightStart;
    }

    /**
     * Recover the complete declarative query extent of Calcite's SqlOrderBy.
     * Calcite 1.42 assigns that composite node the position of its final
     * decoration token (for example ONLY), so its parser position is not a
     * covering identity. Reconstruct the extent monotonically from the exact
     * base query and ordered clause operands, accepting only PostgreSQL/SQL
     * clause spellings whose punctuation is closed in the original source.
     */
    private SourceSpan orderedQueryExtentSpan(SqlOrderBy orderBy) {
      if (orderBy == null || orderBy.query == null) {
        return null;
      }
      SourceSpan query = sourceQueryExtentSpan(orderBy.query);
      if (query == null) {
        return null;
      }
      int end = query.end();

      if (orderBy.orderList != null && !orderBy.orderList.isEmpty()) {
        SourceSpan orderList = orderListSpan(orderBy.orderList);
        int cursor = skipSourceTrivia(end);
        cursor = consumeSourceKeyword(cursor, "ORDER");
        if (cursor < 0) {
          return null;
        }
        cursor = skipSourceTrivia(cursor);
        cursor = consumeSourceKeyword(cursor, "BY");
        if (cursor < 0
            || orderList == null
            || skipSourceTrivia(cursor) != orderList.start()) {
          return null;
        }
        end = orderList.end();
      }

      SourceSpan offset = orderBy.offset == null
          ? null
          : sourceSpan(orderBy.offset.getParserPosition());
      SourceSpan fetch = orderBy.fetch == null
          ? null
          : sourceSpan(orderBy.fetch.getParserPosition());
      if (orderBy.offset != null && offset == null
          || orderBy.fetch != null && fetch == null) {
        return null;
      }

      while (offset != null || fetch != null) {
        if (offset != null && (fetch == null || offset.start() < fetch.start())) {
          int cursor = skipSourceTrivia(end);
          cursor = consumeSourceKeyword(cursor, "OFFSET");
          if (cursor < 0 || skipSourceTrivia(cursor) != offset.start()) {
            return null;
          }
          end = offset.end();
          cursor = skipSourceTrivia(end);
          int rowEnd = consumeSourceKeyword(cursor, "ROW");
          if (rowEnd < 0) {
            rowEnd = consumeSourceKeyword(cursor, "ROWS");
          }
          if (rowEnd >= 0) {
            end = rowEnd;
          }
          offset = null;
          continue;
        }

        int cursor = skipSourceTrivia(end);
        int limitEnd = consumeSourceKeyword(cursor, "LIMIT");
        if (limitEnd >= 0) {
          if (skipSourceTrivia(limitEnd) != fetch.start()) {
            return null;
          }
          end = fetch.end();
          fetch = null;
          continue;
        }

        cursor = consumeSourceKeyword(cursor, "FETCH");
        if (cursor < 0) {
          return null;
        }
        cursor = skipSourceTrivia(cursor);
        int directionEnd = consumeSourceKeyword(cursor, "FIRST");
        if (directionEnd < 0) {
          directionEnd = consumeSourceKeyword(cursor, "NEXT");
        }
        if (directionEnd < 0 || skipSourceTrivia(directionEnd) != fetch.start()) {
          return null;
        }
        end = fetch.end();
        cursor = skipSourceTrivia(end);
        int rowsEnd = consumeSourceKeyword(cursor, "ROW");
        if (rowsEnd < 0) {
          rowsEnd = consumeSourceKeyword(cursor, "ROWS");
        }
        if (rowsEnd < 0) {
          return null;
        }
        cursor = skipSourceTrivia(rowsEnd);
        int onlyEnd = consumeSourceKeyword(cursor, "ONLY");
        if (onlyEnd < 0) {
          return null;
        }
        end = onlyEnd;
        fetch = null;
      }
      return new SourceSpan(query.start(), end);
    }

    private SourceSpan cteItemSpan(SqlWithItem item) {
      if (item == null
          || item.name == null
          || !item.name.isSimple()
          || item.query == null
          || item.recursive != null && item.recursive.booleanValue()) {
        return null;
      }
      SourceSpan name = sourceSpan(item.name.getParserPosition());
      SourceSpan query = sourceQueryExtentSpan(item.query);
      if (name == null || query == null || name.end() >= query.start()) {
        return null;
      }
      int cursor = skipSourceTrivia(name.end());
      if (item.columnList != null && !item.columnList.isEmpty()) {
        if (cursor >= originalSql.length() || originalSql.charAt(cursor) != '(') {
          return null;
        }
        int columnListOpen = cursor;
        cursor = skipSourceTrivia(columnListOpen + 1);
        for (int index = 0; index < item.columnList.size(); index++) {
          SqlNode rawColumn = item.columnList.get(index);
          SourceSpan column = rawColumn == null
              ? null
              : sourceSpan(rawColumn.getParserPosition());
          if (!(rawColumn instanceof SqlIdentifier identifier)
              || !identifier.isSimple()
              || column == null
              || cursor != column.start()) {
            return null;
          }
          cursor = skipSourceTrivia(column.end());
          if (index + 1 < item.columnList.size()) {
            if (cursor >= originalSql.length() || originalSql.charAt(cursor) != ',') {
              return null;
            }
            cursor = skipSourceTrivia(cursor + 1);
          }
        }
        if (cursor >= originalSql.length()
            || originalSql.charAt(cursor) != ')'
            || matchingSourceCloseParen(columnListOpen) != cursor) {
          return null;
        }
        cursor = skipSourceTrivia(cursor + 1);
      }
      cursor = consumeSourceKeyword(cursor, "AS");
      if (cursor < 0) {
        return null;
      }
      cursor = skipSourceTrivia(cursor);
      if (cursor >= originalSql.length() || originalSql.charAt(cursor) != '(') {
        return null;
      }
      int open = cursor;
      if (skipSourceTrivia(open + 1) != query.start()) {
        return null;
      }
      int close = skipSourceTrivia(query.end());
      if (close >= originalSql.length()
          || originalSql.charAt(close) != ')'
          || matchingSourceCloseParen(open) != close) {
        return null;
      }
      return new SourceSpan(name.start(), close + 1);
    }

    private SourceSpan cteListSpan(SqlWith with) {
      if (with == null || with.withList == null || with.withList.isEmpty()) {
        return null;
      }
      SourceSpan first = null;
      SourceSpan previous = null;
      for (SqlNode rawItem : with.withList) {
        if (!(rawItem instanceof SqlWithItem item)) {
          return null;
        }
        SourceSpan current = cteItemSpan(item);
        if (current == null) {
          return null;
        }
        if (previous != null) {
          int separator = skipSourceTrivia(previous.end());
          if (separator >= originalSql.length()
              || originalSql.charAt(separator) != ','
              || skipSourceTrivia(separator + 1) != current.start()) {
            return null;
          }
        }
        if (first == null) {
          first = current;
        }
        previous = current;
      }
      return new SourceSpan(first.start(), previous.end());
    }

    private SourceSpan cteWithSpan(SqlWith with) {
      SourceSpan parserSpan = with == null ? null : sourceSpan(with.getParserPosition());
      SourceSpan list = cteListSpan(with);
      SourceSpan body = with == null ? null : sourceQueryExtentSpan(with.body);
      if (parserSpan == null
          || list == null
          || body == null
          || parserSpan.start() >= list.start()
          || list.end() > body.start()) {
        return null;
      }
      int withEnd = consumeSourceKeyword(parserSpan.start(), "WITH");
      if (withEnd < 0
          || skipSourceTrivia(withEnd) != list.start()
          || skipSourceTrivia(list.end()) != body.start()) {
        // This also rejects WITH RECURSIVE conservatively: Logos does not yet
        // model recursive fixed-point semantics.
        return null;
      }
      return new SourceSpan(parserSpan.start(), body.end());
    }

    private int matchingSourceCloseParen(int open) {
      if (open < 0 || open >= originalSql.length() || originalSql.charAt(open) != '(') {
        return -1;
      }
      int depth = 0;
      for (int index = open; index < originalSql.length();) {
        char current = originalSql.charAt(index);
        char next = index + 1 < originalSql.length() ? originalSql.charAt(index + 1) : 0;
        if (current == '-' && next == '-') {
          index += 2;
          while (index < originalSql.length()
              && originalSql.charAt(index) != '\n'
              && originalSql.charAt(index) != '\r') {
            index++;
          }
          continue;
        }
        if (current == '/' && next == '*') {
          int close = originalSql.indexOf("*/", index + 2);
          if (close < 0) {
            return -1;
          }
          index = close + 2;
          continue;
        }
        if (current == '\'' || current == '"' || current == '`') {
          try {
            index = quotedTokenEnd(originalSql, index, current);
          } catch (IllegalArgumentException error) {
            return -1;
          }
          continue;
        }
        if (current == '$') {
          int delimiterEnd = dollarQuoteDelimiterEnd(originalSql, index);
          if (delimiterEnd >= 0) {
            String delimiter = originalSql.substring(index, delimiterEnd);
            int close = originalSql.indexOf(delimiter, delimiterEnd);
            if (close < 0) {
              return -1;
            }
            index = close + delimiter.length();
            continue;
          }
        }
        if (current == '(') {
          depth++;
        } else if (current == ')') {
          depth--;
          if (depth == 0) {
            return index;
          }
          if (depth < 0) {
            return -1;
          }
        }
        index++;
      }
      return -1;
    }

    boolean sourceIdentifierComponentQuoted(SqlIdentifier identifier, int component) {
      if (identifier == null || component < 0 || component >= identifier.names.size()) {
        throw new UnsupportedOperationException(
            "missing exact source identifier component");
      }
      SourceSpan span = sourceSpan(identifier.getComponentParserPosition(component));
      if (span == null) {
        List<ExactIdentifierComponent> recovered = exactIdentifierComponents(identifier);
        if (recovered == null || recovered.size() != identifier.names.size()) {
          SourceSpan whole = sourceSpan(identifier.getParserPosition());
          throw new UnsupportedOperationException(
              "missing exact source identifier component position"
                  + (whole == null
                      ? " (whole identifier position is also unavailable: whole="
                          + identifier.getParserPosition()
                          + ", component="
                          + identifier.getComponentParserPosition(component) + ")"
                      : " (whole exact text: "
                          + originalSql.substring(whole.start(), whole.end()) + ")"));
        }
        return recovered.get(component).quoted();
      }
      String exact = originalSql.substring(span.start(), span.end());
      String name = identifier.names.get(component);
      if (name.isEmpty() && exact.equals("*")) {
        return false;
      }
      if (exact.length() >= 2
          && exact.charAt(0) == '"'
          && exact.charAt(exact.length() - 1) == '"') {
        String decoded = exact.substring(1, exact.length() - 1).replace("\"\"", "\"");
        if (!decoded.equals(name)) {
          throw new UnsupportedOperationException(
              "quoted source identifier differs from its parsed component");
        }
        return true;
      }
      if (exact.isEmpty()
          || exact.indexOf('"') >= 0
          || !postgresBareIdentifierKey(exact).equals(name)) {
        throw new UnsupportedOperationException(
            "unquoted source identifier differs from its parsed component");
      }
      return false;
    }

    /**
     * Calcite can omit component positions after treating a PostgreSQL
     * carriage return as a line boundary. Recover only from the identifier's
     * already mapped whole span: lex every component in order, decode quotes,
     * and compare it to Calcite's parsed names. This never searches for a
     * matching spelling elsewhere in the statement.
     */
    private List<ExactIdentifierComponent> exactIdentifierComponents(
        SqlIdentifier identifier) {
      SourceSpan whole = identifier == null
          ? null
          : sourceSpan(identifier.getParserPosition());
      if (whole == null) {
        return null;
      }
      List<ExactIdentifierComponent> components = new ArrayList<>();
      int cursor = whole.start();
      while (cursor < whole.end()) {
        String decoded;
        boolean quoted;
        char current = originalSql.charAt(cursor);
        if (current == '"') {
          int tokenEnd;
          try {
            tokenEnd = quotedTokenEnd(originalSql, cursor, '"');
          } catch (IllegalArgumentException error) {
            return null;
          }
          if (tokenEnd > whole.end()) {
            return null;
          }
          decoded = originalSql
              .substring(cursor + 1, tokenEnd - 1)
              .replace("\"\"", "\"");
          quoted = true;
          cursor = tokenEnd;
        } else if (current == '*') {
          decoded = "";
          quoted = false;
          cursor++;
        } else {
          if (!isBareIdentifierStart(current) && current < 0x80) {
            return null;
          }
          int tokenEnd = cursor + 1;
          while (tokenEnd < whole.end()) {
            char part = originalSql.charAt(tokenEnd);
            if (!isBareIdentifierPart(part) && part < 0x80) {
              break;
            }
            tokenEnd++;
          }
          decoded = postgresBareIdentifierKey(
              originalSql.substring(cursor, tokenEnd));
          quoted = false;
          cursor = tokenEnd;
        }
        int index = components.size();
        if (index >= identifier.names.size()
            || !decoded.equals(identifier.names.get(index))) {
          return null;
        }
        components.add(new ExactIdentifierComponent(decoded, quoted));
        if (cursor == whole.end()) {
          break;
        }
        int afterTrivia = skipSourceTrivia(cursor);
        if (afterTrivia >= whole.end()
            || originalSql.charAt(afterTrivia) != '.') {
          return null;
        }
        cursor = skipSourceTrivia(afterTrivia + 1);
        if (cursor >= whole.end()) {
          return null;
        }
      }
      return components.size() == identifier.names.size() ? components : null;
    }

    private static String postgresBareIdentifierKey(String exact) {
      StringBuilder folded = new StringBuilder(exact.length());
      for (int index = 0; index < exact.length(); index++) {
        char current = exact.charAt(index);
        folded.append(current >= 'A' && current <= 'Z'
            ? (char) (current - 'A' + 'a')
            : current);
      }
      return folded.toString();
    }

    private record ExactIdentifierComponent(String decoded, boolean quoted) {}

    /**
     * Recover one complete PostgreSQL ORDER BY item from the exact expression
     * position. Calcite assigns the wrapper calls for DESC/NULLS to only the
     * final decoration token, so the SqlNode position for the decorated item
     * is not a trustworthy covering span.
     */
    ExactSourceIdentity orderItemIdentity(SqlNode rawItem) {
      SourceSpan span = orderItemSpan(rawItem);
      return span == null ? null : sourceIdentity(span);
    }

    private SourceSpan orderItemSpan(SqlNode rawItem) {
      SqlNode expression = stripOrderByDecoration(rawItem);
      SourceSpan expressionSpan = expression == null
          ? null
          : sourceSpan(expression.getParserPosition());
      if (expressionSpan == null) {
        return null;
      }
      int end = expressionSpan.end();
      int cursor = skipSourceTrivia(end);
      int directionEnd = consumeSourceKeyword(cursor, "ASC");
      if (directionEnd < 0) {
        directionEnd = consumeSourceKeyword(cursor, "DESC");
      }
      if (directionEnd >= 0) {
        end = directionEnd;
        cursor = skipSourceTrivia(directionEnd);
      }
      int nullsEnd = consumeSourceKeyword(cursor, "NULLS");
      if (nullsEnd >= 0) {
        int placementStart = skipSourceTrivia(nullsEnd);
        int placementEnd = consumeSourceKeyword(placementStart, "FIRST");
        if (placementEnd < 0) {
          placementEnd = consumeSourceKeyword(placementStart, "LAST");
        }
        if (placementEnd < 0) {
          return null;
        }
        end = placementEnd;
      }
      return new SourceSpan(expressionSpan.start(), end);
    }

    ExactSourceIdentity orderListIdentity(SqlNodeList orderList) {
      SourceSpan span = orderListSpan(orderList);
      return span == null ? null : sourceIdentity(span);
    }

    boolean hasDirectOrderByBoundary(SqlNode query, SqlNodeList orderList) {
      SourceSpan querySpan = sourceQueryExtentSpan(query);
      SourceSpan listSpan = orderListSpan(orderList);
      if (querySpan == null || listSpan == null || querySpan.end() >= listSpan.start()) {
        return false;
      }
      int cursor = skipSourceTrivia(querySpan.end());
      cursor = consumeSourceKeyword(cursor, "ORDER");
      if (cursor < 0) {
        return false;
      }
      cursor = skipSourceTrivia(cursor);
      cursor = consumeSourceKeyword(cursor, "BY");
      return cursor >= 0 && skipSourceTrivia(cursor) == listSpan.start();
    }

    private SourceSpan orderListSpan(SqlNodeList orderList) {
      if (orderList == null || orderList.isEmpty()) {
        return null;
      }
      SourceSpan first = null;
      SourceSpan previous = null;
      for (SqlNode rawItem : orderList) {
        SourceSpan current = orderItemSpan(rawItem);
        if (current == null) {
          return null;
        }
        if (previous != null) {
          int separator = skipSourceTrivia(previous.end());
          if (separator >= originalSql.length() || originalSql.charAt(separator) != ',') {
            return null;
          }
          if (skipSourceTrivia(separator + 1) != current.start()) {
            return null;
          }
        }
        if (first == null) {
          first = current;
        }
        previous = current;
      }
      return new SourceSpan(first.start(), previous.end());
    }

    private int skipSourceTrivia(int start) {
      int cursor = start;
      while (cursor < originalSql.length()) {
        char current = originalSql.charAt(cursor);
        char next = cursor + 1 < originalSql.length() ? originalSql.charAt(cursor + 1) : 0;
        if (isPostgresSqlWhitespace(current)) {
          cursor++;
          continue;
        }
        if (current == '-' && next == '-') {
          cursor += 2;
          while (cursor < originalSql.length()
              && originalSql.charAt(cursor) != '\n'
              && originalSql.charAt(cursor) != '\r') {
            cursor++;
          }
          continue;
        }
        if (current == '/' && next == '*') {
          int close = originalSql.indexOf("*/", cursor + 2);
          if (close < 0) {
            return originalSql.length();
          }
          cursor = close + 2;
          continue;
        }
        break;
      }
      return cursor;
    }

    private int consumeSourceKeyword(int start, String keyword) {
      int end = start + keyword.length();
      if (start < 0
          || end > originalSql.length()
          || !originalSql.regionMatches(true, start, keyword, 0, keyword.length())) {
        return -1;
      }
      if (start > 0 && isBareIdentifierPart(originalSql.charAt(start - 1))) {
        return -1;
      }
      if (end < originalSql.length() && isBareIdentifierPart(originalSql.charAt(end))) {
        return -1;
      }
      return end;
    }

    ExactSourceIdentity coveringIdentity(List<SqlNode> nodes) {
      if (nodes == null || nodes.isEmpty()) {
        return null;
      }
      SourceSpan first = null;
      SourceSpan previous = null;
      for (SqlNode node : nodes) {
        SourceSpan current = node == null ? null : sourceSpan(node.getParserPosition());
        if (current == null || previous != null && current.start() <= previous.end()) {
          return null;
        }
        if (first == null) {
          first = current;
        }
        previous = current;
      }
      return sourceIdentity(new SourceSpan(first.start(), previous.end()));
    }

    ExactSourceIdentity relationIdentity(SqlNode relation) {
      SourceSpan span = relationSpan(relation);
      return span == null ? null : sourceIdentity(span);
    }

    ExactSourceIdentity unaliasedDerivedRelationIdentity(SqlNode relation) {
      if (!isQuerySourceNode(relation)) {
        return null;
      }
      SourceSpan query = sourceQueryExtentSpan(relation);
      SourceSpan relationExtent = relationSpan(relation);
      if (query == null
          || relationExtent == null
          || relationExtent.start() >= query.start()
          || relationExtent.end() <= query.end()) {
        return null;
      }
      // Projected-expansion validation treats the opening parenthesis as the
      // exact FROM prefix and the closing parenthesis as the relation suffix,
      // matching Calcite's aliased-query node extent.
      return sourceIdentity(new SourceSpan(query.start(), relationExtent.end()));
    }

    private SourceSpan relationSpan(SqlNode relation) {
      if (relation instanceof SqlJoin join) {
        SourceSpan left = relationSpan(join.getLeft());
        SourceSpan right = relationSpan(join.getRight());
        SourceSpan condition = join.getCondition() == null
            ? null
            : sourceSpan(join.getCondition().getParserPosition());
        if (left == null
            || right == null
            || left.end() >= right.start()
            || condition != null && right.end() >= condition.start()) {
          return null;
        }
        return new SourceSpan(
            left.start(), condition == null ? right.end() : condition.end());
      }
      if (relation instanceof SqlCall call
          && call.getKind().name().equals("AS")
          && call.getOperandList().size() >= 2
          && isQuerySourceNode(call.getOperandList().get(0))) {
        SqlNode queryNode = call.getOperandList().get(0);
        SqlNode aliasNode = call.getOperandList().get(1);
        SourceSpan query = sourceQueryExtentSpan(queryNode);
        SourceSpan alias = aliasNode == null
            ? null
            : sourceSpan(aliasNode.getParserPosition());
        if (query == null || alias == null || query.end() >= alias.start()) {
          return null;
        }
        int open = query.start() - 1;
        while (open >= 0 && isPostgresSqlWhitespace(originalSql.charAt(open))) {
          open--;
        }
        if (open < 0
            || originalSql.charAt(open) != '('
            || skipSourceTrivia(open + 1) != query.start()) {
          return null;
        }
        int close = skipSourceTrivia(query.end());
        if (close >= originalSql.length()
            || originalSql.charAt(close) != ')'
            || matchingSourceCloseParen(open) != close) {
          return null;
        }
        int aliasStart = skipSourceTrivia(close + 1);
        int afterAs = consumeSourceKeyword(aliasStart, "AS");
        if (afterAs >= 0) {
          aliasStart = skipSourceTrivia(afterAs);
        }
        if (aliasStart != alias.start()) {
          return null;
        }
        int relationEnd = alias.end();
        if (call.getOperandList().size() > 2) {
          int columnListOpen = skipSourceTrivia(alias.end());
          if (columnListOpen >= originalSql.length()
              || originalSql.charAt(columnListOpen) != '(') {
            return null;
          }
          int cursor = skipSourceTrivia(columnListOpen + 1);
          for (int index = 2; index < call.getOperandList().size(); index++) {
            SqlNode columnAlias = call.getOperandList().get(index);
            SourceSpan column = columnAlias == null
                ? null
                : sourceSpan(columnAlias.getParserPosition());
            if (!(columnAlias instanceof SqlIdentifier identifier)
                || !identifier.isSimple()
                || column == null
                || cursor != column.start()) {
              return null;
            }
            cursor = skipSourceTrivia(column.end());
            if (index + 1 < call.getOperandList().size()) {
              if (cursor >= originalSql.length() || originalSql.charAt(cursor) != ',') {
                return null;
              }
              cursor = skipSourceTrivia(cursor + 1);
            }
          }
          if (cursor >= originalSql.length()
              || originalSql.charAt(cursor) != ')'
              || matchingSourceCloseParen(columnListOpen) != cursor) {
            return null;
          }
          relationEnd = cursor + 1;
        }
        return new SourceSpan(open, relationEnd);
      }
      if (isQuerySourceNode(relation)) {
        // PostgreSQL 16+ accepts `FROM (SELECT ...)` without an alias. Calcite
        // gives the SqlSelect only its inner query position, so recover the
        // exact parenthesized relation extent and require one matching pair.
        SourceSpan query = sourceQueryExtentSpan(relation);
        if (query == null) {
          return null;
        }
        int open = query.start() - 1;
        while (open >= 0 && isPostgresSqlWhitespace(originalSql.charAt(open))) {
          open--;
        }
        if (open < 0
            || originalSql.charAt(open) != '('
            || skipSourceTrivia(open + 1) != query.start()) {
          return null;
        }
        int close = skipSourceTrivia(query.end());
        if (close >= originalSql.length()
            || originalSql.charAt(close) != ')'
            || matchingSourceCloseParen(open) != close) {
          return null;
        }
        return new SourceSpan(open, close + 1);
      }
      return relation == null ? null : sourceSpan(relation.getParserPosition());
    }

    ExactSourceIdentity joinSyntaxIdentity(SqlJoin join) {
      if (join == null) {
        return null;
      }
      SourceSpan joinToken = sourceSpan(join.getJoinTypeNode().getParserPosition());
      if (joinToken == null) {
        return null;
      }
      String syntax = join.getJoinType().name();
      if (syntax.equals("COMMA")) {
        return originalSql.substring(joinToken.start(), joinToken.end()).trim().equals(",")
            ? sourceIdentity(joinToken)
            : null;
      }
      if (!originalSql.substring(joinToken.start(), joinToken.end())
          .trim().equalsIgnoreCase("JOIN")) {
        return null;
      }
      int start = joinToken.start();
      String required = switch (syntax) {
        case "CROSS" -> "CROSS";
        case "LEFT" -> "LEFT";
        case "RIGHT" -> "RIGHT";
        case "FULL" -> "FULL";
        case "INNER" -> "INNER";
        default -> null;
      };
      if (required == null) {
        return null;
      }
      int wordEnd = start;
      while (wordEnd > 0 && Character.isWhitespace(originalSql.charAt(wordEnd - 1))) {
        wordEnd--;
      }
      int wordStart = wordEnd;
      while (wordStart > 0) {
        char ch = originalSql.charAt(wordStart - 1);
        if (!Character.isLetterOrDigit(ch) && ch != '_') {
          break;
        }
        wordStart--;
      }
      String previous = originalSql.substring(wordStart, wordEnd);
      if (syntax.equals("INNER") && !previous.equalsIgnoreCase("INNER")) {
        // Bare JOIN is PostgreSQL's INNER syntax. Do not search farther left:
        // the immediately preceding token belongs to the left relation.
        return sourceIdentity(joinToken);
      }
      if ((syntax.equals("LEFT") || syntax.equals("RIGHT") || syntax.equals("FULL"))
          && previous.equalsIgnoreCase("OUTER")) {
        wordEnd = wordStart;
        while (wordEnd > 0 && Character.isWhitespace(originalSql.charAt(wordEnd - 1))) {
          wordEnd--;
        }
        wordStart = wordEnd;
        while (wordStart > 0) {
          char ch = originalSql.charAt(wordStart - 1);
          if (!Character.isLetterOrDigit(ch) && ch != '_') {
            break;
          }
          wordStart--;
        }
        previous = originalSql.substring(wordStart, wordEnd);
      }
      if (!previous.equalsIgnoreCase(required)) {
        return null;
      }
      return sourceIdentity(new SourceSpan(wordStart, joinToken.end()));
    }

    private ExactSourceIdentity sourceIdentity(SourceSpan span) {
      LineColumn start = originalLineColumn(originalSql, span.start());
      LineColumn end = originalLineColumn(originalSql, span.end() - 1);
      String nodeId = start.line() + ":" + start.column()
          + "-" + end.line() + ":" + end.column();
      return new ExactSourceIdentity(
          nodeId, originalSql.substring(span.start(), span.end()));
    }

    private void verify() {
      if (originalBoundary.length != parserSql.length() + 1
          || originalBoundary[0] != 0
          || originalBoundary[originalBoundary.length - 1] != originalSql.length()) {
        throw new IllegalArgumentException(
            "parser source-position map has inconsistent endpoints");
      }
      int previous = -1;
      for (int boundary : originalBoundary) {
        if (boundary < 0 || boundary > originalSql.length() || boundary < previous) {
          throw new IllegalArgumentException(
              "parser source-position map is not bounded and monotone");
        }
        previous = boundary;
      }
      for (int index = 0; index < parserSql.length(); index++) {
        int original = originalBoundary[index];
        int delta = originalBoundary[index + 1] - original;
        char parserCharacter = parserSql.charAt(index);
        if (delta == 0) {
          if (parserCharacter != '"') {
            throw new IllegalArgumentException(
                "only an inserted identifier quote may have zero source width");
          }
        } else if (delta == 1) {
          char originalCharacter = originalSql.charAt(original);
          if (parserCharacter != originalCharacter
              && !(originalCharacter == '\u000b' && parserCharacter == ' ')) {
            throw new IllegalArgumentException(
                "parser source-position map contains unrecognized edit drift");
          }
        } else {
          throw new IllegalArgumentException(
              "parser source-position map skips original statement content");
        }
      }
    }
  }

  private record LineColumn(int line, int column) {}

  /**
   * Convert Calcite's one-based parser position to a UTF-16 offset. Calcite's
   * {@code SqlParserPos} columns are raw reader columns: a tab occupies one
   * column and an astral character occupies its two Java {@code char}s. This
   * differs from both stock JavaCC tab-stop accounting and the downstream
   * Unicode-scalar source-coordinate convention.
   */
  private static int calciteLineColumnOffset(
      String sql, int targetLine, int targetColumn) {
    if (targetLine < 1 || targetColumn < 1) {
      return -1;
    }
    int line = 1;
    int column = 1;
    for (int index = 0; index < sql.length(); index++) {
      if (line == targetLine && column == targetColumn) {
        return index;
      }
      if (sql.charAt(index) == '\r') {
        // JavaCC/Calcite treats both lone CR and CRLF as one line boundary.
        // Skip the LF half of CRLF here so it cannot advance the line twice.
        if (index + 1 < sql.length() && sql.charAt(index + 1) == '\n') {
          index++;
        }
        line++;
        column = 1;
      } else if (sql.charAt(index) == '\n') {
        line++;
        column = 1;
      } else {
        column++;
      }
    }
    return -1;
  }

  /**
   * Original-statement coordinates use the consumer's Unicode-scalar,
   * LF-separated convention, not JavaCC's tab-expanded parser columns.
   */
  private static LineColumn originalLineColumn(String sql, int targetOffset) {
    if (targetOffset < 0 || targetOffset >= sql.length()) {
      throw new IllegalArgumentException("original source offset is outside the statement");
    }
    if (targetOffset > 0
        && Character.isLowSurrogate(sql.charAt(targetOffset))
        && Character.isHighSurrogate(sql.charAt(targetOffset - 1))) {
      targetOffset--;
    }
    int line = 1;
    int column = 1;
    for (int offset = 0; offset < targetOffset;) {
      int codePoint = sql.codePointAt(offset);
      if (codePoint == '\n') {
        line++;
        column = 1;
      } else if (codePoint != '\r' || offset + 1 >= sql.length()
          || sql.charAt(offset + 1) != '\n') {
        column++;
      }
      offset += Character.charCount(codePoint);
    }
    return new LineColumn(line, column);
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
        out.name("declaredType").value(column.declaredType);
        out.comma();
        out.name("explicitCollation").value(column.explicitCollation);
        out.comma();
        out.name("precision").value(column.precision);
        out.comma();
        out.name("scale").value(column.scale);
        out.endObject();
      }
      out.endArray();
      if (!table.constraints.isEmpty()) {
        out.comma();
        out.name("constraints");
        out.beginObject();
        out.name("notNull");
        emitStringList(out, table.constraints.notNull);
        if (!table.constraints.primaryKey.isEmpty()) {
          out.comma();
          out.name("primaryKey");
          emitStringList(out, table.constraints.primaryKey);
        }
        if (!table.constraints.unique.isEmpty()) {
          out.comma();
          out.name("unique");
          out.beginArray();
          for (int constraintIndex = 0;
              constraintIndex < table.constraints.unique.size();
              constraintIndex++) {
            if (constraintIndex > 0) {
              out.comma();
            }
            UniqueConstraintDef constraint = table.constraints.unique.get(constraintIndex);
            out.beginObject();
            if (constraint.name != null) {
              out.name("name").value(constraint.name);
              out.comma();
            }
            out.name("columns");
            emitStringList(out, constraint.columns);
            out.endObject();
          }
          out.endArray();
        }
        if (!table.constraints.foreignKeys.isEmpty()) {
          out.comma();
          out.name("foreignKeys");
          out.beginArray();
          for (int constraintIndex = 0;
              constraintIndex < table.constraints.foreignKeys.size();
              constraintIndex++) {
            if (constraintIndex > 0) {
              out.comma();
            }
            ForeignKeyDef constraint = table.constraints.foreignKeys.get(constraintIndex);
            out.beginObject();
            if (constraint.name != null) {
              out.name("name").value(constraint.name);
              out.comma();
            }
            out.name("columns");
            emitStringList(out, constraint.columns);
            out.comma();
            out.name("referencedTable").value(constraint.referencedTable);
            out.comma();
            out.name("referencedColumns");
            emitStringList(out, constraint.referencedColumns);
            out.comma();
            out.name("matchType").value("simple");
            if (constraint.referentialActions != null) {
              out.comma();
              out.name("referentialActions").value(constraint.referentialActions);
            }
            out.endObject();
          }
          out.endArray();
        }
        if (!table.constraints.checks.isEmpty()) {
          out.comma();
          out.name("checks");
          out.beginArray();
          for (int constraintIndex = 0;
              constraintIndex < table.constraints.checks.size();
              constraintIndex++) {
            if (constraintIndex > 0) {
              out.comma();
            }
            CheckDef constraint = table.constraints.checks.get(constraintIndex);
            out.beginObject();
            if (constraint.name != null) {
              out.name("name").value(constraint.name);
              out.comma();
            }
            out.name("expression").value(constraint.expression);
            out.endObject();
          }
          out.endArray();
        }
        if (!table.constraints.uniqueIndexes.isEmpty()) {
          out.comma();
          out.name("uniqueIndexes");
          out.beginArray();
          for (int constraintIndex = 0;
              constraintIndex < table.constraints.uniqueIndexes.size();
              constraintIndex++) {
            if (constraintIndex > 0) {
              out.comma();
            }
            UniqueIndexDef constraint = table.constraints.uniqueIndexes.get(constraintIndex);
            out.beginObject();
            if (constraint.name != null) {
              out.name("name").value(constraint.name);
              out.comma();
            }
            out.name("terms");
            out.beginArray();
            for (int termIndex = 0; termIndex < constraint.terms.size(); termIndex++) {
              if (termIndex > 0) {
                out.comma();
              }
              out.value(constraint.terms.get(termIndex).sourceSql);
            }
            out.endArray();
            if (constraint.predicate != null) {
              out.comma();
              out.name("predicate").value(constraint.predicateSql);
            }
            out.endObject();
          }
          out.endArray();
        }
        out.endObject();
      }
      out.endObject();
    }
    out.endArray();
  }

  private static void emitStringList(Json out, List<String> values) {
    out.beginArray();
    for (int i = 0; i < values.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      out.value(values.get(i));
    }
    out.endArray();
  }

  private static void emitRelNode(Json out, RelNode rel, SourceContext source) {
    emitRelNode(out, rel, source, false);
  }

  private static void emitRelNode(
      Json out, RelNode rel, SourceContext source, boolean syntheticRootOutputProject) {
    SqlNode sourceSql = source.node();
    SqlSelect sourceQueryBlock = topLevelSelect(sourceSql);
    String sourceQueryBlockId = sourceRelQueryBlockId(sourceSql, source.sourcePositions());
    if (sourceQueryBlockId == null
        && rel instanceof Join
        && sourceSql != null
        && stripAlias(sourceSql) instanceof SqlJoin) {
      // A Join's exact source node lives inside FROM rather than being a
      // SqlSelect itself. Retain the owning block solely when traversal has
      // carried that independently parsed identity to this Join.
      sourceQueryBlockId = source.queryBlockId();
    }
    SqlNode relationalSourceSql = sourceSql;
    if (rel instanceof Join && sourceQueryBlock != null) {
      SqlNode from = stripAlias(sourceQueryBlock.getFrom());
      if (from instanceof SqlJoin) {
        relationalSourceSql = from;
      }
    }
    out.beginObject();
    out.name("type").value(rel.getRelTypeName());
    out.comma();
    out.name("rowType");
    emitRowType(out, rel.getRowType());
    emitCorrelationMetadata(out, rel);
    if (relationalSourceSql != null) {
      out.comma();
      out.name("sourceSql").value(relationalSourceSql.toString());
      out.comma();
      out.name("sourceKind").value(relationalSourceSql.getKind().name());
      if (relationalSourceSql instanceof SqlCall sourceCall) {
        out.comma();
        out.name("sourceOperator").value(sourceCall.getOperator().getName());
      }
    }
    emitExactRelSourceBinding(out, source.sourcePositions(), relationalSourceSql);
    if (sourceQueryBlockId != null) {
      out.comma();
      out.name("sourceQueryBlockId").value(sourceQueryBlockId);
    }
    if (source.rootQueryBlockId() != null) {
      out.comma();
      out.name("sourceRootQueryBlockId").value(source.rootQueryBlockId());
    }

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
      SourceTableBinding tableBinding = sourceTableBinding(scan, source);
      if (tableBinding == null || source.sourcePositions() == null) {
        throw new UnsupportedOperationException(
            "missing exact declarative source relation for LogicalTableScan");
      }
      ExactSourceIdentity relationIdentity = exactSourceIdentity(
          source.sourcePositions(), tableBinding.relation(), "table relation");
      ExactSourceIdentity tableIdentity = exactSourceIdentity(
          source.sourcePositions(), tableBinding.table(), "table identifier");
      ExactSourceIdentity aliasIdentity = tableBinding.alias() == null
          ? null
          : exactSourceIdentity(
              source.sourcePositions(), tableBinding.alias(), "table alias");
      out.comma();
      out.name("sourceTable");
      out.beginObject();
      out.name("kind").value("DIRECT_BASE_TABLE");
      out.comma();
      out.name("queryBlockId").value(source.queryBlockId());
      out.comma();
      out.name("relationOccurrenceId").value(relationIdentity.nodeId());
      out.comma();
      out.name("relationNodeId").value(relationIdentity.nodeId());
      out.comma();
      out.name("relationText").value(relationIdentity.text());
      out.comma();
      out.name("tableNodeId").value(tableIdentity.nodeId());
      out.comma();
      out.name("tableText").value(tableIdentity.text());
      out.comma();
      out.name("tableNames");
      emitIdentifierNames(out, tableBinding.table());
      out.comma();
      out.name("tableQuoted");
      emitIdentifierQuoted(out, tableBinding.table(), source.sourcePositions());
      if (aliasIdentity != null) {
        out.comma();
        out.name("aliasNodeId").value(aliasIdentity.nodeId());
        out.comma();
        out.name("aliasText").value(aliasIdentity.text());
        out.comma();
        out.name("aliasNames");
        emitIdentifierNames(out, tableBinding.alias());
        out.comma();
        out.name("aliasQuoted");
        emitIdentifierQuoted(out, tableBinding.alias(), source.sourcePositions());
      }
      emitSourceTableColumnLineage(
          out, scan, tableBinding.source(), relationIdentity, source.sourcePositions());
      out.endObject();
    } else if (rel instanceof Project project) {
      out.comma();
      out.name("projectRex");
      out.beginArray();
      List<SqlNode> sourceProjects = List.of();
      List<SqlNode> sourceProjectRoles = List.of();
      if (!syntheticRootOutputProject) {
        sourceProjectRoles = topLevelSelectItemRoles(sourceSql);
        sourceProjects = topLevelSelectItems(sourceSql);
        if (sourceProjects.isEmpty()) {
          // A child of the exact VALUES-to-UNION mapping owns one source ROW,
          // not a SELECT list. Recover that row's positional expressions.
          List<List<SqlNode>> sourceRows = sourceValueRows(sourceSql);
          if (sourceRows.size() == 1) {
            sourceProjects = sourceRows.get(0);
            sourceProjectRoles = sourceProjects;
          }
        }
        if (sourceProjects.isEmpty()) {
          sourceProjects = sourceSelectItemsForHiddenOrder(project, sourceSql);
          sourceProjectRoles = topLevelSelectItemRoles(sourceSql);
        }
        List<AggregateInputSource> aggregateBindings =
            aggregateInputSources(sourceSql, source);
        List<SqlNode> aggregateInputs = new ArrayList<>();
        List<SqlNode> aggregateRoles = new ArrayList<>();
        for (AggregateInputSource binding : aggregateBindings) {
          aggregateInputs.add(binding.definition());
          aggregateRoles.add(binding.role());
        }
        if (source.clausePhase() == SourceClausePhase.PRE_AGGREGATE
            && aggregateInputs.size() == project.getProjects().size()) {
          sourceProjects = aggregateInputs;
          sourceProjectRoles = aggregateRoles;
        } else if (sourceProjects.size() < project.getProjects().size()
            && sourceSelectPrefixMatchesProject(
                project, sourceSql, sourceProjects.size(), source.sourcePositions())) {
          // SqlToRel appends hidden ORDER BY helpers after the visible SELECT
          // outputs.  Keep exact provenance for the visible prefix instead of
          // discarding every source expression merely because those helpers
          // increase the generated Project arity.  The unmatched helpers stay
          // source-less unless every hidden expression is bound below to one
          // exact independently parsed ORDER BY expression.
          List<SqlNode> visiblePrefix = new ArrayList<>(sourceProjects);
          List<SqlNode> visibleRoles = new ArrayList<>(sourceProjectRoles);
          List<SqlNode> hiddenOrderExpressions = sourceHiddenOrderProjectExpressions(
              project, sourceSql, sourceProjects.size(), source.sourcePositions());
          if (hiddenOrderExpressions.size()
              == project.getProjects().size() - sourceProjects.size()) {
            visiblePrefix.addAll(hiddenOrderExpressions);
            visibleRoles.addAll(hiddenOrderExpressions);
          } else {
            while (visiblePrefix.size() < project.getProjects().size()) {
              visiblePrefix.add(null);
              visibleRoles.add(null);
            }
          }
          sourceProjects = visiblePrefix;
          sourceProjectRoles = visibleRoles;
        } else if (sourceProjects.size() != project.getProjects().size()) {
          sourceProjects = aggregateInputs;
          sourceProjectRoles = aggregateRoles;
        }
        if (sourceProjects.size() != project.getProjects().size()) {
          sourceProjects = List.of();
          sourceProjectRoles = List.of();
        }
      }
      for (int i = 0; i < project.getProjects().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        SqlNode sourceProject = i < sourceProjects.size() ? sourceProjects.get(i) : null;
        SqlNode sourceProjectRole =
            i < sourceProjectRoles.size() ? sourceProjectRoles.get(i) : null;
        if (sourceProjectRole instanceof SqlIdentifier identifier && identifier.isStar()) {
          // `*` is a relational SELECT-list expansion, not a scalar column
          // identifier.  In the one-column case Calcite happens to produce
          // one RexInputRef, but attaching its pseudo-name [""] would make
          // that cardinality accident look like source scalar authority.  The
          // importer closes wildcard arity, order, qualifier, and typed input
          // positions against the exact SELECT list at the Project boundary.
          sourceProject = null;
          sourceProjectRole = null;
        }
        sourceProject = exactProjectedLiteralSource(
            project.getProjects().get(i), sourceProject, source);
        SourceProjectedExpansion sourceExpansion = null;
        if (sourceProject != null && sourceProjectRole != null) {
          ProjectedSourceResolution resolution = exactProjectedDescendantSource(
              project.getProjects().get(i), sourceProjectRole, source);
          if (resolution.expansion() == null
              && source.clausePhase() == SourceClausePhase.PRE_AGGREGATE
              && sourceProjectRole instanceof SqlIdentifier reference) {
            SourceProjectedExpansion groupInputCarrier = directDerivedProjectedExpansion(
                project.getProjects().get(i), reference,
                topLevelSelect(source.recoveryRoot()), source, true);
            if (groupInputCarrier != null) {
              resolution = new ProjectedSourceResolution(
                  groupInputCarrier.definition(), groupInputCarrier, null);
            }
          }
          if (resolution.expansion() == null
              && project.getProjects().get(i) instanceof RexInputRef inputRef
              && sourceProjectRole instanceof SqlIdentifier reference
              && inputRef.getIndex() >= 0
              && inputRef.getIndex() < project.getInput().getRowType().getFieldCount()
              && inputRef.getType().equals(
                  project.getInput().getRowType().getFieldList().get(inputRef.getIndex()).getType())
              && inputRef.getType().equals(
                  project.getRowType().getFieldList().get(i).getType())) {
            // A normal Project over one direct derived SELECT can retain the
            // exact inner definition on a positional RexInputRef (not only
            // on Calcite's pre-Aggregate carrier).  Preserve both the outer
            // public reference and inner definition.  The Rust importer
            // independently proves this exact expansion and binds the index
            // through the complete child relation, so a same-typed swap is
            // still rejected.
            SourceProjectedExpansion directCarrier = directDerivedProjectedExpansion(
                project.getProjects().get(i), reference,
                topLevelSelect(source.recoveryRoot()), source, true);
            if (directCarrier != null) {
              resolution = new ProjectedSourceResolution(
                  directCarrier.definition(), directCarrier, null);
            }
          }
          if (resolution.expansion() == null
              && project.getInput() instanceof Aggregate aggregateInput
              && project.getProjects().get(i) instanceof RexInputRef inputRef
              && inputRef.getIndex() < aggregateInput.getGroupSet().cardinality()
              && sourceProjectRole instanceof SqlIdentifier reference) {
            SourceProjectedExpansion groupCarrier = directDerivedProjectedExpansion(
                project.getProjects().get(i), reference,
                topLevelSelect(source.recoveryRoot()), source, true);
            if (groupCarrier != null) {
              resolution = new ProjectedSourceResolution(
                  groupCarrier.definition(), groupCarrier, null);
            }
          }
          boolean exactCrossScopeReference = resolution.matchedDefinition() != null
              && resolution.source() == sourceProjectRole
              && resolution.matchedDefinition() == sourceProject;
          SourceCteUse directProjectCteUse = project.getInputs().size() == 1
              ? sourceCteUseForRelInput(
                  project, source, sourceForRelInput(project, source, 0), 0)
              : null;
          boolean exactCteExpansion = resolution.expansion() != null
              && resolution.expansion().cteUse() != null
              && resolution.source() == resolution.expansion().definition()
              && resolution.expansion().reference() == sourceProjectRole
              && directProjectCteUse != null
              && directProjectCteUse.reference()
                  == resolution.expansion().cteUse().reference()
              && directProjectCteUse.definitionQuery()
                  == resolution.expansion().cteUse().definitionQuery();
          boolean attachResolution = resolution.expansion() != null
                  && resolution.expansion().cteUse() != null
              ? exactCteExpansion
              : resolution.source() != null
                  && (resolution.source().toString().equals(sourceProject.toString())
                      || exactCrossScopeReference);
          if (resolution.source() != null && attachResolution) {
            sourceProject = resolution.source();
            sourceExpansion = resolution.expansion();
          }
        }
        SourceContext projectSource = syntheticRootOutputProject
            ? SourceContext.empty()
            : source.withNode(sourceProject).withDirectProjectedOperandExpansion();
        emitRexNode(out, project.getProjects().get(i), projectSource, sourceExpansion);
      }
      out.endArray();
    } else if (rel instanceof Filter filter) {
      String sourceClause = sourceFilterClause(filter, source);
      SourceWhereAttestation sourceWhere = sourceWhereAttestation(filter, source);
      SourceNativeHavingAttestation nativeHaving =
          sourceNativeHavingAttestation(filter, source);
      if (sourceClause != null && sourceQueryBlockId != null) {
        out.comma();
        out.name("sourceClause").value(sourceClause);
      }
      if (sourceWhere != null) {
        out.comma();
        out.name("sourceWhere");
        out.beginObject();
        out.name("kind").value("WHERE");
        out.comma();
        out.name("queryBlockId").value(sourceWhere.queryBlockId());
        out.comma();
        out.name("ownerNodeId").value(sourceWhere.ownerNodeId());
        out.comma();
        out.name("sourceConditionNodeId").value(sourceWhere.sourceConditionNodeId());
        out.comma();
        out.name("sourceConditionSql").value(sourceWhere.sourceConditionSql());
        out.comma();
        out.name("sourceConditionKind").value(sourceWhere.sourceConditionKind());
        if (sourceWhere.sourceConditionOperator() != null) {
          out.comma();
          out.name("sourceConditionOperator").value(sourceWhere.sourceConditionOperator());
        }
        out.comma();
        out.name("generatedConditionSql").value(sourceWhere.generatedConditionSql());
        out.comma();
        out.name("filterOutputArity").value(sourceWhere.filterOutputArity());
        out.comma();
        out.name("inputOutputArity").value(sourceWhere.inputOutputArity());
        out.comma();
        out.name("variablesSet");
        out.beginArray();
        for (int i = 0; i < sourceWhere.variablesSet().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          out.value(sourceWhere.variablesSet().get(i));
        }
        out.endArray();
        out.comma();
        out.name("inputBindings");
        out.beginArray();
        for (int i = 0; i < sourceWhere.inputBindings().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          SourceWhereInputBinding binding = sourceWhere.inputBindings().get(i);
          out.beginObject();
          out.name("path").value(binding.path());
          out.comma();
          out.name("inputIndex").value(binding.inputIndex());
          out.comma();
          out.name("sourceSql").value(binding.sourceSql());
          out.comma();
          out.name("sourceRelationNodeId").value(binding.sourceRelationNodeId());
          out.comma();
          out.name("sourceRelationSql").value(binding.sourceRelationSql());
          out.comma();
          out.name("baseTable");
          out.beginArray();
          for (int j = 0; j < binding.baseTable().size(); j++) {
            if (j > 0) {
              out.comma();
            }
            out.value(binding.baseTable().get(j));
          }
          out.endArray();
          out.comma();
          out.name("tableFieldIndex").value(binding.tableFieldIndex());
          out.comma();
          out.name("baseFieldName").value(binding.baseFieldName());
          out.comma();
          out.name("generatedFieldName").value(binding.generatedFieldName());
          out.endObject();
        }
        out.endArray();
        out.comma();
        out.name("analysisErrors");
        out.beginArray();
        for (int i = 0; i < sourceWhere.analysisErrors().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          SourceWhereAnalysisErrorBinding binding = sourceWhere.analysisErrors().get(i);
          out.beginObject();
          out.name("kind").value(binding.kind());
          out.comma();
          out.name("rexPath").value(binding.rexPath());
          out.comma();
          out.name("identifierOperand").value(binding.identifierOperand());
          out.comma();
          out.name("literalOperand").value(binding.literalOperand());
          out.comma();
          out.name("generatedComparisonSql").value(binding.generatedComparisonSql());
          out.comma();
          out.name("inputIndex").value(binding.inputIndex());
          out.comma();
          out.name("baseTable");
          out.beginArray();
          for (int j = 0; j < binding.baseTable().size(); j++) {
            if (j > 0) {
              out.comma();
            }
            out.value(binding.baseTable().get(j));
          }
          out.endArray();
          out.comma();
          out.name("tableFieldIndex").value(binding.tableFieldIndex());
          out.comma();
          out.name("baseFieldName").value(binding.baseFieldName());
          out.comma();
          out.name("sourceLiteralCanonicalValue")
              .value(binding.sourceLiteralCanonicalValue());
          out.comma();
          out.name("generatedLiteralCanonicalValue")
              .value(binding.generatedLiteralCanonicalValue());
          out.endObject();
        }
        out.endArray();
        out.endObject();
      }
      if (nativeHaving != null) {
        out.comma();
        out.name("sourceNativeHaving");
        out.beginObject();
        out.name("kind").value(nativeHaving.kind());
        out.comma();
        out.name("queryBlockId").value(nativeHaving.queryBlockId());
        out.comma();
        out.name("ownerNodeId").value(nativeHaving.ownerNodeId());
        out.comma();
        out.name("sourceOwnerSql").value(nativeHaving.sourceOwnerSql());
        out.comma();
        out.name("sourceOwnerText").value(nativeHaving.sourceOwnerText());
        out.comma();
        out.name("sourceSelectSql").value(nativeHaving.sourceSelectSql());
        out.comma();
        out.name("sourceSelectText").value(nativeHaving.sourceSelectText());
        out.comma();
        out.name("sourceConditionNodeId").value(nativeHaving.sourceConditionNodeId());
        out.comma();
        out.name("sourceConditionSql").value(nativeHaving.sourceConditionSql());
        out.comma();
        out.name("sourceConditionText").value(nativeHaving.sourceConditionText());
        out.comma();
        out.name("generatedConditionSql").value(nativeHaving.generatedConditionSql());
        out.comma();
        out.name("aggregateOutputArity").value(nativeHaving.aggregateOutputArity());
        out.comma();
        out.name("aggregateCallCount").value(nativeHaving.aggregateCallCount());
        out.comma();
        out.name("operandBindings");
        out.beginArray();
        for (int i = 0; i < nativeHaving.operandBindings().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          SourceNativeHavingOperandBinding binding = nativeHaving.operandBindings().get(i);
          out.beginObject();
          out.name("path").value(binding.path());
          out.comma();
          out.name("aggregateOutputIndex").value(binding.aggregateOutputIndex());
          out.comma();
          out.name("sourceSql").value(binding.sourceSql());
          out.comma();
          out.name("sourceKind").value(binding.sourceKind());
          if (binding.sourceOperator() != null) {
            out.comma();
            out.name("sourceOperator").value(binding.sourceOperator());
          }
          out.endObject();
        }
        out.endArray();
        out.endObject();
      }
      out.comma();
      out.name("conditionRex");
      emitRexNode(out, filter.getCondition(), source.withNode(sourceFilterCondition(filter, source)));
    } else if (rel instanceof Join join) {
      out.comma();
      out.name("joinType").value(join.getJoinType().name());
      String sourceJoinType = sourceWhereJoinType(sourceSql);
      if (sourceJoinType != null) {
        out.comma();
        out.name("sourceJoinType").value(sourceJoinType);
      }
      String sourceJoinSyntax = sourceWhereJoinSyntax(sourceSql);
      if (sourceJoinSyntax != null) {
        SqlJoin sourceJoin = sourceWhereJoin(sourceSql);
        ExactSourceIdentity syntaxIdentity = source.sourcePositions() == null
            ? null
            : source.sourcePositions().joinSyntaxIdentity(sourceJoin);
        if (syntaxIdentity == null) {
          throw new UnsupportedOperationException(
              "missing exact parsed join-syntax source identity");
        }
        out.comma();
        out.name("sourceJoinSyntax").value(sourceJoinSyntax);
        out.comma();
        out.name("sourceJoinSyntaxNodeId").value(syntaxIdentity.nodeId());
        out.comma();
        out.name("sourceJoinSyntaxText").value(syntaxIdentity.text());
        ExactSourceIdentity leftIdentity = exactSourceRelationExtent(
            source.sourcePositions(), sourceJoin.getLeft(), "join left input");
        ExactSourceIdentity rightIdentity = exactSourceRelationExtent(
            source.sourcePositions(), sourceJoin.getRight(), "join right input");
        SqlNode sourceCondition = sourceJoin.getCondition();
        ExactSourceIdentity conditionIdentity = sourceCondition == null
            ? null
            : exactSourceIdentity(
                source.sourcePositions(), sourceCondition, "join condition");
        ExactSourceIdentity joinIdentity = exactSourceRelationExtent(
            source.sourcePositions(), sourceJoin, "join expression");
        out.comma();
        out.name("sourceJoin");
        out.beginObject();
        out.name("kind").value("DIRECT_JOIN");
        out.comma();
        out.name("queryBlockId").value(source.queryBlockId());
        out.comma();
        out.name("joinNodeId").value(joinIdentity.nodeId());
        out.comma();
        out.name("joinText").value(joinIdentity.text());
        out.comma();
        out.name("leftNodeId").value(leftIdentity.nodeId());
        out.comma();
        out.name("leftText").value(leftIdentity.text());
        out.comma();
        out.name("rightNodeId").value(rightIdentity.nodeId());
        out.comma();
        out.name("rightText").value(rightIdentity.text());
        out.comma();
        out.name("conditionType").value(sourceJoin.getConditionType().name());
        if (conditionIdentity != null) {
          out.comma();
          out.name("conditionNodeId").value(conditionIdentity.nodeId());
          out.comma();
          out.name("conditionText").value(conditionIdentity.text());
        }
        SourceCteUse leftCteUse = sourceCteUse(sourceJoin.getLeft(), source);
        SourceCteUse rightCteUse = sourceCteUse(sourceJoin.getRight(), source);
        if (leftCteUse != null) {
          out.comma();
          out.name("leftCteUse");
          emitSourceCteUse(out, leftCteUse, source.sourcePositions());
        }
        if (rightCteUse != null) {
          out.comma();
          out.name("rightCteUse");
          emitSourceCteUse(out, rightCteUse, source.sourcePositions());
        }
        out.endObject();
      }
      out.comma();
      out.name("conditionRex");
      emitRexNode(out, join.getCondition(), source.withNode(topLevelJoinCondition(sourceSql)));
    } else if (rel instanceof Aggregate aggregate) {
      SourceDistinctAttestation sourceDistinct =
          sourceDistinctAttestation(aggregate, source);
      if (sourceDistinct != null) {
        out.comma();
        out.name("sourceDistinct");
        out.beginObject();
        out.name("kind").value(sourceDistinct.kind());
        out.comma();
        out.name("queryBlockId").value(sourceDistinct.queryBlockId());
        out.comma();
        out.name("sourceSelectNodeId").value(sourceDistinct.sourceSelectNodeId());
        out.comma();
        out.name("sourceSelectText").value(sourceDistinct.sourceSelectText());
        out.comma();
        out.name("groupIndexes");
        emitIntegerList(out, sourceDistinct.groupIndexes());
        out.comma();
        out.name("groupingSets");
        out.beginArray();
        for (int i = 0; i < sourceDistinct.groupingSets().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          emitIntegerList(out, sourceDistinct.groupingSets().get(i));
        }
        out.endArray();
        out.comma();
        out.name("inputOutputArity").value(sourceDistinct.inputOutputArity());
        out.comma();
        out.name("outputArity").value(sourceDistinct.outputArity());
        out.endObject();
      }
      SourceGroupingAttestation sourceGrouping =
          sourceGroupingAttestation(aggregate, source);
      if (sourceGrouping != null) {
        out.comma();
        out.name("sourceGrouping");
        out.beginObject();
        out.name("kind").value(sourceGrouping.kind());
        out.comma();
        out.name("queryBlockId").value(sourceGrouping.queryBlockId());
        out.comma();
        out.name("sourceSelectNodeId").value(sourceGrouping.sourceSelectNodeId());
        out.comma();
        out.name("sourceSelectText").value(sourceGrouping.sourceSelectText());
        out.comma();
        out.name("sourceSelectSql").value(sourceGrouping.sourceSelectSql());
        out.comma();
        out.name("sourceGroupNodeId").value(sourceGrouping.sourceGroupNodeId());
        out.comma();
        out.name("sourceGroupText").value(sourceGrouping.sourceGroupText());
        out.comma();
        out.name("sourceGroupSql").value(sourceGrouping.sourceGroupSql());
        out.comma();
        out.name("groupIndexes");
        emitIntegerList(out, sourceGrouping.groupIndexes());
        out.comma();
        out.name("groupingSets");
        out.beginArray();
        for (int i = 0; i < sourceGrouping.groupingSets().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          emitIntegerList(out, sourceGrouping.groupingSets().get(i));
        }
        out.endArray();
        out.comma();
        out.name("sourceOperandIndexes");
        out.beginArray();
        for (int i = 0; i < sourceGrouping.sourceOperandIndexes().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          emitIntegerList(out, sourceGrouping.sourceOperandIndexes().get(i));
        }
        out.endArray();
        out.comma();
        out.name("sourceOperands");
        out.beginArray();
        for (int i = 0; i < sourceGrouping.sourceOperands().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          out.beginArray();
          List<SqlNode> sourceSet = sourceGrouping.sourceOperands().get(i);
          for (int j = 0; j < sourceSet.size(); j++) {
            if (j > 0) {
              out.comma();
            }
            emitSourceNodeProvenance(out, sourceSet.get(j), source.sourcePositions());
          }
          out.endArray();
        }
        out.endArray();
        out.comma();
        out.name("sourceHasWhere").value(sourceGrouping.sourceHasWhere());
        out.comma();
        out.name("sourceHasHaving").value(sourceGrouping.sourceHasHaving());
        out.endObject();
      }
      out.comma();
      out.name("groupSet");
      emitIntegerList(out, aggregate.getGroupSet().asList());
      out.comma();
      out.name("groupSets");
      out.beginArray();
      var groupSets = aggregate.getGroupSets();
      for (int i = 0; i < groupSets.size(); i++) {
        if (i > 0) {
          out.comma();
        }
        emitIntegerList(out, groupSets.get(i).asList());
      }
      out.endArray();
      List<Integer> sourceGroupIndexes = sourceWhereAggregateGroupIndexes(aggregate, sourceSql);
      if (sourceGroupIndexes != null) {
        out.comma();
        out.name("sourceGroupIndexes");
        out.beginArray();
        for (int i = 0; i < sourceGroupIndexes.size(); i++) {
          if (i > 0) {
            out.comma();
          }
          out.value(sourceGroupIndexes.get(i));
        }
        out.endArray();
        out.comma();
        out.name("sourceGroupingSets");
        out.beginArray();
        out.beginArray();
        for (int i = 0; i < sourceGroupIndexes.size(); i++) {
          if (i > 0) {
            out.comma();
          }
          out.value(sourceGroupIndexes.get(i));
        }
        out.endArray();
        out.endArray();
      }
      out.comma();
      out.name("aggCallDetails");
      out.beginArray();
      List<SqlCall> sourceAggregateCalls = alignedSourceAggregateCalls(aggregate, sourceSql);
      if (sourceAggregateCalls == null) {
        sourceAggregateCalls = List.of();
      }
      for (int i = 0; i < aggregate.getAggCallList().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        SqlCall sourceAggregate =
            i < sourceAggregateCalls.size() ? sourceAggregateCalls.get(i) : null;
        emitAggregateCall(
            out, aggregate.getAggCallList().get(i), sourceAggregate,
            source.sourcePositions());
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
      SourceOrderAttestation sourceOrder = sourceOrderAttestation(sort, source);
      if (sourceOrder != null) {
        out.comma();
        out.name("sourceOrder");
        out.beginObject();
        out.name("kind").value("ORDER_BY");
        out.comma();
        out.name("queryNodeId").value(sourceOrder.query().nodeId());
        out.comma();
        out.name("queryText").value(sourceOrder.query().text());
        out.comma();
        out.name("orderListNodeId").value(sourceOrder.orderList().nodeId());
        out.comma();
        out.name("orderListText").value(sourceOrder.orderList().text());
        out.comma();
        out.name("items");
        out.beginArray();
        for (int i = 0; i < sourceOrder.items().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          SourceOrderItemAttestation item = sourceOrder.items().get(i);
          out.beginObject();
          out.name("itemNodeId").value(item.item().nodeId());
          out.comma();
          out.name("itemText").value(item.item().text());
          out.comma();
          out.name("expressionNodeId").value(item.expression().nodeId());
          out.comma();
          out.name("expressionText").value(item.expression().text());
          out.endObject();
        }
        out.endArray();
        out.endObject();
      }
      if (sort.fetch != null) {
        out.comma();
        out.name("fetchRex");
        SqlNode sourceFetch = sourceSql instanceof SqlOrderBy orderBy
            ? orderBy.fetch
            : sourceQueryBlock == null ? null : sourceQueryBlock.getFetch();
        emitRexNode(out, sort.fetch, source.withNode(sourceFetch));
      }
      if (sort.offset != null) {
        out.comma();
        out.name("offsetRex");
        SqlNode sourceOffset = sourceSql instanceof SqlOrderBy orderBy
            ? orderBy.offset
            : sourceQueryBlock == null ? null : sourceQueryBlock.getOffset();
        emitRexNode(out, sort.offset, source.withNode(sourceOffset));
      }
    } else if (rel instanceof Values values) {
      out.comma();
      out.name("tuples");
      out.beginArray();
      List<List<SqlNode>> sourceRows = sourceValueRows(sourceSql);
      if (sourceRows.size() != values.getTuples().size()) {
        sourceRows = List.of();
      }
      for (int i = 0; i < values.getTuples().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        out.beginArray();
        var tuple = values.getTuples().get(i);
        List<SqlNode> sourceRow = i < sourceRows.size() ? sourceRows.get(i) : List.of();
        for (int j = 0; j < tuple.size(); j++) {
          if (j > 0) {
            out.comma();
          }
          SqlNode sourceValue = j < sourceRow.size() ? sourceRow.get(j) : null;
          emitRexNode(out, tuple.get(j), source.withNode(sourceValue));
        }
        out.endArray();
      }
      out.endArray();
    }

    out.comma();
    List<SourceContext> inputSources = new ArrayList<>();
    List<SourceCteUse> inputCteUses = new ArrayList<>();
    List<RelNode> inputs = rel.getInputs();
    boolean hasInputCteUse = false;
    for (int i = 0; i < inputs.size(); i++) {
      SourceContext inputSource = syntheticRootOutputProject
          ? source
          : sourceForRelInput(rel, source, i);
      SourceCteUse inputCteUse = syntheticRootOutputProject
          ? null
          : sourceCteUseForRelInput(rel, source, inputSource, i);
      inputSources.add(inputSource);
      inputCteUses.add(inputCteUse);
      hasInputCteUse |= inputCteUse != null;
    }
    if (hasInputCteUse) {
      out.name("sourceInputCteUses");
      out.beginArray();
      for (int i = 0; i < inputCteUses.size(); i++) {
        if (i > 0) {
          out.comma();
        }
        SourceCteUse use = inputCteUses.get(i);
        if (use == null) {
          out.nullValue();
        } else {
          emitSourceCteUse(out, use, source.sourcePositions());
        }
      }
      out.endArray();
      out.comma();
    }
    out.name("inputs");
    out.beginArray();
    for (int i = 0; i < inputs.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      emitRelNode(out, inputs.get(i), inputSources.get(i));
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
    emitRexNode(out, rex, SourceContext.empty());
  }

  private static void emitRexNode(Json out, RexNode rex, SourceContext source) {
    emitRexNode(out, rex, source, null);
  }

  private static void emitRexNode(
      Json out, RexNode rex, SourceContext source,
      SourceProjectedExpansion sourceExpansion) {
    SqlNode sourceSql = source.node();
    if (rex == null) {
      out.nullValue();
      return;
    }

    if (sourceSql == null && source.allowLiteralRecovery() && rex instanceof RexCall call) {
      sourceSql = uniqueStringConcatSource(call, source.literalUniverse());
    }
    if (sourceSql == null && source.allowLiteralRecovery() && rex instanceof RexLiteral literal) {
      sourceSql = literal.getTypeName() == SqlTypeName.NULL
          ? uniqueNullLiteralSource(source.recoveryRoot())
          : uniqueCharacterLiteralSource(literal, source.recoveryRoot());
      if (sourceSql == null && source.literalUniverse() != source.recoveryRoot()) {
        // Rel conversion can pull CTE and set-operation branches through
        // validator-generated Projects, losing the local SqlNode association.
        // A query-wide fallback is sound only when every source candidate
        // matching the Rex payload has the same parsed SQL expression; the
        // recovery helpers reject any semantic ambiguity.
        sourceSql = literal.getTypeName() == SqlTypeName.NULL
            ? uniqueNullLiteralSourceAcrossQuery(source.literalUniverse())
            : uniqueCharacterLiteralSourceAcrossQuery(literal, source.literalUniverse());
      }
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
      emitExactSourceBinding(out, source.sourcePositions(), sourceSql);
      out.comma();
      out.name("sourceKind").value(sourceSql.getKind().name());
      if (sourceSql instanceof SqlCall sourceCall) {
        out.comma();
        out.name("sourceOperator").value(sourceCall.getOperator().getName());
      }
      if (sourceSql instanceof SqlIdentifier sourceIdentifier) {
        emitSourceIdentifierMetadata(out, sourceIdentifier, source.sourcePositions());
      }
      String sourceWindowFunction = sourceWindowFunction(sourceSql);
      if (sourceWindowFunction != null) {
        out.comma();
        out.name("sourceWindowFunction").value(sourceWindowFunction);
      }
    }
    if (sourceExpansion != null) {
      emitSourceProjectedExpansion(out, sourceExpansion, source);
    }
    if (hasUnsupportedCollapsedSourceCast(rex, sourceSql, source.sourcePositions())) {
      throw new UnsupportedOperationException(
          "Calcite collapsed a source-explicit nonliteral CAST into a non-CAST Rex root");
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
      emitRexCallFields(out, subQuery, source);
      SqlNode nestedSource = subquerySource(sourceSql);
      SourceInSubqueryOrderAttestation lostOrder =
          sourceInSubqueryOrderAttestation(
              subQuery, sourceSql, source.sourcePositions());
      SqlNode nestedRelNode = lostOrder == null
          ? nestedSource
          : ((SqlOrderBy) nestedSource).query;
      // A scalar/IN subquery can reference a CTE defined by an enclosing
      // WITH.  Starting a fresh context here discards that lexical CTE
      // environment and the independently parsed statement-wide literal
      // universe.  Calcite then inlines the CTE, and its generated coercion
      // Rex nodes become indistinguishable from source-written casts.  Enter
      // the exact nested source node through the existing context instead:
      // CteProvenanceScopes has indexed that node with precisely the visible
      // preceding CTEs, while nestedRoot also establishes the nested query's
      // own clause phase and literal-recovery root.
      SourceContext nestedRelSource = source.nestedRoot(nestedRelNode);
      SourceRelCorrespondence sourceRelCorrespondence = nestedSource == null
          ? null
          : sourceSubqueryRelCorrespondence(subQuery.rel, nestedRelSource);
      if (nestedSource != null && sourceRelCorrespondence == null) {
        throw new UnsupportedOperationException(
            "source subquery has no complete compositional relational correspondence");
      }
      if (lostOrder != null) {
        out.comma();
        out.name("sourceInSubqueryOrder");
        emitSourceInSubqueryOrderAttestation(out, lostOrder);
      }
      if (sourceRelCorrespondence != null) {
        out.comma();
        out.name("sourceRelCorrespondence");
        emitSourceRelCorrespondence(out, sourceRelCorrespondence);
      }
      out.comma();
      out.name("subqueryRel");
      emitRelNode(out, subQuery.rel, nestedRelSource);
    } else if (rex instanceof RexOver over) {
      emitRexCallFields(out, over, source);
      out.comma();
      out.name("window");
      emitRexWindow(out, over.getWindow(), source);
      out.comma();
      out.name("distinct").value(over.isDistinct());
      out.comma();
      out.name("ignoreNulls").value(over.ignoreNulls());
    } else if (rex instanceof RexCall call) {
      emitRexCallFields(out, call, source);
    }

    out.endObject();
  }

  /**
   * Preserve the source window function independently of Calcite's Rex
   * operator.  Calcite can replace a nullable PostgreSQL window SUM by a
   * generated CASE/COUNT/SUM tree, so the Rex root says CASE even though the
   * independently parsed source root is OVER(SUM(...)).  Downstream still
   * validates the complete generated tree; this field only retains the
   * source language identity that the rewrite otherwise erases.
   */
  private static String sourceWindowFunction(SqlNode sourceSql) {
    SqlNode unaliased = stripAlias(sourceSql);
    if (!(unaliased instanceof SqlCall over)
        || !over.getKind().name().equals("OVER")
        || over.getOperandList().isEmpty()) {
      return null;
    }
    SqlNode functionNode = stripAlias(over.getOperandList().get(0));
    if (!(functionNode instanceof SqlCall function)) {
      return null;
    }
    return function.getOperator().getName().toUpperCase(Locale.ROOT);
  }

  private static void emitRexCallFields(Json out, RexCall call, SourceContext source) {
    out.comma();
    out.name("operator").value(call.getOperator().getName());
    out.comma();
    out.name("opKind").value(call.getOperator().getKind().name());
    out.comma();
    out.name("operands");
    out.beginArray();
    List<SqlNode> sourceOperands = sourceOperands(
        call, source.node(), source.sourcePositions());
    SqlCase sourceCase = directSourceCase(
        call, source.node(), source.sourcePositions());
    int implicitCaseElse = exactImplicitCaseElseIndex(
        call, sourceCase, sourceOperands, source);
    for (int i = 0; i < call.getOperands().size(); i++) {
      if (i > 0) {
        out.comma();
      }
      boolean sourcePositionMapped = i < sourceOperands.size();
      SqlNode sourceOperand = sourcePositionMapped && i != implicitCaseElse
          ? sourceOperands.get(i)
          : null;
      SourceProjectedExpansion sourceExpansion = null;
      if (sourceOperand != null) {
        ProjectedSourceResolution resolution = exactProjectedDescendantSource(
            call.getOperands().get(i), sourceOperand, source);
        sourceOperand = resolution.source();
        sourceExpansion = resolution.expansion();
      }
      SourceContext operandSource = source.withNode(sourceOperand);
      if (sourcePositionMapped && sourceOperand == null) {
        // A mapped null denotes a validator-generated operand, such as the
        // NULL arm introduced by NULLIF/CASE. It must not borrow provenance
        // from an unrelated literal elsewhere in the source query.
        operandSource = operandSource.withoutLiteralRecovery();
      }
      emitRexNode(out, call.getOperands().get(i), operandSource, sourceExpansion);
    }
    out.endArray();
  }

  private static ProjectedSourceResolution exactProjectedDescendantSource(
      RexNode generated, SqlNode sourceOperand, SourceContext source) {
    SqlNode unaliased = stripAlias(sourceOperand);
    if (!(unaliased instanceof SqlIdentifier)
        || source.recoveryRoot() == null) {
      return ProjectedSourceResolution.direct(sourceOperand);
    }
    if (!source.allowDirectProjectedOperandExpansion()
        && source.node() instanceof SqlCall sourceCall
        && sourceCall.getOperandList().stream()
            .anyMatch(operand -> operand == sourceOperand || operand == unaliased)) {
      // A lexically present operand remains authoritative as written. In
      // particular, an outer WHERE over a derived output must retain
      // `alias.column`; resolving it to the inner group key here would make
      // the Rex condition disagree with the independently emitted
      // derived-group binding. Alias expansion below is only for a generated
      // pass-through wrapper whose complete source node is the identifier.
      return ProjectedSourceResolution.direct(sourceOperand);
    }
    SqlSelect owner = topLevelSelect(source.recoveryRoot());
    if (owner == null) {
      return ProjectedSourceResolution.direct(sourceOperand);
    }
    SourceProjectedExpansion directExpansion = directDerivedProjectedExpansion(
        generated, (SqlIdentifier) unaliased, owner, source, false);
    if (directExpansion != null) {
      return new ProjectedSourceResolution(
          directExpansion.definition(), directExpansion, null);
    }
    SourceProjectedExpansion directCteExpansion = directCteProjectedExpansion(
        generated, (SqlIdentifier) unaliased, owner, source);
    if (directCteExpansion != null) {
      return new ProjectedSourceResolution(
          directCteExpansion.definition(), directCteExpansion, null);
    }
    if (source.node() instanceof SqlCall sourceCall
        && sourceCall.getOperandList().stream()
            .anyMatch(operand -> operand == sourceOperand || operand == unaliased)) {
      // Direct scalar operands remain the lexically written references unless
      // the closed derived-table expansion above proves the complete
      // cross-query edge.  In particular, resolving a CTE output name to an
      // inlined aggregate definition would attach an earlier-query span
      // outside this scalar parent.  Rust validates the reference against the
      // exact CTE definition's ordered output namespace instead.
      return ProjectedSourceResolution.direct(sourceOperand);
    }
    SqlNode resolved = resolveProjectedSource(source, owner, unaliased, 8);
    if (resolved == unaliased || resolved.toString().equals(unaliased.toString())) {
      return ProjectedSourceResolution.direct(sourceOperand);
    }
    SqlSelect lexicalOwner = topLevelSelect(source.node());
    SqlNode lexicalInput = lexicalOwner == null
        ? null
        : referencedInputQuery(lexicalOwner, source.ctes());
    SqlSelect lexicalInputOwner = topLevelSelect(lexicalInput);
    boolean resolvedInsideDirectInputQuery = source.sourcePositions() != null
        && lexicalInputOwner != null
        && source.sourcePositions().exactlyContains(lexicalInputOwner, resolved)
        && !source.sourcePositions().exactlyContains(lexicalInputOwner, unaliased);
    if (source.sourcePositions() != null
        && lexicalOwner != null
        && source.sourcePositions().exactlyContains(lexicalOwner, unaliased)
        && (!source.sourcePositions().exactlyContains(lexicalOwner, resolved)
            || resolvedInsideDirectInputQuery)) {
      // A CTE output may resolve to an earlier definition expression after
      // Calcite inlining.  Likewise, an outer reference to an ORDER/OFFSET/
      // FETCH-wrapped derived query may resolve to an inner definition that
      // is textually contained by the outer SELECT while still belonging to
      // the direct child query block.  Without a complete cross-scope
      // expansion payload, neither definition can replace the exact
      // reference written in this query block. Keep the reference; emitted
      // relational provenance and Rust's ordered output-namespace validation
      // bind its generated input.
      return hiddenOrderExpressionAssociationMatches(
              generated, resolved, owner, source.sourcePositions(), 8)
          ? ProjectedSourceResolution.exactCrossScopeReference(sourceOperand, resolved)
          : ProjectedSourceResolution.direct(sourceOperand);
    }
    // Alias expansion is used only after the complete generated subtree and
    // independently parsed projected expression agree. This prevents one
    // same-named derived output from lending literals or casts to an
    // unrelated Rex descendant.
    return hiddenOrderExpressionAssociationMatches(
            generated, resolved, owner, source.sourcePositions(), 8)
        ? ProjectedSourceResolution.direct(resolved)
        : ProjectedSourceResolution.direct(sourceOperand);
  }

  /**
   * Prove the one alias-expansion boundary that can place an exact child
   * source outside its scalar parent's source span. The outer query must have
   * exactly one direct derived-table relation, and the referenced simple name
   * must identify exactly one explicit projected alias in that inner SELECT.
   * CTE, join, lateral, set-operation, implicit-name, column-list, and
   * duplicate-alias shapes remain conservatively unresolved here.
   */
  private static SourceProjectedExpansion directDerivedProjectedExpansion(
      RexNode generated, SqlIdentifier reference, SqlSelect outerSelect,
      SourceContext source, boolean allowGeneratedGroupCarrier) {
    if (outerSelect == null || outerSelect.getFrom() == null) {
      return null;
    }
    SqlNode outerFrom = outerSelect.getFrom();
    SqlSelect innerSelect;
    SqlIdentifier relationAlias = null;
    if (outerFrom instanceof SqlCall derivedRelation
        && derivedRelation.getKind().name().equals("AS")
        && derivedRelation.getOperandList().size() == 2
        && derivedRelation.getOperandList().get(0) instanceof SqlSelect select
        && derivedRelation.getOperandList().get(1) instanceof SqlIdentifier alias
        && alias.isSimple()) {
      innerSelect = select;
      relationAlias = alias;
    } else if (outerFrom instanceof SqlSelect select) {
      // PostgreSQL 16 and later permit a FROM subquery without a relation
      // alias. Its output columns remain visible only by unqualified name.
      // Preserve that exact single-derived-table namespace; qualified
      // references still require an explicit alias below.
      innerSelect = select;
    } else {
      return null;
    }
    if (innerSelect.getSelectList() == null
        || source.sourcePositions() == null) {
      return null;
    }
    boolean directReference = reference.isSimple();
    boolean qualifiedReference = relationAlias != null
        && reference.names.size() == 2
        && reference.names.get(0).equals(relationAlias.names.get(0));
    if (!directReference && !qualifiedReference) {
      return null;
    }
    String referenceName = reference.names.get(reference.names.size() - 1);
    String expansionKind = null;
    SqlNode matchedItem = null;
    SqlIdentifier matchedAlias = null;
    SqlNode matchedDefinition = null;
    for (SqlNode item : innerSelect.getSelectList()) {
      String currentKind = null;
      SqlIdentifier outputAlias = null;
      SqlNode definition = null;
      if (item instanceof SqlCall projected
          && projected.getKind().name().equals("AS")
          && projected.getOperandList().size() == 2
          && projected.getOperandList().get(1) instanceof SqlIdentifier alias
          && alias.isSimple()
          && alias.names.get(0).equals(referenceName)) {
        currentKind = "DIRECT_DERIVED_OUTPUT_ALIAS";
        outputAlias = alias;
        definition = projected.getOperandList().get(0);
      } else if (item instanceof SqlIdentifier identifier
          && !identifier.names.isEmpty()
          && identifier.names.get(identifier.names.size() - 1).equals(referenceName)) {
        currentKind = "DIRECT_DERIVED_PASSTHROUGH";
        outputAlias = identifier;
        definition = identifier;
      }
      if (currentKind == null) {
        continue;
      }
      if (matchedItem != null) {
        return null;
      }
      expansionKind = currentKind;
      matchedItem = item;
      matchedAlias = outputAlias;
      matchedDefinition = definition;
    }
    if (matchedItem == null
        || matchedAlias == null
        || matchedDefinition == null
        || !allowGeneratedGroupCarrier
            && !hiddenOrderExpressionAssociationMatches(
                generated, matchedDefinition, outerSelect, source.sourcePositions(), 8)) {
      return null;
    }
    return new SourceProjectedExpansion(
        expansionKind,
        reference,
        matchedDefinition,
        matchedItem,
        matchedAlias,
        innerSelect,
        outerFrom,
        outerSelect,
        null,
        null);
  }

  /**
   * Bind one direct reference to the public output namespace of one exact,
   * nonrecursive CTE use.  Calcite may inline and prune the CTE's public
   * Project, so a generated value can name a reordered Aggregate result or a
   * literal rather than the CTE output ordinal.  This payload is provenance,
   * not authority by itself: Rust independently re-parses the complete CTE
   * definition and requires this exact use to be the consuming Project's
   * unique {@code sourceInputCteUses} edge.
   */
  private static SourceProjectedExpansion directCteProjectedExpansion(
      RexNode generated, SqlIdentifier reference, SqlSelect outerSelect,
      SourceContext source) {
    if (outerSelect == null
        || outerSelect.getFrom() == null
        || source.sourcePositions() == null) {
      return null;
    }
    SourceCteUse use = sourceCteUse(outerSelect.getFrom(), source);
    if (use == null
        || !(use.definitionQuery() instanceof SqlSelect definitionSelect)
        || definitionSelect.getSelectList() == null
        || definitionSelect.getSelectList().isEmpty()) {
      // Set operations, nested WITH/ORDER wrappers, and other non-direct
      // definitions deliberately remain outside this expansion boundary.
      return null;
    }

    SqlIdentifier visibleRelation = null;
    SqlNode relation = outerSelect.getFrom();
    if (relation instanceof SqlCall aliasCall
        && aliasCall.getKind().name().equals("AS")
        && aliasCall.getOperandList().size() >= 2
        && aliasCall.getOperandList().get(1) instanceof SqlIdentifier alias
        && alias.isSimple()) {
      visibleRelation = alias;
    } else if (stripAlias(relation) instanceof SqlIdentifier cteName
        && cteName.isSimple()) {
      visibleRelation = cteName;
    }
    if (visibleRelation == null) {
      return null;
    }
    boolean directReference = reference.isSimple();
    boolean qualifiedReference = reference.names.size() == 2
        && reference.names.get(0).equals(visibleRelation.names.get(0));
    if (!directReference && !qualifiedReference) {
      return null;
    }

    SqlNodeList selectItems = definitionSelect.getSelectList();
    SqlNodeList declaredColumns = use.definitionItem().columnList;
    boolean hasDeclaredColumns = declaredColumns != null && !declaredColumns.isEmpty();
    if (hasDeclaredColumns && declaredColumns.size() != selectItems.size()) {
      return null;
    }
    String referenceName = reference.names.get(reference.names.size() - 1);
    SourceProjectedExpansion matched = null;
    for (int index = 0; index < selectItems.size(); index++) {
      SqlNode item = selectItems.get(index);
      if (item == null || stripAlias(item) instanceof SqlIdentifier wildcard
          && wildcard.isStar()) {
        return null;
      }
      SqlNode definition = null;
      SqlIdentifier internalOutput = null;
      String kind = null;
      if (item instanceof SqlCall projected
          && projected.getKind().name().equals("AS")
          && projected.getOperandList().size() == 2
          && projected.getOperandList().get(1) instanceof SqlIdentifier alias
          && alias.isSimple()) {
        definition = projected.getOperandList().get(0);
        internalOutput = alias;
        kind = "DIRECT_CTE_OUTPUT_ALIAS";
      } else if (item instanceof SqlIdentifier identifier
          && !identifier.isStar()
          && !identifier.names.isEmpty()) {
        definition = identifier;
        internalOutput = identifier;
        kind = "DIRECT_CTE_PASSTHROUGH";
      }
      if (definition == null || internalOutput == null) {
        // An unnamed expression has no independently recoverable CTE public
        // name.  An explicit CTE column list can name it, but keep the Java
        // association closed to AST nodes whose complete definition/output
        // parts are exact and let Rust conservatively reject anything else.
        if (!hasDeclaredColumns) {
          return null;
        }
        definition = stripAlias(item);
      }

      SqlIdentifier publicOutput;
      if (hasDeclaredColumns) {
        SqlNode rawColumn = declaredColumns.get(index);
        if (!(rawColumn instanceof SqlIdentifier column) || !column.isSimple()) {
          return null;
        }
        publicOutput = column;
        kind = "DIRECT_CTE_EXPLICIT_COLUMN";
      } else {
        publicOutput = internalOutput;
      }
      if (publicOutput == null
          || !publicOutput.names.get(0).equals(referenceName)) {
        continue;
      }
      if (!hiddenOrderExpressionAssociationMatches(
          generated, definition, definitionSelect, source.sourcePositions(), 16)) {
        continue;
      }
      if (matched != null) {
        // Duplicate public output names cannot lend one arbitrary definition
        // to an otherwise ambiguous outer reference.
        return null;
      }
      matched = new SourceProjectedExpansion(
          kind,
          reference,
          definition,
          item,
          publicOutput,
          definitionSelect,
          outerSelect.getFrom(),
          outerSelect,
          index,
          use);
    }
    return matched;
  }

  private static void emitSourceProjectedExpansion(
      Json out, SourceProjectedExpansion expansion, SourceContext source) {
    if (source.node() != expansion.definition()) {
      throw new IllegalStateException(
          "projected-source expansion is not attached to its definition root");
    }
    ExactSourceIdentity reference = exactSourceIdentity(
        source.sourcePositions(), expansion.reference(), "outer alias reference");
    ExactSourceIdentity definition = exactSourceIdentity(
        source.sourcePositions(), expansion.definition(), "projected definition");
    ExactSourceIdentity projectItem = exactSourceIdentity(
        source.sourcePositions(), expansion.projectItem(), "projected select item");
    ExactSourceIdentity outputAlias = exactSourceIdentity(
        source.sourcePositions(), expansion.outputAlias(), "projected output alias");
    ExactSourceIdentity innerSelect = exactSourceIdentity(
        source.sourcePositions(), expansion.innerSelect(), "inner derived SELECT");
    ExactSourceIdentity outerFrom = expansion.cteUse() == null
            && expansion.outerFrom() instanceof SqlSelect
        ? source.sourcePositions().unaliasedDerivedRelationIdentity(expansion.outerFrom())
        : exactSourceIdentity(
            source.sourcePositions(), expansion.outerFrom(), "outer derived FROM");
    if (outerFrom == null) {
      throw new UnsupportedOperationException(
          "missing exact source identity for unaliased outer derived FROM");
    }
    ExactSourceIdentity outerSelect = exactSourceIdentity(
        source.sourcePositions(), expansion.outerSelect(), "outer SELECT");

    out.comma();
    out.name("sourceExpansion");
    out.beginObject();
    out.name("kind").value(expansion.kind());
    emitExactSourceIdentity(out, "reference", reference);
    emitExactSourceIdentity(out, "definition", definition);
    emitExactSourceIdentity(out, "projectItem", projectItem);
    emitExactSourceIdentity(out, "outputAlias", outputAlias);
    emitExactSourceIdentity(out, "innerSelect", innerSelect);
    emitExactSourceIdentity(out, "outerFrom", outerFrom);
    emitExactSourceIdentity(out, "outerSelect", outerSelect);
    if (expansion.publicOutputIndex() != null || expansion.cteUse() != null) {
      if (expansion.publicOutputIndex() == null || expansion.cteUse() == null) {
        throw new IllegalStateException(
            "projected CTE expansion has an incomplete public-output edge");
      }
      out.comma();
      out.name("publicOutputIndex").value(expansion.publicOutputIndex());
      out.comma();
      out.name("cteUse");
      emitSourceCteUse(out, expansion.cteUse(), source.sourcePositions());
    }
    out.endObject();
  }

  private static ExactSourceIdentity exactSourceIdentity(
      SourcePositionMap sourcePositions, SqlNode node, String label) {
    String nodeId = sourceNodeId(sourcePositions, node);
    String sourceText = sourceTextAtNode(sourcePositions, node);
    if (nodeId == null || sourceText == null || sourceText.isEmpty()) {
      throw new UnsupportedOperationException(
          "missing exact source identity for " + label);
    }
    return new ExactSourceIdentity(nodeId, sourceText);
  }

  private static ExactSourceIdentity requiredExactSourceIdentity(
      ExactSourceIdentity identity, String label) {
    if (identity == null || identity.text().isEmpty()) {
      throw new UnsupportedOperationException(
          "missing exact source identity for " + label);
    }
    return identity;
  }

  private static ExactSourceIdentity exactSourceRelationExtent(
      SourcePositionMap sourcePositions, SqlNode relation, String label) {
    ExactSourceIdentity identity = sourcePositions == null
        ? null
        : sourcePositions.relationIdentity(relation);
    if (identity == null || identity.text().isEmpty()) {
      throw new UnsupportedOperationException(
          "missing exact source identity for " + label);
    }
    return identity;
  }

  private static SourceCteUse sourceCteUse(
      SqlNode relation, SourceContext source) {
    SqlNode referenceNode = stripAlias(relation);
    if (!(referenceNode instanceof SqlIdentifier reference)
        || !reference.isSimple()) {
      return null;
    }
    SqlNode definition = source.ctes().get(reference.names.get(0));
    if (definition == null || definition == referenceNode) {
      return null;
    }
    CteDefinitionBinding binding = findCteDefinitionBinding(
        source.literalUniverse(), definition);
    SqlWithItem item = binding == null ? null : binding.item();
    if (binding == null || item == null || item.name == null
        || item.name.names.size() != 1
        || !item.name.names.get(0).equals(reference.names.get(0))) {
      throw new UnsupportedOperationException(
          "cannot bind exact CTE reference to its lexical definition");
    }
    CteReferenceScope referenceScope = directCteReferenceScope(
        binding.owner(), item, reference);
    if (referenceScope == null) {
      throw new UnsupportedOperationException(
          "CTE reference crosses a nested, recursive, or non-lexical scope");
    }
    return new SourceCteUse(
        relation,
        reference,
        item.name,
        definition,
        item,
        binding.owner().withList,
        binding.owner().body,
        binding.owner(),
        referenceScope.kind(),
        referenceScope.container());
  }

  private static SourceCteUse sourceCteUseForRelInput(
      RelNode rel, SourceContext source, SourceContext inputSource, int index) {
    SqlNode candidate = null;
    SqlSelect select = topLevelSelect(source.node());
    if (rel instanceof Join) {
      SqlNode from = select == null ? stripAlias(source.node()) : stripAlias(select.getFrom());
      if (from instanceof SqlJoin join) {
        candidate = index == 0 ? join.getLeft() : join.getRight();
      }
    } else if (rel.getInputs().size() == 1 && select != null) {
      candidate = select.getFrom();
    }
    SourceCteUse use = candidate == null ? null : sourceCteUse(candidate, source);
    return use != null && inputSource.node() == use.definitionQuery() ? use : null;
  }

  private static CteDefinitionBinding findCteDefinitionBinding(
      SqlNode node, SqlNode definition) {
    if (node == null) {
      return null;
    }
    if (node instanceof SqlWith with) {
      for (SqlNode rawItem : with.withList) {
        if (rawItem instanceof SqlWithItem item) {
          if (item.query == definition) {
            return new CteDefinitionBinding(with, item);
          }
          CteDefinitionBinding nested = findCteDefinitionBinding(item.query, definition);
          if (nested != null) {
            return nested;
          }
        }
      }
      return findCteDefinitionBinding(with.body, definition);
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        CteDefinitionBinding nested = findCteDefinitionBinding(item, definition);
        if (nested != null) {
          return nested;
        }
      }
    } else if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        CteDefinitionBinding nested = findCteDefinitionBinding(operand, definition);
        if (nested != null) {
          return nested;
        }
      }
    }
    return null;
  }

  private static CteReferenceScope directCteReferenceScope(
      SqlWith owner, SqlWithItem definition, SqlIdentifier reference) {
    if (containsNodeWithoutNestedWith(owner.body, reference)) {
      return new CteReferenceScope("BODY", owner.body);
    }
    boolean afterDefinition = false;
    for (SqlNode rawItem : owner.withList) {
      if (!(rawItem instanceof SqlWithItem item)) {
        return null;
      }
      if (item == definition) {
        afterDefinition = true;
        continue;
      }
      if (afterDefinition && containsNodeWithoutNestedWith(item.query, reference)) {
        return new CteReferenceScope("LATER_ITEM", item);
      }
    }
    return null;
  }

  private static boolean containsNodeWithoutNestedWith(SqlNode node, SqlNode target) {
    if (node == target) {
      return true;
    }
    if (node == null || node instanceof SqlWith) {
      return false;
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        if (containsNodeWithoutNestedWith(item, target)) {
          return true;
        }
      }
    } else if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        if (containsNodeWithoutNestedWith(operand, target)) {
          return true;
        }
      }
    }
    return false;
  }

  private static void emitSourceCteUse(
      Json out, SourceCteUse use, SourcePositionMap positions) {
    if (positions == null
        || use.definitionWith().withList != use.definitionList()
        || use.definitionWith().body != use.definitionBody()) {
      throw new UnsupportedOperationException(
          "CTE use is detached from its exact lexical WITH owner");
    }
    ExactSourceIdentity reference = exactSourceIdentity(
        positions, use.reference(), "CTE reference");
    ExactSourceIdentity relation = exactSourceIdentity(
        positions, use.relation(), "CTE use relation");
    ExactSourceIdentity definitionName = exactSourceIdentity(
        positions, use.definitionName(), "CTE definition name");
    ExactSourceIdentity definitionQuery = requiredExactSourceIdentity(
        positions.cteQueryIdentity(use.definitionQuery()), "CTE definition query");
    ExactSourceIdentity definitionItem = requiredExactSourceIdentity(
        positions.cteItemIdentity(use.definitionItem()), "CTE definition item");
    ExactSourceIdentity definitionList = requiredExactSourceIdentity(
        positions.cteListIdentity(use.definitionWith()), "CTE definition list");
    ExactSourceIdentity definitionBody = requiredExactSourceIdentity(
        positions.cteQueryIdentity(use.definitionBody()), "CTE WITH body");
    ExactSourceIdentity definitionWith = requiredExactSourceIdentity(
        positions.cteWithIdentity(use.definitionWith()), "CTE WITH owner");
    ExactSourceIdentity referenceScope = requiredExactSourceIdentity(
        positions.cteReferenceScopeIdentity(use.referenceScope()), "CTE reference scope");
    out.beginObject();
    out.name("kind").value("CTE_USE");
    emitExactSourceIdentity(out, "relation", relation);
    emitExactSourceIdentity(out, "reference", reference);
    emitExactSourceIdentity(out, "definitionName", definitionName);
    emitExactSourceIdentity(out, "definitionQuery", definitionQuery);
    emitExactSourceIdentity(out, "definitionItem", definitionItem);
    emitExactSourceIdentity(out, "definitionList", definitionList);
    emitExactSourceIdentity(out, "definitionBody", definitionBody);
    emitExactSourceIdentity(out, "definitionWith", definitionWith);
    out.comma();
    out.name("referenceScopeKind").value(use.referenceScopeKind());
    emitExactSourceIdentity(out, "referenceScope", referenceScope);
    out.endObject();
  }

  private static void emitExactSourceIdentity(
      Json out, String prefix, ExactSourceIdentity identity) {
    out.comma();
    out.name(prefix + "NodeId").value(identity.nodeId());
    out.comma();
    out.name(prefix + "Text").value(identity.text());
  }

  private static SqlNode exactProjectedLiteralSource(
      RexNode generated, SqlNode sourceProject, SourceContext source) {
    if (!(generated instanceof RexLiteral)
        || !(stripAlias(sourceProject) instanceof SqlIdentifier identifier)
        || source.recoveryRoot() == null) {
      return sourceProject;
    }
    SqlSelect owner = topLevelSelect(source.recoveryRoot());
    if (owner == null) {
      return sourceProject;
    }
    SqlNode resolved = resolveProjectedSource(source, owner, identifier, 8);
    if (resolved == identifier || resolved.toString().equals(identifier.toString())) {
      return sourceProject;
    }
    // Calcite can inline a CTE and replace one projected CTE column by its
    // defining literal. An outer identifier is not literal provenance. Use
    // the defining source expression only when the complete generated literal
    // independently matches that exact projected descendant.
    return hiddenOrderExpressionAssociationMatches(
            generated, resolved, owner, source.sourcePositions(), 8)
        ? resolved
        : sourceProject;
  }

  private static void emitRexWindow(Json out, RexWindow window, SourceContext source) {
    SqlWindow sourceWindow = directSourceWindow(source.node());
    List<SqlNode> sourcePartitions = List.of();
    List<SqlNode> sourceOrders = List.of();
    if (sourceWindow != null
        && sourceWindow.getPartitionList() != null
        && sourceWindow.getOrderList() != null
        && sourceWindow.getPartitionList().size() == window.partitionKeys.size()
        && sourceWindow.getOrderList().size() == window.orderKeys.size()) {
      sourcePartitions = sourceWindow.getPartitionList().getList();
      boolean orderMatches = true;
      for (int i = 0; i < window.partitionKeys.size(); i++) {
        if (!windowExpressionAssociationMatches(
            window.partitionKeys.get(i), sourcePartitions.get(i))) {
          orderMatches = false;
          break;
        }
      }
      List<SqlNode> orders = new ArrayList<>();
      for (int i = 0; orderMatches && i < window.orderKeys.size(); i++) {
        SqlNode sourceOrder = sourceWindow.getOrderList().get(i);
        if (!sourceWindowOrderMatches(window.orderKeys.get(i), sourceOrder)
            || !windowExpressionAssociationMatches(
                window.orderKeys.get(i).left, stripOrderByDecoration(sourceOrder))) {
          orderMatches = false;
          break;
        }
        orders.add(stripOrderByDecoration(sourceOrder));
      }
      if (orderMatches) {
        sourceOrders = orders;
      } else {
        sourcePartitions = List.of();
      }
    }
    out.beginObject();
    out.name("partitionKeys");
    out.beginArray();
    for (int i = 0; i < window.partitionKeys.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      SourceContext keySource = i < sourcePartitions.size()
          ? source.withNode(sourcePartitions.get(i))
          : SourceContext.empty();
      emitRexNode(out, window.partitionKeys.get(i), keySource);
    }
    out.endArray();
    out.comma();
    out.name("orderKeys");
    out.beginArray();
    for (int i = 0; i < window.orderKeys.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      SourceContext keySource = i < sourceOrders.size()
          ? source.withNode(sourceOrders.get(i))
          : SourceContext.empty();
      emitRexFieldCollation(out, window.orderKeys.get(i), keySource);
    }
    out.endArray();
    out.comma();
    out.name("isRows").value(window.isRows());
    out.comma();
    out.name("lowerBound");
    emitRexWindowBound(out, window.getLowerBound(), SourceContext.empty());
    out.comma();
    out.name("upperBound");
    emitRexWindowBound(out, window.getUpperBound(), SourceContext.empty());
    out.comma();
    out.name("exclude").value(window.getExclude().name());
    out.endObject();
  }

  private static SqlWindow directSourceWindow(SqlNode source) {
    if (!(source instanceof SqlCall call) || !call.getKind().name().equals("OVER")) {
      return null;
    }
    SqlWindow matched = null;
    for (SqlNode operand : call.getOperandList()) {
      if (operand instanceof SqlWindow window) {
        if (matched != null) {
          return null;
        }
        matched = window;
      }
    }
    return matched;
  }

  private static boolean sourceWindowOrderMatches(
      RexFieldCollation generated, SqlNode source) {
    boolean descending = false;
    String explicitNulls = null;
    SqlNode current = source;
    while (current instanceof SqlCall call && call.getOperandList().size() == 1) {
      String kind = call.getKind().name();
      if (kind.equals("DESCENDING")) {
        descending = true;
      } else if (kind.equals("NULLS_FIRST")) {
        explicitNulls = "FIRST";
      } else if (kind.equals("NULLS_LAST")) {
        explicitNulls = "LAST";
      } else {
        break;
      }
      current = call.getOperandList().get(0);
    }
    String expectedDirection = descending ? "DESCENDING" : "ASCENDING";
    String expectedNulls = explicitNulls != null
        ? explicitNulls
        : descending ? "FIRST" : "LAST";
    return generated.getDirection().name().equals(expectedDirection)
        && generated.getNullDirection().name().equals(expectedNulls);
  }

  private static boolean windowExpressionAssociationMatches(
      RexNode generated, SqlNode rawSource) {
    SqlNode source = stripAlias(rawSource);
    if (generated instanceof RexInputRef) {
      if (source instanceof SqlIdentifier) {
        return true;
      }
      return source instanceof SqlCall call
          && (call.getOperator().getName().equalsIgnoreCase("GROUPING")
              || isSourceAggregateCall(call));
    }
    if (generated instanceof RexLiteral rexLiteral && source instanceof SqlLiteral sqlLiteral) {
      if (rexLiteral.getTypeName() == SqlTypeName.NULL
          || sqlLiteral.getTypeName() == SqlTypeName.NULL) {
        return rexLiteral.getTypeName() == SqlTypeName.NULL
            && sqlLiteral.getTypeName() == SqlTypeName.NULL;
      }
      CanonicalLiteral rex = canonicalRexLiteral(rexLiteral);
      CanonicalLiteral sql = canonicalSourceLiteral(sqlLiteral);
      return rex != null && rex.equals(sql);
    }
    if (!(generated instanceof RexCall rexCall)) {
      return false;
    }
    List<SqlNode> sourceOperands;
    if (source instanceof SqlCase sourceCase && rexCall.getKind().name().equals("CASE")) {
      sourceOperands = sourceCaseOperands(sourceCase);
    } else if (source instanceof SqlCall sourceCall
        && (rexCall.getKind().name().equals(sourceCall.getKind().name())
            || rexCall.getOperator().getName()
                .equalsIgnoreCase(sourceCall.getOperator().getName()))) {
      sourceOperands = sourceCall.getOperandList();
    } else {
      return false;
    }
    if (sourceOperands.size() != rexCall.getOperands().size()) {
      return false;
    }
    for (int i = 0; i < sourceOperands.size(); i++) {
      if (sourceOperands.get(i) == null) {
        // SqlCase represents an omitted ELSE with a null operand while
        // Calcite materializes that one position as a typed Rex NULL.  This
        // admission is deliberately scoped to the already matched CASE tree;
        // a source-less NULL anywhere else still withholds all provenance.
        if (!(source instanceof SqlCase sourceCase)
            || sourceCase.getElseOperand() != null
            || i != sourceOperands.size() - 1
            || !(rexCall.getOperands().get(i) instanceof RexLiteral implicitElse)
            || implicitElse.getTypeName() != SqlTypeName.NULL) {
          return false;
        }
        continue;
      }
      if (!windowExpressionAssociationMatches(
          rexCall.getOperands().get(i), sourceOperands.get(i))) {
        return false;
      }
    }
    return true;
  }

  private static void emitRexFieldCollation(
      Json out, RexFieldCollation field, SourceContext source) {
    out.beginObject();
    out.name("expr");
    emitRexNode(out, field.left, source);
    out.comma();
    out.name("direction").value(field.getDirection().name());
    out.comma();
    out.name("nullDirection").value(field.getNullDirection().name());
    out.endObject();
  }

  private static void emitRexWindowBound(
      Json out, RexWindowBound bound, SourceContext source) {
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
      emitRexNode(out, offset, source);
    }
    out.endObject();
  }

  private static List<SqlNode> topLevelSelectItems(SqlNode sourceSql) {
    SqlSelect select = topLevelSelect(sourceSql);
    if (select == null) {
      return List.of();
    }
    SqlNodeList selectList = select.getSelectList();
    if (selectList == null) {
      return List.of();
    }
    List<SqlNode> items = new ArrayList<>();
    for (SqlNode item : selectList) {
      items.add(resolveProjectedSource(select, stripAlias(item), 8));
    }
    return items;
  }

  private static List<SqlNode> topLevelSelectItemRoles(SqlNode sourceSql) {
    SqlSelect select = topLevelSelect(sourceSql);
    if (select == null || select.getSelectList() == null) {
      return List.of();
    }
    List<SqlNode> items = new ArrayList<>();
    for (SqlNode item : select.getSelectList()) {
      items.add(stripAlias(item));
    }
    return items;
  }

  private static List<SqlNode> sourceSelectItemsForHiddenOrder(
      Project project, SqlNode sourceSql) {
    SqlSelect select = sourceProjectionSelect(sourceSql);
    if (sourceTopLevelOrderBy(sourceSql) == null
        || select == null
        || select.getSelectList() == null
        || select.getSelectList().size() >= project.getProjects().size()) {
      return List.of();
    }
    List<SqlNode> items = new ArrayList<>();
    for (SqlNode item : select.getSelectList()) {
      items.add(resolveProjectedSource(select, stripAlias(item), 8));
    }
    return items;
  }

  private static SqlSelect sourceProjectionSelect(SqlNode sourceSql) {
    SqlNode query = sourceSql;
    for (int fuel = 0; fuel < 8; fuel++) {
      if (query instanceof SqlSelect select) {
        return select;
      }
      if (query instanceof SqlOrderBy orderBy) {
        query = orderBy.query;
        continue;
      }
      if (query instanceof SqlWith with) {
        query = with.body;
        continue;
      }
      return null;
    }
    return null;
  }

  private static boolean sourceSelectPrefixMatchesProject(
      Project project, SqlNode sourceSql, int visibleCount,
      SourcePositionMap sourcePositions) {
    SqlSelect select = sourceProjectionSelect(sourceSql);
    if (select == null
        || select.getSelectList() == null
        || select.getSelectList().size() != visibleCount
        || visibleCount <= 0
        || visibleCount >= project.getProjects().size()
        || visibleCount > project.getRowType().getFieldCount()) {
      return false;
    }
    for (int i = 0; i < visibleCount; i++) {
      String sourceName = sourceSelectOutputName(select.getSelectList().get(i));
      String generatedName = project.getRowType().getFieldList().get(i).getName();
      if (sourceName == null
          ? !hiddenOrderExpressionAssociationMatches(
              project.getProjects().get(i),
              stripAlias(select.getSelectList().get(i)),
              select,
              sourcePositions,
              16)
          : !sourceName.equalsIgnoreCase(generatedName)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Bind Calcite's appended ORDER BY Project fields to exact source items.
   * A hidden expression is exposed only when every generated suffix field has
   * one positional source expression and the complete expression trees agree,
   * modulo Calcite's substitution of one explicit SELECT output alias.
   */
  private static List<SqlNode> sourceHiddenOrderProjectExpressions(
      Project project, SqlNode sourceSql, int visibleCount,
      SourcePositionMap sourcePositions) {
    SqlOrderBy orderBy = sourceTopLevelOrderBy(sourceSql);
    SqlSelect select = sourceProjectionSelect(sourceSql);
    if (orderBy == null
        || orderBy.orderList == null
        || select == null
        || select.getSelectList() == null
        || visibleCount != select.getSelectList().size()
        || visibleCount >= project.getProjects().size()) {
      return List.of();
    }
    List<SqlNode> candidates = new ArrayList<>();
    for (SqlNode rawOrderItem : orderBy.orderList) {
      SqlNode expression = stripOrderByDecoration(rawOrderItem);
      if (sourceOrderExpressionUsesVisibleFieldDirectly(
              expression, select.getSelectList(), visibleCount)
          || sourceExpressionIsVisibleSelectItem(expression, select.getSelectList())) {
        continue;
      }
      candidates.add(expression);
    }
    int hiddenCount = project.getProjects().size() - visibleCount;
    if (candidates.size() != hiddenCount) {
      return List.of();
    }
    for (int i = 0; i < hiddenCount; i++) {
      if (!hiddenOrderExpressionAssociationMatches(
          project.getProjects().get(visibleCount + i), candidates.get(i), select,
          sourcePositions, 16)) {
        return List.of();
      }
    }
    return candidates;
  }

  private static boolean sourceOrderExpressionUsesVisibleFieldDirectly(
      SqlNode expression, SqlNodeList selectList, int visibleCount) {
    if (expression instanceof SqlIdentifier identifier && identifier.isSimple()) {
      String name = identifier.names.get(0);
      for (SqlNode item : selectList) {
        if (name.equals(sourceSelectOutputName(item))) {
          return true;
        }
      }
    }
    if (expression instanceof SqlLiteral literal) {
      CanonicalLiteral canonical = canonicalSourceLiteral(literal);
      if (canonical != null && canonical.family().equals("NUMERIC")) {
        try {
          int ordinal = Integer.parseInt(canonical.canonicalValue());
          return ordinal >= 1 && ordinal <= visibleCount;
        } catch (NumberFormatException ignored) {
          return false;
        }
      }
    }
    return false;
  }

  private static boolean sourceExpressionIsVisibleSelectItem(
      SqlNode expression, SqlNodeList selectList) {
    String source = expression.toString();
    for (SqlNode item : selectList) {
      if (stripAlias(item).toString().equals(source)) {
        return true;
      }
    }
    return false;
  }

  private static boolean hiddenOrderExpressionAssociationMatches(
      RexNode generated, SqlNode rawSource, SqlSelect select,
      SourcePositionMap sourcePositions, int fuel) {
    if (fuel == 0) {
      return false;
    }
    SqlNode source = stripAlias(rawSource);
    if (generated instanceof RexInputRef) {
      if (source instanceof SqlIdentifier) {
        return true;
      }
      return source instanceof SqlCall call
          && (call.getOperator().getName().equalsIgnoreCase("GROUPING")
              || isSourceAggregateCall(call));
    }
    if (source instanceof SqlIdentifier identifier) {
      SqlNode expanded = explicitSelectAliasExpression(select, identifier);
      if (expanded != null) {
        return hiddenOrderExpressionAssociationMatches(
            generated, expanded, select, sourcePositions, fuel - 1);
      }
    }
    if (generated instanceof RexLiteral rexLiteral && source instanceof SqlLiteral sqlLiteral) {
      if (rexLiteral.getTypeName() == SqlTypeName.NULL
          || sqlLiteral.getTypeName() == SqlTypeName.NULL) {
        return rexLiteral.getTypeName() == SqlTypeName.NULL
            && sqlLiteral.getTypeName() == SqlTypeName.NULL;
      }
      CanonicalLiteral rex = canonicalRexLiteral(rexLiteral);
      CanonicalLiteral sql = canonicalSourceLiteral(sqlLiteral);
      return rex != null && rex.equals(sql);
    }
    if (!(generated instanceof RexCall rexCall)) {
      return false;
    }
    List<SqlNode> sourceOperands;
    if (source instanceof SqlCase sourceCase && rexCall.getKind().name().equals("CASE")) {
      sourceOperands = sourceCaseOperands(sourceCase);
    } else if (source instanceof SqlCall sourceCall
        && rexCall.getKind().name().equals("CAST")
        && sourceCall.getKind().name().equals("CAST")) {
      // A SQL CAST call carries its datatype as a second AST operand, while
      // the corresponding RexCall has only the value operand. Reuse the
      // exact CAST-target matcher used by ordinary source emission so a
      // derived explicit CAST can be associated without comparing those
      // unlike arities. Rust independently reparses and checks the exact
      // source target (including observable typmods) before accepting the
      // resulting expansion.
      sourceOperands = sourceOperands(rexCall, source, sourcePositions);
    } else if (source instanceof SqlCall sourceCall
        && (rexCall.getKind().name().equals(sourceCall.getKind().name())
            || rexCall.getOperator().getName()
                .equalsIgnoreCase(sourceCall.getOperator().getName()))) {
      sourceOperands = sourceCall.getOperandList();
    } else {
      return false;
    }
    if (sourceOperands.size() != rexCall.getOperands().size()) {
      return false;
    }
    for (int i = 0; i < sourceOperands.size(); i++) {
      if (sourceOperands.get(i) == null) {
        if (!(source instanceof SqlCase sourceCase)
            || sourceCase.getElseOperand() != null
            || i != sourceOperands.size() - 1
            || !(rexCall.getOperands().get(i) instanceof RexLiteral implicitElse)
            || implicitElse.getTypeName() != SqlTypeName.NULL) {
          return false;
        }
      } else if (!hiddenOrderExpressionAssociationMatches(
          rexCall.getOperands().get(i), sourceOperands.get(i), select,
          sourcePositions, fuel - 1)) {
        return false;
      }
    }
    return true;
  }

  private static SqlNode explicitSelectAliasExpression(
      SqlSelect select, SqlIdentifier identifier) {
    if (!identifier.isSimple() || select.getSelectList() == null) {
      return null;
    }
    String name = identifier.names.get(0);
    SqlNode matched = null;
    for (SqlNode item : select.getSelectList()) {
      if (!(item instanceof SqlCall call)
          || !call.getKind().name().equals("AS")
          || call.getOperandList().size() < 2
          || !(call.getOperandList().get(1) instanceof SqlIdentifier alias)
          || !alias.isSimple()
          || !alias.names.get(0).equals(name)) {
        continue;
      }
      if (matched != null) {
        return null;
      }
      matched = call.getOperandList().get(0);
    }
    return matched;
  }

  private static String sourceSelectOutputName(SqlNode item) {
    if (item instanceof SqlCall call
        && call.getKind().name().equals("AS")
        && call.getOperandList().size() >= 2
        && call.getOperandList().get(1) instanceof SqlIdentifier alias
        && !alias.names.isEmpty()) {
      return alias.names.get(alias.names.size() - 1);
    }
    SqlNode expression = stripAlias(item);
    if (expression instanceof SqlIdentifier identifier && !identifier.names.isEmpty()) {
      return identifier.names.get(identifier.names.size() - 1);
    }
    return null;
  }

  private static List<SqlNode> aggregateInputExpressions(SqlNode sourceSql) {
    return aggregateInputExpressions(sourceSql, null);
  }

  private static List<SqlNode> aggregateInputExpressions(
      SqlNode sourceSql, SourceContext sourceContext) {
    List<SqlNode> definitions = new ArrayList<>();
    for (AggregateInputSource input : aggregateInputSources(sourceSql, sourceContext)) {
      definitions.add(input.definition());
    }
    return definitions;
  }

  /**
   * Preserve both sides of a derived-output aggregate input. The generated
   * Project computes the exact inner definition, while GROUP BY/aggregate
   * syntax names its exact outer reference. Keeping the pair aligned lets the
   * JSON carry a closed cross-scope expansion instead of treating the
   * resolved definition as if it had appeared at the outer reference site.
   */
  private static List<AggregateInputSource> aggregateInputSources(
      SqlNode sourceSql, SourceContext sourceContext) {
    SqlSelect select = topLevelSelect(sourceSql);
    if (select == null) {
      return List.of();
    }
    List<SqlNode> expressions = new ArrayList<>();
    if (select.getGroup() != null) {
      for (SqlNode group : select.getGroup()) {
        collectGroupInputExpressions(stripAlias(group), expressions);
      }
    }
    if (select.getSelectList() != null) {
      for (SqlNode item : select.getSelectList()) {
        collectAggregateInputExpressions(stripAlias(item), expressions);
      }
    }
    if (select.getHaving() != null) {
      collectAggregateInputExpressions(select.getHaving(), expressions);
    }
    List<AggregateInputSource> resolved = new ArrayList<>();
    for (SqlNode role : expressions) {
      SqlNode definition = sourceContext == null
          ? resolveProjectedSource(select, role, 8)
          : resolveProjectedSource(sourceContext, select, role, 8);
      boolean duplicate = resolved.stream().anyMatch(
          input -> input.definition().toString().equals(definition.toString()));
      if (!duplicate) {
        resolved.add(new AggregateInputSource(role, definition));
      }
    }
    return resolved;
  }

  private static List<SqlCall> sourceAggregateCalls(SqlNode sourceSql) {
    SqlSelect select = topLevelSelect(sourceSql);
    if (select == null) {
      return List.of();
    }
    List<SourceAggregateBinding> bindings = new ArrayList<>();
    if (select.getSelectList() != null) {
      for (SqlNode item : select.getSelectList()) {
        collectSourceAggregateBindings(stripAlias(item), bindings);
      }
    }
    if (select.getHaving() != null) {
      collectSourceAggregateBindings(select.getHaving(), bindings);
    }
    List<SqlCall> calls = new ArrayList<>();
    for (SourceAggregateBinding binding : bindings) {
      calls.add(binding.call());
    }
    return calls;
  }

  private static List<SourceAggregateBinding> sourceAggregateBindings(SqlNode sourceSql) {
    SqlSelect select = topLevelSelect(sourceSql);
    if (select == null) {
      return List.of();
    }
    List<SourceAggregateBinding> bindings = new ArrayList<>();
    if (select.getSelectList() != null) {
      for (SqlNode item : select.getSelectList()) {
        collectSourceAggregateBindings(stripAlias(item), bindings);
      }
    }
    if (select.getHaving() != null) {
      collectSourceAggregateBindings(select.getHaving(), bindings);
    }
    return bindings;
  }

  private static void collectSourceAggregateBindings(
      SqlNode node, List<SourceAggregateBinding> bindings) {
    SqlNode unaliased = stripAlias(node);
    if (isQuerySourceNode(unaliased)) {
      // Aggregate ownership is lexical. A scalar subquery, CTE body, or set
      // branch has its own Aggregate RelNode and must never contribute calls
      // to the surrounding SELECT's positional aggregate outputs.
      return;
    }
    if (node instanceof SqlCall call) {
      if (call.getKind().name().equals("OVER") && !call.getOperandList().isEmpty()) {
        collectSourceAggregateBindingsInsideWindowFunction(
            call.getOperandList().get(0), bindings);
        SqlWindow window = directSourceWindow(call);
        if (window != null) {
          if (window.getPartitionList() != null) {
            for (SqlNode partition : window.getPartitionList()) {
              collectSourceAggregateBindings(partition, bindings);
            }
          }
          if (window.getOrderList() != null) {
            for (SqlNode order : window.getOrderList()) {
              collectSourceAggregateBindings(stripOrderByDecoration(order), bindings);
            }
          }
        }
        return;
      }
      if (call.getOperator().getName().equalsIgnoreCase("FILTER")
          && call.getOperandList().size() >= 2) {
        SqlNode aggregateNode = stripAlias(call.getOperandList().get(0));
        if (aggregateNode instanceof SqlCall aggregateCall
            && isSourceAggregateCall(aggregateCall)) {
          addSourceAggregateBinding(
              bindings,
              new SourceAggregateBinding(
                  aggregateCall, singleSourceNode(call.getOperandList().get(1))));
        }
        return;
      }
      if (isSourceAggregateCall(call)) {
        addSourceAggregateBinding(bindings, new SourceAggregateBinding(call, null));
        return;
      }
      for (SqlNode operand : call.getOperandList()) {
        collectSourceAggregateBindings(operand, bindings);
      }
    } else if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectSourceAggregateBindings(item, bindings);
      }
    }
  }

  /**
   * The function at the root of {@code f(...) OVER (...)} is a window
   * function, not a grouped aggregate owned by the input Aggregate RelNode.
   * Search only inside its arguments for nested grouped aggregates.  This
   * distinguishes ordinary {@code SUM(x) OVER (...)} (no grouped call) from
   * {@code SUM(SUM(x)) OVER (...)} (the inner SUM is grouped).
   */
  private static void collectSourceAggregateBindingsInsideWindowFunction(
      SqlNode node, List<SourceAggregateBinding> bindings) {
    SqlNode unaliased = stripAlias(node);
    if (!(unaliased instanceof SqlCall call)) {
      return;
    }
    if (call.getOperator().getName().equalsIgnoreCase("FILTER")
        && !call.getOperandList().isEmpty()) {
      collectSourceAggregateBindingsInsideWindowFunction(
          call.getOperandList().get(0), bindings);
      for (int i = 1; i < call.getOperandList().size(); i++) {
        collectSourceAggregateBindings(call.getOperandList().get(i), bindings);
      }
      return;
    }
    for (SqlNode operand : call.getOperandList()) {
      collectSourceAggregateBindings(operand, bindings);
    }
  }

  private static void addSourceAggregateBinding(
      List<SourceAggregateBinding> bindings, SourceAggregateBinding candidate) {
    String callSql = candidate.call().toString();
    String filterSql = candidate.filter() == null ? null : candidate.filter().toString();
    for (SourceAggregateBinding existing : bindings) {
      if (existing.call().toString().equals(callSql)
          && Objects.equals(
              existing.filter() == null ? null : existing.filter().toString(), filterSql)) {
        return;
      }
    }
    bindings.add(candidate);
  }

  /**
   * Bind each generated Aggregate output position to one same-query-block
   * source aggregate. Function names alone are insufficient when several
   * aggregates use the same operator: their argument/filter indexes must
   * agree with the independently parsed source expressions that populate the
   * Aggregate input row.
   *
   * @return the source calls in generated output order, or null when any
   *     positional provenance is unavailable or inconsistent
   */
  private static List<SqlCall> alignedSourceAggregateCalls(
      Aggregate aggregate, SqlNode sourceSql) {
    SqlSelect select = topLevelSelect(sourceSql);
    if (select == null) {
      return null;
    }
    List<SourceAggregateBinding> source = sourceAggregateBindings(sourceSql);
    List<org.apache.calcite.rel.core.AggregateCall> typed = aggregate.getAggCallList();
    if (typed.size() != source.size()) {
      return null;
    }
    List<SqlNode> inputExpressions = aggregateInputExpressions(sourceSql);
    List<SqlCall> calls = new ArrayList<>();
    for (int i = 0; i < typed.size(); i++) {
      org.apache.calcite.rel.core.AggregateCall generated = typed.get(i);
      SourceAggregateBinding binding = source.get(i);
      SqlCall sourceCall = binding.call();
      if (!generated.getAggregation().getName()
              .equalsIgnoreCase(sourceCall.getOperator().getName())
          || generated.isDistinct() != sourceAggregateIsDistinct(sourceCall)) {
        return null;
      }

      List<Integer> expectedArgs = new ArrayList<>();
      for (SqlNode operand : sourceCall.getOperandList()) {
        if (operand != null && operand.getKind().name().equals("IDENTIFIER")
            && operand.toString().equals("*")) {
          continue;
        }
        int inputIndex = resolvedSourceExpressionIndex(
            select, inputExpressions, stripAlias(operand));
        if (inputIndex < 0) {
          return null;
        }
        expectedArgs.add(inputIndex);
      }
      if (!generated.getArgList().equals(expectedArgs)) {
        return null;
      }

      if (binding.filter() == null) {
        if (generated.filterArg >= 0) {
          return null;
        }
      } else {
        int filterIndex = resolvedSourceExpressionIndex(
            select, inputExpressions, binding.filter());
        if (filterIndex < 0 || generated.filterArg != filterIndex) {
          return null;
        }
      }
      calls.add(sourceCall);
    }
    return calls;
  }

  private static boolean sourceAggregateIsDistinct(SqlCall call) {
    return call.getFunctionQuantifier() != null
        && call.getFunctionQuantifier().toString().equalsIgnoreCase("DISTINCT");
  }

  private static int sourceExpressionIndex(List<SqlNode> expressions, SqlNode needle) {
    if (needle == null) {
      return -1;
    }
    String sql = needle.toString();
    for (int i = 0; i < expressions.size(); i++) {
      if (expressions.get(i).toString().equals(sql)) {
        return i;
      }
    }
    return -1;
  }

  /**
   * {@link #aggregateInputExpressions} records expressions after following a
   * direct derived-table projection. Resolve every lookup through that same
   * independently parsed SELECT before comparing it with the positional
   * input list. Mixing a resolved list with an unresolved alias can make an
   * owning Aggregate appear to belong to its child query block and attach
   * unrelated source expressions to generated Rex nodes.
   */
  private static int resolvedSourceExpressionIndex(
      SqlSelect select, List<SqlNode> expressions, SqlNode needle) {
    if (select == null || needle == null) {
      return -1;
    }
    return sourceExpressionIndex(
        expressions, resolveProjectedSource(select, stripAlias(needle), 8));
  }

  private static void collectGroupInputExpressions(
      SqlNode node, List<SqlNode> expressions) {
    SqlNode unaliased = stripAlias(node);
    if (unaliased instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectGroupInputExpressions(item, expressions);
      }
      return;
    }
    if (unaliased instanceof SqlCall call
        && (call.getKind().name().equals("GROUPING_SETS")
            || call.getKind().name().equals("ROLLUP")
            || call.getKind().name().equals("CUBE")
            || call.getKind().name().equals("ROW"))) {
      for (SqlNode operand : call.getOperandList()) {
        collectGroupInputExpressions(operand, expressions);
      }
      return;
    }
    addSourceExpression(expressions, unaliased);
  }

  private static void collectAggregateInputExpressions(
      SqlNode node, List<SqlNode> expressions) {
    if (isQuerySourceNode(stripAlias(node))) {
      return;
    }
    if (node instanceof SqlCall call) {
      if (call.getKind().name().equals("OVER") && !call.getOperandList().isEmpty()) {
        collectAggregateInputsInsideWindowFunction(
            call.getOperandList().get(0), expressions);
        SqlWindow window = directSourceWindow(call);
        if (window != null) {
          if (window.getPartitionList() != null) {
            for (SqlNode partition : window.getPartitionList()) {
              collectAggregateInputExpressions(partition, expressions);
            }
          }
          if (window.getOrderList() != null) {
            for (SqlNode order : window.getOrderList()) {
              collectAggregateInputExpressions(stripOrderByDecoration(order), expressions);
            }
          }
        }
        return;
      }
      if (call.getOperator().getName().equalsIgnoreCase("FILTER")
          && call.getOperandList().size() >= 2) {
        collectAggregateInputExpressions(call.getOperandList().get(0), expressions);
        addSourceExpression(expressions, singleSourceNode(call.getOperandList().get(1)));
        return;
      }
      if (isSourceAggregateCall(call)) {
        for (SqlNode operand : call.getOperandList()) {
          if (operand != null && operand.getKind().name().equals("IDENTIFIER")
              && operand.toString().equals("*")) {
            continue;
          }
          addSourceExpression(expressions, stripAlias(operand));
        }
        return;
      }
      for (SqlNode operand : call.getOperandList()) {
        collectAggregateInputExpressions(operand, expressions);
      }
    } else if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectAggregateInputExpressions(item, expressions);
      }
    }
  }

  private static void collectAggregateInputsInsideWindowFunction(
      SqlNode node, List<SqlNode> expressions) {
    SqlNode unaliased = stripAlias(node);
    if (!(unaliased instanceof SqlCall call)) {
      return;
    }
    if (call.getOperator().getName().equalsIgnoreCase("FILTER")
        && !call.getOperandList().isEmpty()) {
      collectAggregateInputsInsideWindowFunction(
          call.getOperandList().get(0), expressions);
      for (int i = 1; i < call.getOperandList().size(); i++) {
        collectAggregateInputExpressions(call.getOperandList().get(i), expressions);
      }
      return;
    }
    for (SqlNode operand : call.getOperandList()) {
      collectAggregateInputExpressions(operand, expressions);
    }
  }

  private static SqlNode singleSourceNode(SqlNode node) {
    if (node instanceof SqlNodeList list && list.size() == 1) {
      return list.get(0);
    }
    return node;
  }

  private static boolean isSourceAggregateCall(SqlCall call) {
    if (call.getOperator().isAggregator()) {
      return true;
    }
    return switch (call.getOperator().getName().toUpperCase(Locale.ROOT)) {
      case "COUNT", "SUM", "AVG", "MIN", "MAX", "EVERY", "SOME", "ANY", "GROUPING",
          "BOOL_AND", "BOOL_OR", "BIT_AND", "BIT_OR", "ARRAY_AGG", "STRING_AGG",
          "LISTAGG", "STDDEV", "STDDEV_POP", "STDDEV_SAMP", "VARIANCE", "VAR_POP",
          "VAR_SAMP", "ANY_VALUE", "SINGLE_VALUE" -> true;
      default -> false;
    };
  }

  private static void addSourceExpression(List<SqlNode> expressions, SqlNode candidate) {
    if (candidate == null) {
      return;
    }
    String text = candidate.toString();
    for (SqlNode expression : expressions) {
      if (expression.toString().equals(text)) {
        return;
      }
    }
    expressions.add(candidate);
  }

  private static SqlNode resolveProjectedSource(SqlSelect select, SqlNode expression, int fuel) {
    if (fuel == 0 || !(expression instanceof SqlIdentifier identifier)) {
      return expression;
    }
    SqlSelect input = selectInputSubquery(select.getFrom());
    if (input == null || input.getSelectList() == null) {
      return expression;
    }
    String name = identifier.names.get(identifier.names.size() - 1);
    SqlNode matched = null;
    for (SqlNode item : input.getSelectList()) {
      String alias = selectItemAlias(item);
      // The parser configuration has already folded unquoted PostgreSQL
      // identifiers to lower case and retained quoted spelling exactly.  An
      // additional case-insensitive comparison would therefore conflate x
      // with "X" and could attach the wrong source CAST/typmod to a Rex node.
      if (alias != null && alias.equals(name)) {
        if (matched != null) {
          // A validated PostgreSQL query should not contain an ambiguous
          // reference at this point.  If Calcite nevertheless presents one,
          // leave the identifier unresolved instead of choosing provenance
          // from one arbitrary select item.
          return expression;
        }
        matched = stripAlias(item);
      }
    }
    return matched == null
        ? expression
        : resolveProjectedSource(input, matched, fuel - 1);
  }

  private static SqlNode resolveProjectedSource(
      SourceContext source, SqlSelect select, SqlNode expression, int fuel) {
    return resolveProjectedSource(
        source.cteScopes(), source.ctes(), select, expression, fuel);
  }

  private static SqlNode resolveProjectedSource(
      CteProvenanceScopes scopes, Map<String, SqlNode> ctes,
      SqlSelect select, SqlNode expression, int fuel) {
    if (fuel == 0 || !(expression instanceof SqlIdentifier identifier)) {
      return expression;
    }
    SqlNode inputNode = resolveCteReference(stripAlias(select.getFrom()), ctes);
    SqlSelect input = topLevelSelect(inputNode);
    if (input == null || input.getSelectList() == null) {
      return expression;
    }
    String name = identifier.names.get(identifier.names.size() - 1);
    SqlNode matched = null;
    for (SqlNode item : input.getSelectList()) {
      String alias = selectItemAlias(item);
      if (alias != null && alias.equals(name)) {
        if (matched != null) {
          return expression;
        }
        matched = stripAlias(item);
      }
    }
    if (matched == null) {
      return expression;
    }
    Map<String, SqlNode> inputCtes = scopes.environmentFor(input, ctes);
    return resolveProjectedSource(scopes, inputCtes, input, matched, fuel - 1);
  }

  private static SqlSelect selectInputSubquery(SqlNode from) {
    SqlNode input = stripAlias(from);
    return input instanceof SqlSelect select ? select : topLevelSelect(input);
  }

  private static String selectItemAlias(SqlNode item) {
    if (item instanceof SqlCall call && call.getKind().name().equals("AS")
        && call.getOperandList().size() >= 2
        && call.getOperandList().get(1) instanceof SqlIdentifier alias) {
      return alias.names.get(alias.names.size() - 1);
    }
    if (item instanceof SqlIdentifier identifier) {
      return identifier.names.get(identifier.names.size() - 1);
    }
    return null;
  }

  private static SqlNode stripAlias(SqlNode node) {
    if (node instanceof SqlCall call && call.getKind().name().equals("AS")
        && !call.getOperandList().isEmpty()) {
      return call.getOperandList().get(0);
    }
    return node;
  }

  private static SqlNode sourceFilterCondition(Filter filter, SourceContext source) {
    return sourceFilterCondition(filter, source, 8);
  }

  /**
   * Return a clause role only when the independently parsed source query block
   * directly accounts for this Calcite Filter.  The recursive condition
   * recovery below is intentionally not used here: a condition found in a
   * nested query is useful scalar provenance, but it cannot authorize moving
   * this relational Filter into an Aggregate belonging to another block.
   */
  private static String sourceFilterClause(Filter filter, SourceContext source) {
    SqlSelect select = topLevelSelect(source.node());
    if (select == null) {
      return null;
    }
    if (source.clausePhase() == SourceClausePhase.POST_AGGREGATE
        && select.getHaving() != null && filter.getInput() instanceof Aggregate) {
      return "HAVING";
    }
    if (select.getWhere() != null) {
      return "WHERE";
    }
    return null;
  }

  /**
   * Bind one LogicalFilter to the exact WHERE node in the independently
   * parsed source query block.  Scalar provenance by itself is not clause
   * ownership: validator-generated and nested filters can carry useful source
   * expressions without denoting this block's WHERE operator.  The root
   * parser span and the complete positional source/Rex alignment are therefore
   * mandatory before downstream code may treat this Filter as the block's
   * declarative pre-group WHERE predicate.
   */
  private static SourceWhereAttestation sourceWhereAttestation(
      Filter filter, SourceContext source) {
    if (!"WHERE".equals(sourceFilterClause(filter, source))) {
      return null;
    }
    SqlSelect select = topLevelSelect(source.node());
    SqlNode sourceWhere = select == null ? null : select.getWhere();
    SqlNode alignedCondition = sourceFilterCondition(filter, source);
    String queryBlockId = sourceQueryBlockId(select, source.sourcePositions());
    ExactSourceIdentity ownerIdentity = source.sourcePositions() == null
        ? null
        : source.sourcePositions().relationalSourceIdentity(source.node());
    String ownerNodeId = ownerIdentity == null ? null : ownerIdentity.nodeId();
    String conditionNodeId = sourceNodeId(source.sourcePositions(), sourceWhere);
    List<SourceWhereInputBinding> inputBindings = new ArrayList<>();
    if (sourceWhere == null
        || alignedCondition != sourceWhere
        || queryBlockId == null
        || !queryBlockId.equals(source.queryBlockId())
        || ownerNodeId == null
        || conditionNodeId == null
        || filter.getInputs().size() != 1
        || !filter.getRowType().equals(filter.getInput().getRowType())
        || !filter.getVariablesSet().containsAll(RelOptUtil.getVariablesUsed(filter))
        || !filter.getVariablesSet().isEmpty()
            && !sourceWhereNestedBaseNamesUnique(filter.getInput())
        || !sourceWhereRexTreeAligned(
            filter.getCondition(), sourceWhere, source.sourcePositions())
        || !collectSourceWhereInputBindings(
            filter.getCondition(), sourceWhere, filter.getInput(), select.getFrom(), "$",
            source.sourcePositions(), inputBindings)) {
      return null;
    }
    List<String> variablesSet = new ArrayList<>();
    for (CorrelationId id : filter.getVariablesSet()) {
      variablesSet.add(id.getName());
    }
    List<SourceWhereAnalysisErrorBinding> analysisErrors = new ArrayList<>();
    collectSourceWhereAnalysisErrors(
        filter.getCondition(), sourceWhere, "$", source.sourcePositions(),
        inputBindings, analysisErrors);
    return new SourceWhereAttestation(
        queryBlockId,
        ownerNodeId,
        conditionNodeId,
        sourceWhere.toString(),
        sourceWhere.getKind().name(),
        sourceWhere instanceof SqlCall call ? call.getOperator().getName() : null,
        filter.getCondition().toString(),
        filter.getRowType().getFieldCount(),
        filter.getInput().getRowType().getFieldCount(),
        variablesSet,
        List.copyOf(inputBindings),
        List.copyOf(analysisErrors));
  }

  /**
   * Record only the one Calcite coercion that this campaign can prove is a
   * PostgreSQL parse-analysis error.  PostgreSQL has explicit int4/bool casts,
   * but no implicit boolean = integer operator; Calcite instead changes a
   * bare source 0/1 into a BOOLEAN RexLiteral.  The surrounding source-WHERE
   * attestation already proves lexical ownership and exact base-field
   * identity, so this binding closes the remaining source/Rex type mismatch
   * at one positional path.
   */
  private static void collectSourceWhereAnalysisErrors(
      RexNode rex,
      SqlNode sourceNode,
      String path,
      SourcePositionMap sourcePositions,
      List<SourceWhereInputBinding> inputBindings,
      List<SourceWhereAnalysisErrorBinding> errors) {
    SourceWhereAnalysisErrorBinding error = sourceWhereBooleanIntegerEqualityError(
        rex, sourceNode, path, inputBindings);
    if (error != null) {
      errors.add(error);
    }
    if (!(rex instanceof RexCall call)) {
      return;
    }
    List<SqlNode> sourceChildren = sourceOperands(call, sourceNode, sourcePositions);
    if (sourceChildren.size() != call.getOperands().size()) {
      return;
    }
    for (int i = 0; i < call.getOperands().size(); i++) {
      SqlNode sourceChild = sourceChildren.get(i);
      if (sourceChild != null) {
        collectSourceWhereAnalysisErrors(
            call.getOperands().get(i), sourceChild, path + "." + i,
            sourcePositions, inputBindings, errors);
      }
    }
  }

  private static SourceWhereAnalysisErrorBinding sourceWhereBooleanIntegerEqualityError(
      RexNode rex,
      SqlNode sourceNode,
      String path,
      List<SourceWhereInputBinding> inputBindings) {
    if (!(rex instanceof RexCall rexCall)
        || !(sourceNode instanceof SqlCall sourceCall)
        || !rexCall.getKind().name().equals("EQUALS")
        || !rexCall.getOperator().getName().equals("=")
        || rexCall.getType().getSqlTypeName() != SqlTypeName.BOOLEAN
        || rexCall.getOperands().size() != 2
        || !sourceCall.getKind().name().equals("EQUALS")
        || !sourceCall.getOperator().getName().equals("=")
        || sourceCall.getOperandList().size() != 2) {
      return null;
    }

    for (int identifierOperand : new int[] {0, 1}) {
      int literalOperand = 1 - identifierOperand;
      RexNode rexIdentifierNode = rexCall.getOperands().get(identifierOperand);
      RexNode rexLiteralNode = rexCall.getOperands().get(literalOperand);
      SqlNode sourceIdentifierNode = sourceCall.getOperandList().get(identifierOperand);
      SqlNode sourceLiteralNode = sourceCall.getOperandList().get(literalOperand);
      if (!(rexIdentifierNode instanceof RexInputRef rexIdentifier)
          || rexIdentifier.getType().getSqlTypeName() != SqlTypeName.BOOLEAN
          || !(rexLiteralNode instanceof RexLiteral rexLiteral)
          || rexLiteral.getTypeName() != SqlTypeName.BOOLEAN
          || rexLiteral.isNull()
          || !(sourceIdentifierNode instanceof SqlIdentifier)
          || !(sourceLiteralNode instanceof SqlLiteral sourceLiteral)) {
        continue;
      }
      CanonicalLiteral sourceCanonical = canonicalSourceLiteral(sourceLiteral);
      CanonicalLiteral generatedCanonical = canonicalRexLiteral(rexLiteral);
      if (sourceCanonical == null
          || generatedCanonical == null
          || !sourceCanonical.family().equals("NUMERIC")
          || !generatedCanonical.family().equals("BOOLEAN")
          || !(sourceCanonical.canonicalValue().equals("0")
              || sourceCanonical.canonicalValue().equals("1"))
          // Restrict the exception to one exact bare integral spelling. A
          // decimal, signed expression, string, or CAST is a different source
          // node even if its eventual value happens to be zero or one.
          || !sourceLiteral.toString().equals(sourceCanonical.canonicalValue())
          || !generatedCanonical.canonicalValue().equals(
              sourceCanonical.canonicalValue().equals("0") ? "false" : "true")) {
        continue;
      }

      String identifierPath = path + "." + identifierOperand;
      SourceWhereInputBinding matched = null;
      for (SourceWhereInputBinding binding : inputBindings) {
        if (binding.path().equals(identifierPath)) {
          if (matched != null) {
            return null;
          }
          matched = binding;
        }
      }
      if (matched == null
          || matched.inputIndex() != rexIdentifier.getIndex()
          || !matched.sourceSql().equals(sourceIdentifierNode.toString())
          || matched.baseTable().isEmpty()
          || matched.baseFieldName().isEmpty()) {
        continue;
      }
      return new SourceWhereAnalysisErrorBinding(
          POSTGRES_BOOLEAN_INTEGER_EQUALITY_UNDEFINED_FUNCTION,
          path,
          identifierOperand,
          literalOperand,
          rexCall.toString(),
          rexIdentifier.getIndex(),
          matched.baseTable(),
          matched.tableFieldIndex(),
          matched.baseFieldName(),
          sourceCanonical.canonicalValue(),
          generatedCanonical.canonicalValue());
    }
    return null;
  }

  private static boolean collectSourceWhereInputBindings(
      RexNode rex, SqlNode sourceNode, RelNode input, SqlNode sourceFrom, String path,
      SourcePositionMap sourcePositions,
      List<SourceWhereInputBinding> bindings) {
    if (rex == null || sourceNode == null) {
      return false;
    }
    if (rex instanceof RexInputRef inputRef) {
      if (!(sourceNode instanceof SqlIdentifier identifier)) {
        return false;
      }
      SourceWhereInputOrigin origin = sourceWhereInputOrigin(
          input, sourceFrom, inputRef.getIndex(), sourcePositions);
      Integer directIndex = origin == null
          ? null
          : directTableFieldIndex(identifier, origin.sourceTable(), origin.scan());
      if (origin == null
          || directIndex == null
          || directIndex != origin.tableFieldIndex()
          || inputRef.getIndex() < 0
          || inputRef.getIndex() >= input.getRowType().getFieldCount()) {
        return false;
      }
      bindings.add(new SourceWhereInputBinding(
          path,
          inputRef.getIndex(),
          identifier.toString(),
          origin.sourceRelationNodeId(),
          origin.sourceRelationSql(),
          origin.scan().getTable().getQualifiedName(),
          origin.tableFieldIndex(),
          origin.scan().getRowType().getFieldList().get(origin.tableFieldIndex()).getName(),
          input.getRowType().getFieldList().get(inputRef.getIndex()).getName()));
      return true;
    }
    if (rex instanceof RexSubQuery subQuery) {
      if (subQuery.getOperands().isEmpty()) {
        return true;
      }
      List<SqlNode> sourceChildren = new ArrayList<>();
      for (SqlNode candidate : sourceOperands(subQuery, sourceNode, sourcePositions)) {
        if (!isQuerySourceNode(stripAlias(candidate))) {
          sourceChildren.add(candidate);
        }
      }
      if (sourceChildren.size() != subQuery.getOperands().size()) {
        return false;
      }
      for (int i = 0; i < subQuery.getOperands().size(); i++) {
        if (!collectSourceWhereInputBindings(
            subQuery.getOperands().get(i), sourceChildren.get(i), input, sourceFrom,
            path + "." + i, sourcePositions, bindings)) {
          return false;
        }
      }
      return true;
    }
    if (rex instanceof RexCall call) {
      List<SqlNode> sourceChildren = sourceOperands(call, sourceNode, sourcePositions);
      if (sourceChildren.size() != call.getOperands().size()) {
        return false;
      }
      for (int i = 0; i < call.getOperands().size(); i++) {
        if (sourceChildren.get(i) == null
            || !collectSourceWhereInputBindings(
                call.getOperands().get(i), sourceChildren.get(i), input, sourceFrom,
                path + "." + i, sourcePositions, bindings)) {
          return false;
        }
      }
      return true;
    }
    return rex instanceof RexLiteral || rex instanceof RexFieldAccess;
  }

  private static SourceWhereInputOrigin sourceWhereInputOrigin(
      RelNode rel, SqlNode sourceNode, int outputIndex,
      SourcePositionMap sourcePositions) {
    if (outputIndex < 0 || outputIndex >= rel.getRowType().getFieldCount()) {
      return null;
    }
    if (rel instanceof Join join) {
      SqlNode from = sourceNode instanceof SqlSelect select ? select.getFrom() : sourceNode;
      if (!(stripAlias(from) instanceof SqlJoin sourceJoin)
          || join.getInputs().size() != 2) {
        return null;
      }
      int leftArity = join.getLeft().getRowType().getFieldCount();
      if (outputIndex < leftArity) {
        return sourceWhereInputOrigin(
            join.getLeft(), sourceJoin.getLeft(), outputIndex, sourcePositions);
      }
      return sourceWhereInputOrigin(
          join.getRight(), sourceJoin.getRight(), outputIndex - leftArity,
          sourcePositions);
    }
    if (rel instanceof Filter || rel instanceof Sort) {
      return rel.getInputs().size() == 1
          ? sourceWhereInputOrigin(
              rel.getInput(0), sourceNode, outputIndex, sourcePositions)
          : null;
    }
    if (!(rel instanceof TableScan scan)) {
      return null;
    }
    DirectTableSource sourceTable = directTableSource(sourceNode, scan);
    String relationNodeId = sourceNodeId(sourcePositions, sourceNode);
    if (sourceTable == null || relationNodeId == null
        || outputIndex >= scan.getRowType().getFieldCount()) {
      return null;
    }
    return new SourceWhereInputOrigin(
        scan, sourceTable, outputIndex, relationNodeId, sourceNode.toString());
  }

  private static boolean sourceWhereRexTreeAligned(
      RexNode rex, SqlNode sourceNode, SourcePositionMap sourcePositions) {
    if (rex == null || sourceNode == null) {
      return false;
    }
    if (rex instanceof RexSubQuery subQuery) {
      SqlNode nestedSource = subquerySource(sourceNode);
      if (nestedSource == null) {
        return false;
      }
      SourceInSubqueryOrderAttestation lostOrder =
          sourceInSubqueryOrderAttestation(subQuery, sourceNode, sourcePositions);
      SourceContext nestedRelSource = lostOrder == null
          ? SourceContext.root(nestedSource, sourcePositions)
          : SourceContext.root(((SqlOrderBy) nestedSource).query, sourcePositions);
      if (!sourceWhereRexOperatorAligned(subQuery, sourceNode)
          || sourceSubqueryRelCorrespondence(subQuery.rel, nestedRelSource) == null) {
        return false;
      }
      if (subQuery.getOperands().isEmpty()) {
        return true;
      }
      List<SqlNode> sourceChildren = new ArrayList<>();
      for (SqlNode candidate : sourceOperands(subQuery, sourceNode, sourcePositions)) {
        if (!isQuerySourceNode(stripAlias(candidate))) {
          sourceChildren.add(candidate);
        }
      }
      if (sourceChildren.size() != subQuery.getOperands().size()) {
        return false;
      }
      for (int i = 0; i < subQuery.getOperands().size(); i++) {
        if (sourceChildren.get(i) == null
            || !sourceWhereRexTreeAligned(
                subQuery.getOperands().get(i), sourceChildren.get(i), sourcePositions)) {
          return false;
        }
      }
      return true;
    }
    if (rex instanceof RexCall call) {
      if (sourceWhereExpandedCoalesceTreeAligned(call, sourceNode, sourcePositions)) {
        return true;
      }
      if (!sourceWhereRexOperatorAligned(call, sourceNode)) {
        return false;
      }
      List<SqlNode> sourceChildren = sourceOperands(call, sourceNode, sourcePositions);
      if (sourceChildren.size() != call.getOperands().size()) {
        return false;
      }
      for (int i = 0; i < call.getOperands().size(); i++) {
        if (sourceChildren.get(i) == null
            || !sourceWhereRexTreeAligned(
                call.getOperands().get(i), sourceChildren.get(i), sourcePositions)) {
          return false;
        }
      }
      return true;
    }
    // A correlated field access is the source identifier leaf.  Its
    // RexCorrelVariable reference has no independent SQL node of its own and
    // is validated structurally by the Rust importer instead of inheriting
    // this identifier's provenance. Do not accept a call collapsed to a leaf:
    // that would erase the source operator tree this attestation authorizes.
    if (rex instanceof RexFieldAccess || rex instanceof RexInputRef) {
      return sourceNode instanceof SqlIdentifier;
    }
    if (rex instanceof RexLiteral) {
      return sourceNode instanceof SqlLiteral;
    }
    return false;
  }

  /**
   * Calcite lowers a two-argument COALESCE to
   * {@code CASE WHEN value IS NOT NULL THEN value ELSE fallback END}, adding
   * result-type casts when needed.  Authenticate that complete declarative
   * rewrite here instead of treating an arbitrary generated IS NOT NULL as an
   * implicit wrapper around a source expression.  In particular, the tested
   * value and returned value must be the same generated Rex subtree after
   * stripping only unary result casts, and all three source roles are checked
   * recursively against the exact ordered COALESCE operands.
   */
  private static boolean sourceWhereExpandedCoalesceTreeAligned(
      RexCall generated, SqlNode sourceNode, SourcePositionMap sourcePositions) {
    if (!generated.getKind().name().equals("CASE")
        || !(sourceNode instanceof SqlCall source)
        || !source.getOperator().getName().equalsIgnoreCase("COALESCE")
        || source.getOperandList().size() != 2
        || generated.getOperands().size() != 3
        || !(generated.getOperands().get(0) instanceof RexCall condition)
        || !condition.getKind().name().equals("IS_NOT_NULL")
        || !condition.getOperator().getName().equalsIgnoreCase("IS NOT NULL")
        || condition.getOperands().size() != 1
        || condition.getType().getSqlTypeName() != SqlTypeName.BOOLEAN
        || condition.getType().isNullable()) {
      return false;
    }

    RexNode tested = condition.getOperands().get(0);
    RexNode returned = generated.getOperands().get(1);
    RexNode returnedLeaf = returned;
    while (returnedLeaf instanceof RexCall cast
        && cast.getKind().name().equals("CAST")
        && cast.getOperands().size() == 1) {
      returnedLeaf = cast.getOperands().get(0);
    }
    SqlNode sourceValue = source.getOperandList().get(0);
    SqlNode sourceFallback = source.getOperandList().get(1);
    return tested.equals(returnedLeaf)
        && sourceWhereRexTreeAligned(tested, sourceValue, sourcePositions)
        && sourceWhereRexTreeAligned(returned, sourceValue, sourcePositions)
        && sourceWhereRexTreeAligned(
            generated.getOperands().get(2), sourceFallback, sourcePositions);
  }

  /**
   * Close RexSubQuery provenance over its complete generated relational tree.
   * Every supported relational/scalar node is aligned positionally with the
   * independently parsed nested query before the outer WHERE may claim
   * clause authority. Unsupported planner shapes fail closed.
   */
  private static boolean sourceRelOperatorCorresponds(
      RelNode rel, SourceContext source) {
    if (rel == null
        || source.node() == null) {
      return false;
    }
    if (source.node() instanceof SqlOrderBy orderBy
        && hasSourceItems(orderBy.orderList)
        && !(rel instanceof Sort)) {
      // A nonempty source ORDER BY must have a generated Sort, except for the
      // one separately attested Calcite-loss path. That path deliberately
      // calls this validator with the wrapped SqlSelect instead.
      return false;
    }
    if (rel instanceof TableScan scan) {
      SqlSelect select = topLevelSelect(source.node());
      SqlNode from = select == null ? source.node() : select.getFrom();
      return rel.getInputs().isEmpty() && directTableSource(from, scan) != null;
    }
    if (rel instanceof Filter filter) {
      SqlNode condition = sourceFilterCondition(filter, source);
      String clause = sourceFilterClause(filter, source);
      boolean conditionAligned = condition != null
          && ("HAVING".equals(clause)
                  && sourceNativeHavingAttestation(filter, source) != null
              || sourceWhereRexTreeAligned(
                  filter.getCondition(), condition, source.sourcePositions()));
      if (rel.getInputs().size() != 1
          || condition == null
          || clause == null
          || !conditionAligned) {
        return false;
      }
    } else if (rel instanceof Project project) {
      if (rel.getInputs().size() != 1) {
        return false;
      }
      List<SqlNode> sourceProjects = topLevelSelectItems(source.node());
      List<SqlNode> aggregateInputs = aggregateInputExpressions(source.node());
      Aggregate projectAggregate = project.getInput() instanceof Aggregate aggregate
          ? aggregate
          : null;
      SqlSelect projectSelect = projectAggregate == null
          ? null
          : topLevelSelect(source.node());
      List<SqlCall> projectAlignedAggregates = projectAggregate == null
          ? null
          : alignedSourceAggregateCalls(projectAggregate, source.node());
      List<SourceAggregateBinding> projectSourceAggregates = projectAggregate == null
          ? null
          : sourceAggregateBindings(source.node());
      SqlIdentifier soleWildcard = sourceProjects.size() == 1
              && stripAlias(sourceProjects.get(0)) instanceof SqlIdentifier identifier
              && identifier.isStar()
          ? (SqlIdentifier) stripAlias(sourceProjects.get(0))
          : null;
      boolean projectAggregateOwnedBySource = projectAggregate != null
          && projectSelect != null
          && sourceOwnsAggregate(projectSelect, projectAggregate);
      SourceWhereWildcardSegment wildcardSegment = soleWildcard == null
              || projectAggregateOwnedBySource
          ? null
          : sourceWhereWildcardInputSegment(project, source, soleWildcard);
      boolean wildcardOverInlinedInput = wildcardSegment != null;
      if (wildcardOverInlinedInput) {
        // A sole wildcard owns a relational output segment, not one scalar
        // expression.  An unqualified wildcard expands the complete input;
        // a qualified wildcard expands only the one exact visible base
        // relation found by sourceWhereWildcardInputSegment. Bind that
        // complete typed positional segment here, then let ordinary child
        // traversal authenticate the relation and its predicates.
        if (project.getProjects().size() != wildcardSegment.width()
            || project.getRowType().getFieldCount() != wildcardSegment.width()) {
          return false;
        }
        for (int i = 0; i < project.getProjects().size(); i++) {
          int inputIndex = wildcardSegment.start() + i;
          if (!(project.getProjects().get(i) instanceof RexInputRef inputRef)
              || inputRef.getIndex() != inputIndex
              || !inputRef.getType().equals(
                  project.getInput().getRowType().getFieldList().get(inputIndex).getType())
              || !inputRef.getType().equals(
                  project.getRowType().getFieldList().get(i).getType())) {
            return false;
          }
        }
      } else {
        if (!projectAggregateOwnedBySource
            && aggregateInputs.size() == project.getProjects().size()) {
          sourceProjects = aggregateInputs;
        } else if (sourceProjects.size() != project.getProjects().size()) {
          sourceProjects = aggregateInputs;
        }
        if (sourceProjects.size() != project.getProjects().size()) {
          return false;
        }
        for (int i = 0; i < project.getProjects().size(); i++) {
          boolean aligned = !projectAggregateOwnedBySource
              ? sourceWhereRexTreeAligned(
                  project.getProjects().get(i), sourceProjects.get(i), source.sourcePositions())
              : projectSelect != null
                  && projectAlignedAggregates != null
                  && projectSourceAggregates != null
                  && projectSourceAggregates.size() == projectAlignedAggregates.size()
                  && collectNativeHavingOperandBindings(
                      project.getProjects().get(i), sourceProjects.get(i), "$",
                      source.sourcePositions(),
                      projectAggregate, projectSelect, aggregateInputs,
                      projectSourceAggregates, new ArrayList<>());
          // A Project above a derived query can read an already-computed child
          // expression positionally.  Calcite keeps the exact inner definition
          // (for example a CASE expression) as that RexInputRef's source, so a
          // call-shaped source node is not itself a generated RexCall here.
          // Admit only the direct, type-identical positional carrier.  Rust
          // subsequently closes the definition against the complete child
          // relation and rejects swapped or cross-scope positions before using
          // this serialized snapshot.
          if (!aligned
              && !projectAggregateOwnedBySource
              && project.getProjects().get(i) instanceof RexInputRef inputRef
              && !(stripAlias(sourceProjects.get(i)) instanceof SqlIdentifier)
              && !isQuerySourceNode(stripAlias(sourceProjects.get(i)))
              && inputRef.getIndex() >= 0
              && inputRef.getIndex() < project.getInput().getRowType().getFieldCount()
              && inputRef.getType().equals(
                  project.getInput().getRowType().getFieldList().get(inputRef.getIndex()).getType())
              && inputRef.getType().equals(
                  project.getRowType().getFieldList().get(i).getType())) {
            aligned = true;
          }
          if (!aligned) {
            return false;
          }
        }
      }
    } else if (rel instanceof Aggregate aggregate) {
      if (rel.getInputs().size() != 1
          || alignedSourceAggregateCalls(aggregate, source.node()) == null) {
        return false;
      }
      List<Integer> sourceGroups = sourceWhereAggregateGroupIndexes(aggregate, source.node());
      if (sourceGroups == null
          || !aggregate.getGroupSet().asList().equals(sourceGroups)
          || aggregate.getGroupSets().size() != 1
          || !aggregate.getGroupSets().get(0).asList().equals(sourceGroups)) {
        return false;
      }
    } else if (rel instanceof Join join) {
      SqlSelect select = topLevelSelect(source.node());
      SqlNode from = select == null ? source.node() : stripAlias(select.getFrom());
      if (rel.getInputs().size() != 2 || !(from instanceof SqlJoin)) {
        return false;
      }
      SqlNode condition = topLevelJoinCondition(source.node());
      String sourceJoinType = sourceWhereJoinType(source.node());
      if (sourceJoinType == null
          || !join.getJoinType().name().equals(sourceJoinType)) {
        return false;
      }
      if (condition == null) {
        if (!join.getCondition().isAlwaysTrue()) {
          return false;
        }
      } else if (!sourceWhereRexTreeAligned(
          join.getCondition(), condition, source.sourcePositions())) {
        return false;
      }
    } else if (rel instanceof SetOp setOp) {
      SqlNode setSource = sourceSetExpression(source.node());
      if (!(setSource instanceof SqlCall call)
          || !sourceSetOperationMatches(setOp, call)) {
        return false;
      }
    } else if (rel instanceof Sort sort) {
      if (rel.getInputs().size() != 1 || !sort.getCollation().getFieldCollations().isEmpty()) {
        return false;
      }
      SqlNode query = source.node();
      if (!(query instanceof SqlOrderBy orderBy)) {
        return false;
      }
      if (hasSourceItems(orderBy.orderList)) {
        // An empty generated collation cannot attest a nonempty source order,
        // even when Calcite retained OFFSET/FETCH as a zero-key Sort.
        return false;
      }
      if ((sort.fetch == null) != (orderBy.fetch == null)
          || (sort.offset == null) != (orderBy.offset == null)
          || sort.fetch != null
              && !sourceWhereRexTreeAligned(
                  sort.fetch, orderBy.fetch, source.sourcePositions())
          || sort.offset != null
              && !sourceWhereRexTreeAligned(
                  sort.offset, orderBy.offset, source.sourcePositions())) {
        return false;
      }
    } else if (rel instanceof Values) {
      // A source VALUES relation needs its own ordered-cell attestation.  The
      // synthetic one-row Values input of a no-FROM SELECT is handled at its
      // exact owning Project edge below and is never treated as source VALUES.
      return false;
    } else {
      return false;
    }

    return true;
  }

  /**
   * Build a compositional source/generated correspondence for one Rex
   * subquery.  Each operator is checked only against its own exact source role
   * and typed inputs; child correspondences are then constructed recursively
   * in generated input order.  This deliberately avoids requiring the source
   * AST and Rel tree to be isomorphic: Calcite may add legal Projects, casts,
   * and aggregate carriers, but every carrier must expose complete ordered
   * input-column lineage and every source expression remains exact-span bound.
   */
  private static SourceRelCorrespondence sourceSubqueryRelCorrespondence(
      RelNode rel, SourceContext source) {
    if (!sourceRelOperatorCorresponds(rel, source)
        || source.sourcePositions() == null
        || source.queryBlockId() == null) {
      return null;
    }
    ExactSourceIdentity owner = source.sourcePositions().relationalSourceIdentity(source.node());
    if (owner == null || owner.text().isEmpty()) {
      return null;
    }
    List<SourceRelOutputLineage> outputs = sourceRelOutputLineage(rel, source, owner);
    if (outputs == null || outputs.size() != rel.getRowType().getFieldCount()) {
      return null;
    }

    List<SourceRelCorrespondence> inputs = new ArrayList<>();
    for (int i = 0; i < rel.getInputs().size(); i++) {
      SourceContext child = sourceForRelInput(rel, source, i);
      RelNode generatedChild = rel.getInput(i);
      if (child.node() == null
          && rel instanceof Project project
          && generatedChild instanceof Values values
          && sourceWhereSyntheticNoFromValues(project, source, values)) {
        List<SourceRelOutputLineage> unitOutput = List.of(
            new SourceRelOutputLineage(
                0,
                "SYNTHETIC_UNIT",
                generatedChild.getRowType().getFieldList().get(0).getName(),
                null,
                List.of()));
        inputs.add(new SourceRelCorrespondence(
            "GENERATED_NO_FROM_UNIT",
            generatedChild.getRelTypeName(),
            source.queryBlockId(),
            owner,
            unitOutput,
            List.of()));
        continue;
      }
      if (child.node() == null) {
        return null;
      }
      SourceRelCorrespondence childCorrespondence =
          sourceSubqueryRelCorrespondence(generatedChild, child);
      if (childCorrespondence == null) {
        return null;
      }
      inputs.add(childCorrespondence);
    }
    return new SourceRelCorrespondence(
        "SOURCE_RELATION",
        rel.getRelTypeName(),
        source.queryBlockId(),
        owner,
        List.copyOf(outputs),
        List.copyOf(inputs));
  }

  private static List<SourceRelOutputLineage> sourceRelOutputLineage(
      RelNode rel, SourceContext source, ExactSourceIdentity owner) {
    List<SourceRelOutputLineage> outputs = new ArrayList<>();
    if (rel instanceof TableScan scan) {
      SqlSelect select = topLevelSelect(source.node());
      SqlNode relation = select == null ? source.node() : select.getFrom();
      DirectTableSource table = directTableSource(relation, scan);
      if (table == null) {
        return null;
      }
      for (int i = 0; i < scan.getRowType().getFieldCount(); i++) {
        ExactSourceIdentity alias = i < table.columnAliases().size()
            ? source.sourcePositions().exactIdentity(table.columnAliases().get(i))
            : null;
        if (i < table.columnAliases().size() && alias == null) {
          return null;
        }
        outputs.add(new SourceRelOutputLineage(
            i,
            "BASE_COLUMN",
            scan.getRowType().getFieldList().get(i).getName(),
            alias == null ? owner : alias,
            List.of()));
      }
      return outputs;
    }
    if (rel instanceof Filter || rel instanceof Sort) {
      if (rel.getInputs().size() != 1
          || rel.getInput(0).getRowType().getFieldCount()
              != rel.getRowType().getFieldCount()) {
        return null;
      }
      for (int i = 0; i < rel.getRowType().getFieldCount(); i++) {
        if (!rel.getRowType().getFieldList().get(i).getType().equals(
            rel.getInput(0).getRowType().getFieldList().get(i).getType())) {
          return null;
        }
        outputs.add(new SourceRelOutputLineage(
            i,
            "PASSTHROUGH",
            rel.getRowType().getFieldList().get(i).getName(),
            owner,
            List.of(new SourceRelInputColumn(0, i))));
      }
      return outputs;
    }
    if (rel instanceof Project project) {
      List<SqlNode> roles = sourceProjectOutputRoles(project, source);
      for (int i = 0; i < project.getProjects().size(); i++) {
        RexNode rex = project.getProjects().get(i);
        List<SourceRelInputColumn> inputs = sourceRelProjectInputs(project, rex);
        if (inputs == null) {
          return null;
        }
        ExactSourceIdentity expression = i < roles.size() && roles.get(i) != null
            ? source.sourcePositions().expressionIdentity(stripAlias(roles.get(i)))
            : null;
        if (inputs.isEmpty() && expression == null) {
          return null;
        }
        if (rex instanceof RexInputRef inputRef
            && (inputRef.getIndex() < 0
                || inputRef.getIndex() >= project.getInput().getRowType().getFieldCount()
                || !inputRef.getType().equals(
                    project.getInput().getRowType().getFieldList().get(inputRef.getIndex()).getType()))) {
          return null;
        }
        outputs.add(new SourceRelOutputLineage(
            i,
            rex instanceof RexInputRef ? "PROJECTED_INPUT" : "SOURCE_EXPRESSION",
            project.getRowType().getFieldList().get(i).getName(),
            expression,
            inputs));
      }
      return outputs;
    }
    if (rel instanceof Aggregate aggregate) {
      List<Integer> groups = aggregate.getGroupSet().asList();
      List<SqlCall> calls = alignedSourceAggregateCalls(aggregate, source.node());
      if (calls == null
          || aggregate.getRowType().getFieldCount()
              != groups.size() + aggregate.getAggCallList().size()) {
        return null;
      }
      for (int i = 0; i < groups.size(); i++) {
        int inputIndex = groups.get(i);
        if (inputIndex < 0 || inputIndex >= aggregate.getInput().getRowType().getFieldCount()) {
          return null;
        }
        outputs.add(new SourceRelOutputLineage(
            i,
            "GROUP_KEY",
            aggregate.getRowType().getFieldList().get(i).getName(),
            owner,
            List.of(new SourceRelInputColumn(0, inputIndex))));
      }
      for (int i = 0; i < calls.size(); i++) {
        ExactSourceIdentity call = source.sourcePositions().expressionIdentity(calls.get(i));
        if (call == null) {
          return null;
        }
        int outputIndex = groups.size() + i;
        List<SourceRelInputColumn> arguments = new ArrayList<>();
        for (int inputIndex : aggregate.getAggCallList().get(i).getArgList()) {
          if (inputIndex < 0 || inputIndex >= aggregate.getInput().getRowType().getFieldCount()) {
            return null;
          }
          arguments.add(new SourceRelInputColumn(0, inputIndex));
        }
        outputs.add(new SourceRelOutputLineage(
            outputIndex,
            "AGGREGATE_CALL",
            aggregate.getRowType().getFieldList().get(outputIndex).getName(),
            call,
            List.copyOf(arguments)));
      }
      return outputs;
    }
    if (rel instanceof Join join) {
      int leftArity = join.getLeft().getRowType().getFieldCount();
      int rightArity = join.getRight().getRowType().getFieldCount();
      if (leftArity + rightArity != join.getRowType().getFieldCount()) {
        return null;
      }
      for (int i = 0; i < join.getRowType().getFieldCount(); i++) {
        int inputOrdinal = i < leftArity ? 0 : 1;
        int inputIndex = i < leftArity ? i : i - leftArity;
        outputs.add(new SourceRelOutputLineage(
            i,
            "JOIN_INPUT",
            join.getRowType().getFieldList().get(i).getName(),
            owner,
            List.of(new SourceRelInputColumn(inputOrdinal, inputIndex))));
      }
      return outputs;
    }
    if (rel instanceof SetOp set) {
      for (RelNode input : set.getInputs()) {
        if (input.getRowType().getFieldCount() != set.getRowType().getFieldCount()) {
          return null;
        }
      }
      for (int i = 0; i < set.getRowType().getFieldCount(); i++) {
        List<SourceRelInputColumn> alternatives = new ArrayList<>();
        for (int input = 0; input < set.getInputs().size(); input++) {
          alternatives.add(new SourceRelInputColumn(input, i));
        }
        outputs.add(new SourceRelOutputLineage(
            i,
            "SET_COLUMN",
            set.getRowType().getFieldList().get(i).getName(),
            owner,
            List.copyOf(alternatives)));
      }
      return outputs;
    }
    return null;
  }

  /**
   * Record every local input column read by one Project expression in stable
   * first-use order.  Calls (including generated casts and CASE/COALESCE
   * normalizations) retain their exact source-expression authority while
   * still exposing complete child-column dependencies.  Correlated fields
   * are intentionally not recast as local inputs; their correlation binding
   * is authenticated by the ordinary Rex metadata.
   */
  private static List<SourceRelInputColumn> sourceRelProjectInputs(
      Project project, RexNode rex) {
    List<Integer> indexes = new ArrayList<>();
    Set<Integer> seen = new HashSet<>();
    if (!collectSourceRelProjectInputIndexes(
        rex, project.getInput().getRowType(), indexes, seen)) {
      return null;
    }
    List<SourceRelInputColumn> inputs = new ArrayList<>();
    for (int index : indexes) {
      inputs.add(new SourceRelInputColumn(0, index));
    }
    return List.copyOf(inputs);
  }

  private static boolean collectSourceRelProjectInputIndexes(
      RexNode rex,
      RelDataType inputType,
      List<Integer> indexes,
      Set<Integer> seen) {
    if (rex instanceof RexInputRef inputRef) {
      int index = inputRef.getIndex();
      if (index < 0
          || index >= inputType.getFieldCount()
          || !inputRef.getType().equals(inputType.getFieldList().get(index).getType())) {
        return false;
      }
      if (seen.add(index)) {
        indexes.add(index);
      }
      return true;
    }
    if (rex instanceof RexFieldAccess fieldAccess) {
      return collectSourceRelProjectInputIndexes(
          fieldAccess.getReferenceExpr(), inputType, indexes, seen);
    }
    if (rex instanceof RexOver over) {
      for (RexNode operand : over.getOperands()) {
        if (!collectSourceRelProjectInputIndexes(operand, inputType, indexes, seen)) {
          return false;
        }
      }
      for (RexNode partition : over.getWindow().partitionKeys) {
        if (!collectSourceRelProjectInputIndexes(partition, inputType, indexes, seen)) {
          return false;
        }
      }
      for (RexFieldCollation order : over.getWindow().orderKeys) {
        if (!collectSourceRelProjectInputIndexes(order.left, inputType, indexes, seen)) {
          return false;
        }
      }
      RexWindowBound lower = over.getWindow().getLowerBound();
      RexWindowBound upper = over.getWindow().getUpperBound();
      return (lower == null
              || lower.getOffset() == null
              || collectSourceRelProjectInputIndexes(
                  lower.getOffset(), inputType, indexes, seen))
          && (upper == null
              || upper.getOffset() == null
              || collectSourceRelProjectInputIndexes(
                  upper.getOffset(), inputType, indexes, seen));
    }
    if (rex instanceof RexCall call) {
      for (RexNode operand : call.getOperands()) {
        if (!collectSourceRelProjectInputIndexes(operand, inputType, indexes, seen)) {
          return false;
        }
      }
      return true;
    }
    return rex instanceof RexLiteral || rex instanceof RexCorrelVariable;
  }

  private static List<SqlNode> sourceProjectOutputRoles(
      Project project, SourceContext source) {
    List<SqlNode> roles = topLevelSelectItemRoles(source.node());
    if (roles.size() == project.getProjects().size()) {
      return roles;
    }
    if (roles.size() == 1
        && stripAlias(roles.get(0)) instanceof SqlIdentifier wildcard
        && wildcard.isStar()) {
      List<SqlNode> expanded = new ArrayList<>();
      for (int i = 0; i < project.getProjects().size(); i++) {
        expanded.add(wildcard);
      }
      return expanded;
    }
    List<SqlNode> aggregateRoles = new ArrayList<>();
    for (AggregateInputSource binding : aggregateInputSources(source.node(), source)) {
      aggregateRoles.add(binding.role());
    }
    if (aggregateRoles.size() == project.getProjects().size()) {
      return aggregateRoles;
    }
    // A generated pass-through Project may have more positions than the
    // source SELECT list (for example hidden ordering/grouping carriers).
    // Its direct RexInputRefs remain fully bound through child ordinals; no
    // unrelated source expression is fabricated for those positions.
    List<SqlNode> partial = new ArrayList<>();
    for (int i = 0; i < project.getProjects().size(); i++) {
      partial.add(i < roles.size() ? roles.get(i) : null);
    }
    return partial;
  }

  private static void emitSourceRelCorrespondence(
      Json out, SourceRelCorrespondence correspondence) {
    out.beginObject();
    out.name("kind").value("COMPOSITIONAL_RELATION_CORRESPONDENCE_V1");
    out.comma();
    out.name("sourceRole").value(correspondence.sourceRole());
    out.comma();
    out.name("generatedType").value(correspondence.generatedType());
    out.comma();
    out.name("queryBlockId").value(correspondence.queryBlockId());
    out.comma();
    out.name("sourceNodeId").value(correspondence.source().nodeId());
    out.comma();
    out.name("sourceText").value(correspondence.source().text());
    out.comma();
    out.name("outputLineage");
    out.beginArray();
    for (int i = 0; i < correspondence.outputs().size(); i++) {
      if (i > 0) {
        out.comma();
      }
      SourceRelOutputLineage lineage = correspondence.outputs().get(i);
      out.beginObject();
      out.name("outputIndex").value(lineage.outputIndex());
      out.comma();
      out.name("kind").value(lineage.kind());
      out.comma();
      out.name("generatedFieldName").value(lineage.generatedFieldName());
      if (lineage.source() != null) {
        out.comma();
        out.name("sourceNodeId").value(lineage.source().nodeId());
        out.comma();
        out.name("sourceText").value(lineage.source().text());
      }
      out.comma();
      out.name("inputs");
      out.beginArray();
      for (int j = 0; j < lineage.inputs().size(); j++) {
        if (j > 0) {
          out.comma();
        }
        SourceRelInputColumn input = lineage.inputs().get(j);
        out.beginObject();
        out.name("inputOrdinal").value(input.inputOrdinal());
        out.comma();
        out.name("inputOutputIndex").value(input.inputOutputIndex());
        out.endObject();
      }
      out.endArray();
      out.endObject();
    }
    out.endArray();
    out.comma();
    out.name("inputs");
    out.beginArray();
    for (int i = 0; i < correspondence.inputs().size(); i++) {
      if (i > 0) {
        out.comma();
      }
      out.beginObject();
      out.name("inputOrdinal").value(i);
      out.comma();
      out.name("correspondence");
      emitSourceRelCorrespondence(out, correspondence.inputs().get(i));
      out.endObject();
    }
    out.endArray();
    out.endObject();
  }

  /**
   * Resolve one exact sole SELECT wildcard to the generated input segment it
   * denotes. PostgreSQL's {@code *} expands the whole FROM namespace, while
   * {@code relation.*} expands one visible relation. For the qualified form,
   * require every generated position to trace through row-preserving
   * Filter/Sort and Join nodes to one and the same exact base-table relation,
   * in complete table-column order. A duplicate/noncontiguous qualifier or a
   * derived shape that cannot be reconstructed this way remains unsupported.
   */
  private static SourceWhereWildcardSegment sourceWhereWildcardInputSegment(
      Project project, SourceContext source, SqlIdentifier wildcard) {
    if (!wildcard.isStar()
        || wildcard.names.isEmpty()
        || source.sourcePositions() == null
        || source.sourcePositions().exactIdentity(wildcard) == null) {
      return null;
    }
    RelNode input = project.getInput();
    if (wildcard.names.size() == 1) {
      return new SourceWhereWildcardSegment(0, input.getRowType().getFieldCount());
    }

    SqlSelect select = topLevelSelect(source.node());
    if (select == null || select.getFrom() == null) {
      return null;
    }
    SqlIdentifier qualifier = wildcard.getComponent(0, wildcard.names.size() - 1);
    SourceWhereInputOrigin first = null;
    int start = -1;
    int width = 0;
    boolean segmentEnded = false;
    for (int index = 0; index < input.getRowType().getFieldCount(); index++) {
      SourceWhereInputOrigin origin = sourceWhereInputOrigin(
          input, select.getFrom(), index, source.sourcePositions());
      boolean matches = origin != null
          && sourceWhereWildcardQualifierMatches(qualifier, origin.sourceTable());
      if (!matches) {
        if (width > 0) {
          segmentEnded = true;
        }
        continue;
      }
      if (segmentEnded) {
        return null;
      }
      if (first == null) {
        first = origin;
        start = index;
      } else if (origin.scan() != first.scan()
          || !origin.sourceRelationNodeId().equals(first.sourceRelationNodeId())) {
        // The same visible spelling reached a second relation. PostgreSQL
        // would not treat that as one wildcard expansion, so fail closed.
        return null;
      }
      if (origin.tableFieldIndex() != width) {
        return null;
      }
      width++;
    }
    if (first == null
        || width != first.scan().getRowType().getFieldCount()
        || start < 0
        || start + width > input.getRowType().getFieldCount()) {
      return null;
    }
    for (int index = 0; index < width; index++) {
      if (!input.getRowType().getFieldList().get(start + index).getType().equals(
          first.scan().getRowType().getFieldList().get(index).getType())) {
        return null;
      }
    }
    return new SourceWhereWildcardSegment(start, width);
  }

  private static boolean sourceWhereWildcardQualifierMatches(
      SqlIdentifier qualifier, DirectTableSource sourceTable) {
    if (sourceTable.alias() != null) {
      // A table alias hides the base relation name in PostgreSQL.
      return samePostgresIdentifier(qualifier, sourceTable.alias());
    }
    boolean fullTableName = samePostgresIdentifier(qualifier, sourceTable.table());
    boolean simpleTableName = qualifier.isSimple()
        && qualifier.names.get(0).equals(
            sourceTable.table().names.get(sourceTable.table().names.size() - 1));
    return fullTableName || simpleTableName;
  }

  /** Calcite implements a no-FROM SELECT over one synthetic integer-zero row.
   * Authenticate only that exact dead input at its owning SELECT Project; the
   * projected source expressions must not read the dummy field. Rust repeats
   * the full tuple/type/provenance check before conversion. */
  private static boolean sourceWhereSyntheticNoFromValues(
      Project project, SourceContext source, Values values) {
    SqlSelect select = topLevelSelect(source.node());
    if (select == null
        || select.getFrom() != null
        || project.getInputs().size() != 1
        || project.getInput() != values
        || values.getInputs().size() != 0
        || values.getRowType().getFieldCount() != 1
        || values.getTuples().size() != 1
        || values.getTuples().get(0).size() != 1
        || project.getProjects().stream().anyMatch(
            CalciteIrCli::sourceWhereRexReadsInput)) {
      return false;
    }
    RexLiteral zero = values.getTuples().get(0).get(0);
    var field = values.getRowType().getFieldList().get(0);
    return field.getName().equals("ZERO")
        && field.getType().getSqlTypeName() == SqlTypeName.INTEGER
        && !field.getType().isNullable()
        && zero.getType().getSqlTypeName() == SqlTypeName.INTEGER
        && !zero.getType().isNullable()
        && zero.toString().equals("0");
  }

  private static boolean sourceWhereRexReadsInput(RexNode rex) {
    if (rex instanceof RexInputRef || rex instanceof RexFieldAccess) {
      return true;
    }
    if (rex instanceof RexCall call) {
      for (RexNode operand : call.getOperands()) {
        if (sourceWhereRexReadsInput(operand)) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Recover a PostgreSQL ORDER BY that Calcite erases under IN. This does not
   * authorize dropping the order: it supplies closed source/typed evidence
   * for Rust to reconstruct the declarative Sort first. The association is
   * entirely structural and applies to any direct-table query block with one
   * projected field and one independently bound ordering field.
   */
  private static SourceInSubqueryOrderAttestation sourceInSubqueryOrderAttestation(
      RexSubQuery subQuery, SqlNode sourceNode,
      SourcePositionMap sourcePositions) {
    SqlNode nested = subquerySource(sourceNode);
    if (!subQuery.getKind().name().equals("IN")
        || subQuery.getOperands().size() != 1
        || !(nested instanceof SqlOrderBy orderBy)
        || orderBy.fetch != null
        || orderBy.offset != null
        || orderBy.orderList == null
        || orderBy.orderList.size() != 1
        || !(orderBy.orderList.get(0) instanceof SqlIdentifier orderItem)
        || !(orderBy.query instanceof SqlSelect select)
        || select.isDistinct()
        || select.getHaving() != null
        || select.getQualify() != null
        || select.getOffset() != null
        || select.getFetch() != null
        || select.hasHints()
        || hasSourceItems(select.getGroup())
        || hasSourceItems(select.getWindowList())
        || hasSourceItems(select.getOrderList())
        || select.getSelectList() == null
        || select.getSelectList().size() != 1
        || !(stripAlias(select.getSelectList().get(0))
            instanceof SqlIdentifier projectItem)
        || !(subQuery.rel instanceof Project project)
        || project.getVariablesSet().size() != 0
        || project.getProjects().size() != 1
        || !(project.getProjects().get(0) instanceof RexInputRef projectRef)
        || project.getInputs().size() != 1
        || !(project.getInput() instanceof Filter filter)
        || !filter.getVariablesSet().isEmpty()
        || filter.getInputs().size() != 1
        || !(filter.getInput() instanceof TableScan scan)
        || !scan.getInputs().isEmpty()
        || project.getRowType().getFieldCount() != 1
        || filter.getRowType().getFieldCount() != scan.getRowType().getFieldCount()
        || !filter.getRowType().equals(scan.getRowType())
        || !sourceWhereNestedBaseNamesUnique(subQuery.rel)) {
      return null;
    }

    DirectTableSource sourceTable = directTableSource(select.getFrom(), scan);
    Integer projectIndex = sourceTable == null
        ? null
        : directTableFieldIndex(projectItem, sourceTable, scan);
    Integer orderIndex = sourceTable == null
        ? null
        : directTableFieldIndex(orderItem, sourceTable, scan);
    ExactSourceIdentity selectIdentity = sourcePositions == null
        ? null
        : sourcePositions.queryBlockIdentity(select);
    String queryBlockId = selectIdentity == null ? null : selectIdentity.nodeId();
    String selectNodeId = queryBlockId;
    String orderByNodeId = sourceNodeId(sourcePositions, orderBy);
    String projectItemNodeId = sourceNodeId(sourcePositions, projectItem);
    String orderItemNodeId = sourceNodeId(sourcePositions, orderItem);
    String relationNodeId = sourceNodeId(sourcePositions, stripAlias(select.getFrom()));
    String selectText = selectIdentity == null ? null : selectIdentity.text();
    String orderByText = sourceTextAtNode(sourcePositions, orderBy);
    String projectItemText = sourceTextAtNode(sourcePositions, projectItem);
    String orderItemText = sourceTextAtNode(sourcePositions, orderItem);
    String relationText = sourceTextAtNode(sourcePositions, stripAlias(select.getFrom()));
    if (sourceTable == null
        || projectIndex == null
        || projectIndex != projectRef.getIndex()
        || orderIndex == null
        || projectIndex == orderIndex
        || queryBlockId == null
        || selectNodeId == null
        || !queryBlockId.equals(selectNodeId)
        || orderByNodeId == null
        || projectItemNodeId == null
        || orderItemNodeId == null
        || relationNodeId == null
        || selectText == null
        || orderByText == null
        || projectItemText == null
        || orderItemText == null
        || relationText == null
        || sourceSubqueryRelCorrespondence(
            project, SourceContext.root(select, sourcePositions)) == null) {
      return null;
    }

    var projectField = scan.getRowType().getFieldList().get(projectIndex);
    var orderField = scan.getRowType().getFieldList().get(orderIndex);
    return new SourceInSubqueryOrderAttestation(
        POSTGRES_IN_SUBQUERY_LOST_ORDER_BY,
        queryBlockId,
        selectNodeId,
        selectText,
        orderByNodeId,
        orderByText,
        select.toString(),
        orderBy.toString(),
        projectItemNodeId,
        projectItemText,
        projectItem.toString(),
        projectIndex,
        projectField.getName(),
        projectField.getType().getFullTypeString(),
        projectField.getType().isNullable(),
        orderItemNodeId,
        orderItemText,
        orderItem.toString(),
        "ASCENDING",
        "LAST",
        relationNodeId,
        relationText,
        stripAlias(select.getFrom()).toString(),
        scan.getTable().getQualifiedName(),
        orderIndex,
        orderField.getName(),
        orderField.getType().getFullTypeString(),
        orderField.getType().isNullable(),
        project.getRowType().getFieldCount(),
        filter.getRowType().getFieldCount());
  }

  private static void emitSourceInSubqueryOrderAttestation(
      Json out, SourceInSubqueryOrderAttestation attestation) {
    out.beginObject();
    out.name("kind").value(attestation.kind());
    out.comma();
    out.name("queryBlockId").value(attestation.queryBlockId());
    out.comma();
    out.name("selectNodeId").value(attestation.selectNodeId());
    out.comma();
    out.name("selectText").value(attestation.selectText());
    out.comma();
    out.name("orderByNodeId").value(attestation.orderByNodeId());
    out.comma();
    out.name("orderByText").value(attestation.orderByText());
    out.comma();
    out.name("sourceSelectSql").value(attestation.sourceSelectSql());
    out.comma();
    out.name("sourceOrderBySql").value(attestation.sourceOrderBySql());
    out.comma();
    out.name("projectItemNodeId").value(attestation.projectItemNodeId());
    out.comma();
    out.name("projectItemText").value(attestation.projectItemText());
    out.comma();
    out.name("sourceProjectItemSql").value(attestation.sourceProjectItemSql());
    out.comma();
    out.name("projectInputIndex").value(attestation.projectInputIndex());
    out.comma();
    out.name("projectBaseFieldName").value(attestation.projectBaseFieldName());
    out.comma();
    out.name("projectFieldType").value(attestation.projectFieldType());
    out.comma();
    out.name("projectFieldNullable").value(attestation.projectFieldNullable());
    out.comma();
    out.name("orderItemNodeId").value(attestation.orderItemNodeId());
    out.comma();
    out.name("orderItemText").value(attestation.orderItemText());
    out.comma();
    out.name("sourceOrderItemSql").value(attestation.sourceOrderItemSql());
    out.comma();
    out.name("direction").value(attestation.direction());
    out.comma();
    out.name("nullDirection").value(attestation.nullDirection());
    out.comma();
    out.name("sourceRelationNodeId").value(attestation.sourceRelationNodeId());
    out.comma();
    out.name("sourceRelationText").value(attestation.sourceRelationText());
    out.comma();
    out.name("sourceRelationSql").value(attestation.sourceRelationSql());
    out.comma();
    out.name("baseTable");
    out.beginArray();
    for (int i = 0; i < attestation.baseTable().size(); i++) {
      if (i > 0) {
        out.comma();
      }
      out.value(attestation.baseTable().get(i));
    }
    out.endArray();
    out.comma();
    out.name("orderFieldIndex").value(attestation.orderFieldIndex());
    out.comma();
    out.name("orderBaseFieldName").value(attestation.orderBaseFieldName());
    out.comma();
    out.name("orderFieldType").value(attestation.orderFieldType());
    out.comma();
    out.name("orderFieldNullable").value(attestation.orderFieldNullable());
    out.comma();
    out.name("generatedProjectArity").value(attestation.generatedProjectArity());
    out.comma();
    out.name("generatedSortInputArity").value(attestation.generatedSortInputArity());
    out.endObject();
  }

  private static List<Integer> sourceWhereAggregateGroupIndexes(
      Aggregate aggregate, SqlNode sourceNode) {
    SqlSelect select = topLevelSelect(sourceNode);
    if (select == null) {
      return null;
    }
    if (select.isDistinct()) {
      if (!aggregate.getAggCallList().isEmpty()
          || aggregate.getInput().getRowType().getFieldCount()
              != aggregate.getGroupSet().cardinality()) {
        return null;
      }
      List<Integer> indexes = new ArrayList<>();
      for (int i = 0; i < aggregate.getInput().getRowType().getFieldCount(); i++) {
        indexes.add(i);
      }
      return indexes;
    }
    SqlNodeList group = select.getGroup();
    if (group == null || group.isEmpty()) {
      return List.of();
    }
    List<SqlNode> inputs = aggregateInputExpressions(select);
    List<Integer> indexes = new ArrayList<>();
    for (SqlNode item : group) {
      String kind = item.getKind().name();
      if (kind.equals("GROUPING_SETS") || kind.equals("ROLLUP") || kind.equals("CUBE")) {
        return null;
      }
      int index = resolvedSourceExpressionIndex(select, inputs, stripAlias(item));
      if (index < 0 || indexes.contains(index)) {
        return null;
      }
      indexes.add(index);
    }
    return indexes;
  }

  private static boolean sourceWhereNestedBaseNamesUnique(RelNode rel) {
    List<String> names = new ArrayList<>();
    return collectUniqueSourceWhereBaseNames(rel, names);
  }

  private static boolean collectUniqueSourceWhereBaseNames(
      RelNode rel, List<String> names) {
    if (rel instanceof TableScan scan) {
      for (var field : scan.getRowType().getFieldList()) {
        if (names.contains(field.getName())) {
          return false;
        }
        names.add(field.getName());
      }
    }
    for (RelNode input : rel.getInputs()) {
      if (!collectUniqueSourceWhereBaseNames(input, names)) {
        return false;
      }
    }
    return true;
  }

  private static String sourceWhereJoinType(SqlNode sourceNode) {
    String syntax = sourceWhereJoinSyntax(sourceNode);
    if (syntax == null) {
      return null;
    }
    return switch (syntax) {
      case "COMMA", "CROSS", "INNER" -> "INNER";
      case "LEFT" -> "LEFT";
      case "RIGHT" -> "RIGHT";
      case "FULL" -> "FULL";
      default -> null;
    };
  }

  private static SqlJoin sourceWhereJoin(SqlNode sourceNode) {
    SqlSelect select = topLevelSelect(sourceNode);
    SqlNode from = select == null ? sourceNode : stripAlias(select.getFrom());
    if (!(stripAlias(from) instanceof SqlJoin join)) {
      return null;
    }
    return join;
  }

  private static String sourceWhereJoinSyntax(SqlNode sourceNode) {
    SqlJoin join = sourceWhereJoin(sourceNode);
    if (join == null) {
      return null;
    }
    return switch (join.getJoinType().name()) {
      case "COMMA" -> "COMMA";
      case "CROSS" -> "CROSS";
      case "INNER" -> "INNER";
      case "LEFT" -> "LEFT";
      case "RIGHT" -> "RIGHT";
      case "FULL" -> "FULL";
      default -> null;
    };
  }

  private static boolean sourceWhereRexOperatorAligned(RexCall rex, SqlNode sourceNode) {
    String rexKind = rex.getKind().name();
    if (rex instanceof RexSubQuery && isQuerySourceNode(stripAlias(sourceNode))) {
      return rexKind.equals("SCALAR_QUERY");
    }
    if (!(sourceNode instanceof SqlCall sourceCall)) {
      // Calcite's validator may add an implicit scalar CAST or boolean truth
      // test around one source leaf. sourceOperands deliberately maps that
      // same leaf through the unary wrapper.
      return rex.getOperands().size() == 1
          && (rexKind.equals("CAST")
              || rexKind.equals("IS_TRUE")
              || rexKind.equals("IS_FALSE")
              || rexKind.equals("IS_NOT_TRUE")
              || rexKind.equals("IS_NOT_FALSE"));
    }
    String sourceKind = sourceCall.getKind().name();
    if (rexKind.equals(sourceKind)) {
      return rex.getOperator().getName().equalsIgnoreCase(sourceCall.getOperator().getName());
    }
    if (rexKind.equals("CAST") && rex.getOperands().size() == 1) {
      return true;
    }
    if (rex.getOperands().size() == 1
        && (rexKind.equals("IS_TRUE")
            || rexKind.equals("IS_FALSE")
            || rexKind.equals("IS_NOT_TRUE")
            || rexKind.equals("IS_NOT_FALSE"))) {
      return true;
    }
    if (rexKind.equals("NOT") && rex.getOperands().size() == 1
        && sourceCall.getOperator().getName().toUpperCase(Locale.ROOT).startsWith("NOT ")) {
      return true;
    }
    if ((rexKind.equals("OR") || rexKind.equals("EQUALS"))
        && sourceKind.equals("IN")) {
      return true;
    }
    if (rexKind.equals("AND")
        && directAsymmetricBetween(sourceCall)
        && exactExpandedBetween(rex)) {
      return true;
    }
    if ((rexKind.equals("GREATER_THAN_OR_EQUAL") || rexKind.equals("LESS_THAN_OR_EQUAL"))
        && sourceKind.equals("BETWEEN")) {
      return true;
    }
    if (rexKind.equals("CASE")
        && (sourceCall.getOperator().getName().equalsIgnoreCase("COALESCE")
            || sourceCall.getOperator().getName().equalsIgnoreCase("NULLIF"))) {
      return true;
    }
    return rex instanceof RexSubQuery
        && (sourceKind.equals("EXISTS") || sourceKind.equals("IN"));
  }

  /**
   * Bind one declarative HAVING Filter immediately over its owning Aggregate.
   * The source query-block identity, the exact source condition node, every
   * generated aggregate call, and every positional Aggregate-output reference
   * must agree. This is independent of whether a PostgreSQL optimizer could
   * move a nonaggregate conjunct or choose any particular execution schedule.
   */
  private static SourceNativeHavingAttestation sourceNativeHavingAttestation(
      Filter filter, SourceContext source) {
    if (!"HAVING".equals(sourceFilterClause(filter, source))
        || !(filter.getInput() instanceof Aggregate aggregate)) {
      return null;
    }
    SqlSelect select = topLevelSelect(source.node());
    String queryBlockId = sourceQueryBlockId(select, source.sourcePositions());
    SqlNode sourceHaving = select == null ? null : select.getHaving();
    SqlNode alignedHaving = sourceFilterCondition(filter, source);
    ExactSourceIdentity ownerIdentity = source.sourcePositions() == null
        ? null
        : source.sourcePositions().relationalSourceIdentity(source.node());
    ExactSourceIdentity selectIdentity = source.sourcePositions() == null
        ? null
        : source.sourcePositions().queryBlockIdentity(select);
    String ownerNodeId = ownerIdentity == null ? null : ownerIdentity.nodeId();
    String conditionNodeId = sourceNodeId(source.sourcePositions(), sourceHaving);
    String sourceOwnerText = ownerIdentity == null ? null : ownerIdentity.text();
    String sourceSelectText = selectIdentity == null ? null : selectIdentity.text();
    String sourceConditionText = sourceTextAtNode(source.sourcePositions(), sourceHaving);
    if (queryBlockId == null
        || !queryBlockId.equals(source.queryBlockId())
        || sourceHaving == null
        || alignedHaving != sourceHaving
        || ownerNodeId == null
        || conditionNodeId == null
        || sourceOwnerText == null
        || sourceSelectText == null
        || sourceConditionText == null
        || filter.getInputs().size() != 1
        || !filter.getRowType().equals(aggregate.getRowType())
        || aggregate.getRowType().getFieldCount()
            != aggregate.getGroupSet().cardinality() + aggregate.getAggCallList().size()) {
      return null;
    }

    List<SqlCall> sourceAggregates = alignedSourceAggregateCalls(aggregate, select);
    if (sourceAggregates == null) {
      return null;
    }
    List<SourceAggregateBinding> aggregateBindings = sourceAggregateBindings(select);
    if (aggregateBindings.size() != sourceAggregates.size()) {
      return null;
    }
    List<SqlNode> aggregateInputs = aggregateInputExpressions(select);
    List<SourceNativeHavingOperandBinding> bindings = new ArrayList<>();
    if (!collectNativeHavingOperandBindings(
        filter.getCondition(), sourceHaving, "$",
        source.sourcePositions(),
        aggregate, select, aggregateInputs, aggregateBindings, bindings)) {
      return null;
    }
    return new SourceNativeHavingAttestation(
        "DECLARATIVE_HAVING",
        queryBlockId,
        ownerNodeId,
        source.node().toString(),
        sourceOwnerText,
        select.toString(),
        sourceSelectText,
        conditionNodeId,
        sourceHaving.toString(),
        sourceConditionText,
        filter.getCondition().toString(),
        aggregate.getRowType().getFieldCount(),
        aggregate.getAggCallList().size(),
        List.copyOf(bindings));
  }

  private static List<SqlIdentifier> groupingSetIdentifiers(SqlNode node) {
    SqlNode unaliased = stripAlias(node);
    List<SqlNode> members;
    if (unaliased instanceof SqlNodeList list) {
      members = list.getList();
    } else if (unaliased instanceof SqlCall row && row.getKind().name().equals("ROW")) {
      members = row.getOperandList();
    } else {
      members = List.of(unaliased);
    }
    List<SqlIdentifier> identifiers = new ArrayList<>();
    for (SqlNode member : members) {
      if (!(stripAlias(member) instanceof SqlIdentifier identifier)) {
        return null;
      }
      identifiers.add(identifier);
    }
    return identifiers;
  }

  /**
   * Collect Aggregate-output bindings through Calcite's exact two-argument
   * COALESCE normalization.  This is deliberately local to declarative
   * HAVING: an arbitrary generated {@code IS NOT NULL} must not be treated as
   * an implicit wrapper around an unrelated source expression.  The tested
   * and returned values must be the same complete Rex subtree after removing
   * only validator-generated result casts, and every surviving leaf is still
   * rebound recursively to its ordered source COALESCE operand.
   */
  private static boolean collectNativeHavingExpandedCoalesceBindings(
      RexCall generated, SqlNode sourceNode, String path,
      SourcePositionMap sourcePositions,
      Aggregate aggregate, SqlSelect select, List<SqlNode> aggregateInputs,
      List<SourceAggregateBinding> sourceAggregates,
      List<SourceNativeHavingOperandBinding> bindings) {
    if (!generated.getKind().name().equals("CASE")
        || !(sourceNode instanceof SqlCall source)
        || !source.getOperator().getName().equalsIgnoreCase("COALESCE")
        || source.getOperandList().size() != 2
        || generated.getOperands().size() != 3
        || !(generated.getOperands().get(0) instanceof RexCall condition)
        || !condition.getKind().name().equals("IS_NOT_NULL")
        || !condition.getOperator().getName().equalsIgnoreCase("IS NOT NULL")
        || condition.getOperands().size() != 1
        || condition.getType().getSqlTypeName() != SqlTypeName.BOOLEAN
        || condition.getType().isNullable()) {
      return false;
    }

    SqlNode sourceValue = source.getOperandList().get(0);
    SqlNode sourceFallback = source.getOperandList().get(1);
    RexNode tested = condition.getOperands().get(0);
    RexNode returned = generated.getOperands().get(1);
    RexNode returnedLeaf = returned;
    while (returnedLeaf instanceof RexCall cast
        && cast.getKind().name().equals("CAST")
        && cast.getOperands().size() == 1
        && (!(sourceValue instanceof SqlCall sourceCast)
            || !sourceCast.getKind().name().equals("CAST")
            || !sourceCastTargetMatchesRex(sourceCast, cast, sourcePositions))) {
      returnedLeaf = cast.getOperands().get(0);
    }
    if (!tested.equals(returnedLeaf)) {
      return false;
    }

    return collectNativeHavingOperandBindings(
            tested, sourceValue, path + ".0.0", sourcePositions,
            aggregate, select, aggregateInputs, sourceAggregates, bindings)
        && collectNativeHavingOperandBindings(
            returned, sourceValue, path + ".1", sourcePositions,
            aggregate, select, aggregateInputs, sourceAggregates, bindings)
        && collectNativeHavingOperandBindings(
            generated.getOperands().get(2), sourceFallback, path + ".2", sourcePositions,
            aggregate, select, aggregateInputs, sourceAggregates, bindings);
  }

  private static boolean collectNativeHavingOperandBindings(
      RexNode rex, SqlNode sourceNode, String path,
      SourcePositionMap sourcePositions,
      Aggregate aggregate, SqlSelect select, List<SqlNode> aggregateInputs,
      List<SourceAggregateBinding> sourceAggregates,
      List<SourceNativeHavingOperandBinding> bindings) {
    if (sourceNode == null) {
      // CASE without ELSE and Calcite's NULLIF expansion contain an implicit
      // NULL leaf that has no independently parsed source node.
      return rex instanceof RexLiteral literal && literal.getTypeName() == SqlTypeName.NULL;
    }
    if (rex instanceof RexInputRef inputRef) {
      if (!nativeHavingAggregateOutputMatchesSource(
          inputRef, sourceNode, aggregate, select, aggregateInputs, sourceAggregates)) {
        return false;
      }
      bindings.add(new SourceNativeHavingOperandBinding(
          path,
          inputRef.getIndex(),
          sourceNode.toString(),
          sourceNode.getKind().name(),
          sourceNode instanceof SqlCall call ? call.getOperator().getName() : null));
      return true;
    }
    if (rex instanceof RexOver over) {
      SqlNode unaliased = stripAlias(sourceNode);
      if (!(unaliased instanceof SqlCall sourceOver)
          || !sourceOver.getKind().name().equals("OVER")
          || sourceOver.getOperandList().isEmpty()
          || !(stripAlias(sourceOver.getOperandList().get(0))
              instanceof SqlCall sourceFunction)
          || !over.getOperator().getName()
              .equalsIgnoreCase(sourceFunction.getOperator().getName())
          || over.isDistinct() != sourceAggregateIsDistinct(sourceFunction)
          || over.getOperands().size() != sourceFunction.getOperandList().size()) {
        return false;
      }
      for (int i = 0; i < over.getOperands().size(); i++) {
        if (!collectNativeHavingOperandBindings(
            over.getOperands().get(i), sourceFunction.getOperandList().get(i), path + "." + i,
            sourcePositions,
            aggregate, select, aggregateInputs, sourceAggregates, bindings)) {
          return false;
        }
      }

      SqlWindow sourceWindow = directSourceWindow(sourceOver);
      RexWindow generatedWindow = over.getWindow();
      if (sourceWindow == null
          || sourceWindow.getPartitionList() == null
          || sourceWindow.getOrderList() == null
          || sourceWindow.getPartitionList().size() != generatedWindow.partitionKeys.size()
          || sourceWindow.getOrderList().size() != generatedWindow.orderKeys.size()) {
        return false;
      }
      for (int i = 0; i < generatedWindow.partitionKeys.size(); i++) {
        if (!collectNativeHavingOperandBindings(
            generatedWindow.partitionKeys.get(i), sourceWindow.getPartitionList().get(i),
            path + ".window.partition." + i,
            sourcePositions,
            aggregate, select, aggregateInputs, sourceAggregates, bindings)) {
          return false;
        }
      }
      for (int i = 0; i < generatedWindow.orderKeys.size(); i++) {
        SqlNode sourceOrder = sourceWindow.getOrderList().get(i);
        if (!sourceWindowOrderMatches(generatedWindow.orderKeys.get(i), sourceOrder)
            || !collectNativeHavingOperandBindings(
                generatedWindow.orderKeys.get(i).left, stripOrderByDecoration(sourceOrder),
                path + ".window.order." + i,
                sourcePositions,
                aggregate, select, aggregateInputs, sourceAggregates, bindings)) {
          return false;
        }
      }
      return true;
    }
    if (rex instanceof RexSubQuery subQuery) {
      // The subquery relational tree is recursively emitted and checked in its
      // own source query block. At this HAVING boundary, align the exact query
      // operand and bind every scalar operand that refers back to an Aggregate
      // output without conflating the two query blocks' provenance.
      if (subquerySource(sourceNode) == null
          || !sourceWhereRexOperatorAligned(subQuery, sourceNode)) {
        return false;
      }
      if (subQuery.getOperands().isEmpty()) {
        return true;
      }
      List<SqlNode> sourceChildren = new ArrayList<>();
      for (SqlNode candidate : sourceOperands(subQuery, sourceNode, sourcePositions)) {
        if (!isQuerySourceNode(stripAlias(candidate))) {
          sourceChildren.add(candidate);
        }
      }
      if (sourceChildren.size() != subQuery.getOperands().size()) {
        return false;
      }
      for (int i = 0; i < subQuery.getOperands().size(); i++) {
        if (!collectNativeHavingOperandBindings(
            subQuery.getOperands().get(i), sourceChildren.get(i), path + "." + i,
            sourcePositions,
            aggregate, select, aggregateInputs, sourceAggregates, bindings)) {
          return false;
        }
      }
      return true;
    }
    if (rex instanceof RexCall call) {
      if (call.getKind().name().equals("CASE")
          && sourceNode instanceof SqlCall sourceCall
          && sourceCall.getOperator().getName().equalsIgnoreCase("COALESCE")) {
        return collectNativeHavingExpandedCoalesceBindings(
            call, sourceNode, path, sourcePositions,
            aggregate, select, aggregateInputs, sourceAggregates, bindings);
      }
      if (!sourceWhereRexOperatorAligned(call, sourceNode)) {
        return false;
      }
      List<SqlNode> sourceChildren = sourceOperands(call, sourceNode, sourcePositions);
      if (sourceChildren.size() != call.getOperands().size()) {
        return false;
      }
      for (int i = 0; i < call.getOperands().size(); i++) {
        if (!collectNativeHavingOperandBindings(
            call.getOperands().get(i), sourceChildren.get(i), path + "." + i,
            sourcePositions,
            aggregate, select, aggregateInputs, sourceAggregates, bindings)) {
          return false;
        }
      }
      return true;
    }
    return rex instanceof RexLiteral && sourceNode instanceof SqlLiteral;
  }

  private static boolean nativeHavingAggregateOutputMatchesSource(
      RexInputRef inputRef, SqlNode sourceNode, Aggregate aggregate, SqlSelect select,
      List<SqlNode> aggregateInputs, List<SourceAggregateBinding> sourceAggregates) {
    int outputIndex = inputRef.getIndex();
    if (outputIndex < 0 || outputIndex >= aggregate.getRowType().getFieldCount()
        || !inputRef.getType().equals(
            aggregate.getRowType().getFieldList().get(outputIndex).getType())) {
      return false;
    }

    List<Integer> groupInputs = aggregate.getGroupSet().asList();
    if (outputIndex < groupInputs.size()) {
      int sourceInputIndex = resolvedSourceExpressionIndex(
          select, aggregateInputs, stripAlias(sourceNode));
      return sourceInputIndex == groupInputs.get(outputIndex);
    }

    int aggregateIndex = outputIndex - groupInputs.size();
    return aggregateIndex >= 0
        && aggregateIndex < sourceAggregates.size()
        && nativeHavingSourceAggregateMatches(
            sourceNode, sourceAggregates.get(aggregateIndex));
  }

  private static boolean nativeHavingSourceAggregateMatches(
      SqlNode sourceNode, SourceAggregateBinding expected) {
    SqlNode unaliased = stripAlias(sourceNode);
    if (expected.filter() == null) {
      return unaliased instanceof SqlCall call
          && isSourceAggregateCall(call)
          && call.toString().equals(expected.call().toString());
    }
    if (!(unaliased instanceof SqlCall filter)
        || !filter.getOperator().getName().equalsIgnoreCase("FILTER")
        || filter.getOperandList().size() < 2
        || !(stripAlias(filter.getOperandList().get(0)) instanceof SqlCall aggregateCall)
        || !isSourceAggregateCall(aggregateCall)) {
      return false;
    }
    SqlNode sourceFilter = singleSourceNode(filter.getOperandList().get(1));
    return aggregateCall.toString().equals(expected.call().toString())
        && sourceFilter != null
        && sourceFilter.toString().equals(expected.filter().toString());
  }

  private static boolean hasSourceItems(SqlNodeList nodes) {
    return nodes != null && !nodes.isEmpty();
  }

  private static DirectTableSource directTableSource(SqlNode from, TableScan scan) {
    SqlIdentifier alias = null;
    List<SqlIdentifier> columnAliases = List.of();
    SqlNode tableNode = from;
    if (from instanceof SqlCall call && call.getKind().name().equals("AS")) {
      if (call.getOperandList().size() < 2
          || !(call.getOperandList().get(1) instanceof SqlIdentifier sourceAlias)
          || !sourceAlias.isSimple()) {
        return null;
      }
      tableNode = call.getOperandList().get(0);
      alias = sourceAlias;
      List<SqlIdentifier> parsedColumnAliases = new ArrayList<>();
      for (int i = 2; i < call.getOperandList().size(); i++) {
        if (!(call.getOperandList().get(i) instanceof SqlIdentifier columnAlias)
            || !columnAlias.isSimple()
            || columnAlias.isStar()) {
          return null;
        }
        parsedColumnAliases.add(columnAlias);
      }
      // PostgreSQL permits a partial alias column list: its N entries rename
      // only the first N columns and the remaining columns retain their base
      // names.  A longer list is rejected by PostgreSQL and must not be
      // truncated into apparently valid provenance here.
      if (parsedColumnAliases.size() > scan.getRowType().getFieldCount()) {
        return null;
      }
      columnAliases = List.copyOf(parsedColumnAliases);
    }
    if (!(tableNode instanceof SqlIdentifier tableIdentifier)
        || tableIdentifier.isStar()
        || !identifierMatchesQualifiedName(
            tableIdentifier, scan.getTable().getQualifiedName())) {
      return null;
    }
    return new DirectTableSource(tableIdentifier, alias, columnAliases);
  }

  private static SourceTableBinding sourceTableBinding(
      TableScan scan, SourceContext source) {
    SqlNode candidate = source.node();
    SqlSelect select = topLevelSelect(candidate);
    if (select != null) {
      candidate = select.getFrom();
    }
    List<SqlNode> relations = new ArrayList<>();
    collectDirectBaseRelations(candidate, relations);
    SourceTableBinding matched = null;
    for (SqlNode relation : relations) {
      DirectTableSource direct = directTableSource(relation, scan);
      if (direct == null) {
        continue;
      }
      if (matched != null) {
        return null;
      }
      matched = new SourceTableBinding(relation, direct.table(), direct.alias(), direct);
    }
    return matched;
  }

  /**
   * Emit the complete ordered public namespace of one exact base-relation
   * occurrence.  PostgreSQL relation alias column lists are ordinal: an
   * explicit prefix renames that prefix and all remaining positions inherit
   * their schema names.  Keeping both the explicit alias nodes and the full
   * output lineage prevents a downstream consumer from borrowing a same-text
   * alias from a different occurrence or silently shifting a partial list.
   */
  private static void emitSourceTableColumnLineage(
      Json out,
      TableScan scan,
      DirectTableSource source,
      ExactSourceIdentity relation,
      SourcePositionMap sourcePositions) {
    if (sourcePositions == null
        || source.columnAliases().size() > scan.getRowType().getFieldCount()) {
      throw new UnsupportedOperationException(
          "base relation column aliases lack exact ordered source authority");
    }

    List<ExactSourceIdentity> aliases = new ArrayList<>();
    Set<String> aliasNodeIds = new HashSet<>();
    for (SqlIdentifier alias : source.columnAliases()) {
      ExactSourceIdentity identity = exactSourceIdentity(
          sourcePositions, alias, "base relation column alias");
      if (!aliasNodeIds.add(identity.nodeId())) {
        throw new UnsupportedOperationException(
            "duplicate exact base relation column-alias occurrence");
      }
      aliases.add(identity);
    }

    out.comma();
    out.name("columnAliases");
    out.beginArray();
    for (int i = 0; i < source.columnAliases().size(); i++) {
      if (i > 0) {
        out.comma();
      }
      SqlIdentifier alias = source.columnAliases().get(i);
      ExactSourceIdentity identity = aliases.get(i);
      out.beginObject();
      out.name("outputIndex").value(i);
      out.comma();
      out.name("nodeId").value(identity.nodeId());
      out.comma();
      out.name("text").value(identity.text());
      out.comma();
      out.name("names");
      emitIdentifierNames(out, alias);
      out.comma();
      out.name("quoted");
      emitIdentifierQuoted(out, alias, sourcePositions);
      out.endObject();
    }
    out.endArray();

    out.comma();
    out.name("outputLineage");
    out.beginArray();
    for (int i = 0; i < scan.getRowType().getFieldCount(); i++) {
      if (i > 0) {
        out.comma();
      }
      String baseName = scan.getRowType().getFieldList().get(i).getName();
      SqlIdentifier explicitAlias = i < source.columnAliases().size()
          ? source.columnAliases().get(i)
          : null;
      String visibleName = explicitAlias == null
          ? baseName
          : explicitAlias.names.get(explicitAlias.names.size() - 1);
      out.beginObject();
      out.name("outputIndex").value(i);
      out.comma();
      out.name("kind").value("BASE_COLUMN");
      out.comma();
      out.name("relationOccurrenceId").value(relation.nodeId());
      out.comma();
      out.name("baseColumnIndex").value(i);
      out.comma();
      out.name("baseColumnName").value(baseName);
      out.comma();
      out.name("visibleColumnName").value(visibleName);
      out.comma();
      out.name("generatedFieldName").value(baseName);
      out.comma();
      out.name("explicitColumnAlias").value(explicitAlias != null);
      if (explicitAlias != null) {
        out.comma();
        out.name("columnAliasNodeId").value(aliases.get(i).nodeId());
        out.comma();
        out.name("columnAliasText").value(aliases.get(i).text());
      }
      out.endObject();
    }
    out.endArray();
  }

  private static void collectDirectBaseRelations(
      SqlNode node, List<SqlNode> relations) {
    if (node == null) {
      return;
    }
    SqlNode unaliased = stripAlias(node);
    if (unaliased instanceof SqlJoin join) {
      collectDirectBaseRelations(join.getLeft(), relations);
      collectDirectBaseRelations(join.getRight(), relations);
      return;
    }
    if (unaliased instanceof SqlIdentifier identifier && !identifier.isStar()) {
      relations.add(node);
    }
  }

  private static boolean identifierMatchesQualifiedName(
      SqlIdentifier identifier, List<String> qualifiedName) {
    if (identifier.names.isEmpty() || qualifiedName.isEmpty()
        || identifier.names.size() > qualifiedName.size()) {
      return false;
    }
    int offset = qualifiedName.size() - identifier.names.size();
    for (int i = 0; i < identifier.names.size(); i++) {
      if (!identifier.names.get(i).equals(qualifiedName.get(offset + i))) {
        return false;
      }
    }
    return true;
  }

  private static Integer directTableFieldIndex(
      SqlIdentifier identifier, DirectTableSource sourceTable, TableScan scan) {
    if (identifier.isStar() || identifier.names.isEmpty()) {
      return null;
    }
    int last = identifier.names.size() - 1;
    if (last > 0) {
      SqlIdentifier qualifier = identifier.getComponent(0, last);
      if (sourceTable.alias() != null) {
        if (!samePostgresIdentifier(qualifier, sourceTable.alias())) {
          return null;
        }
      } else {
        SqlIdentifier table = sourceTable.table();
        boolean fullTableName = samePostgresIdentifier(qualifier, table);
        boolean simpleTableName = qualifier.isSimple()
            && qualifier.names.get(0).equals(table.names.get(table.names.size() - 1));
        if (!fullTableName && !simpleTableName) {
          return null;
        }
      }
    }

    String fieldName = identifier.names.get(last);
    Integer matched = null;
    for (int i = 0; i < scan.getRowType().getFieldCount(); i++) {
      boolean visibleNameMatches;
      if (i < sourceTable.columnAliases().size()) {
        SqlIdentifier visibleAlias = sourceTable.columnAliases().get(i);
        SqlIdentifier requested = identifier.getComponent(last, last + 1);
        visibleNameMatches = samePostgresIdentifier(requested, visibleAlias);
      } else {
        visibleNameMatches = scan.getRowType().getFieldList().get(i).getName().equals(fieldName);
      }
      if (visibleNameMatches) {
        if (matched != null) {
          return null;
        }
        matched = i;
      }
    }
    return matched;
  }

  private static CanonicalLiteral canonicalSourceLiteral(SqlLiteral literal) {
    try {
      return switch (literal.getTypeName()) {
        case TINYINT, SMALLINT, INTEGER, BIGINT, DECIMAL ->
            new CanonicalLiteral("NUMERIC", canonicalExactNumber(literal.bigDecimalValue()));
        case CHAR, VARCHAR ->
            new CanonicalLiteral("STRING", literal.getValueAs(String.class));
        case BOOLEAN ->
            new CanonicalLiteral("BOOLEAN", Boolean.toString(literal.booleanValue()));
        default -> null;
      };
    } catch (RuntimeException | AssertionError e) {
      return null;
    }
  }

  private static CanonicalLiteral canonicalRexLiteral(RexLiteral literal) {
    try {
      return switch (literal.getTypeName()) {
        case TINYINT, SMALLINT, INTEGER, BIGINT, DECIMAL ->
            new CanonicalLiteral(
                "NUMERIC", canonicalExactNumber(RexLiteral.bigDecimalValue(literal)));
        case CHAR, VARCHAR ->
            new CanonicalLiteral("STRING", literal.getValueAs(String.class));
        case BOOLEAN ->
            new CanonicalLiteral(
                "BOOLEAN", Boolean.toString(literal.getValueAs(Boolean.class)));
        default -> null;
      };
    } catch (RuntimeException | AssertionError e) {
      return null;
    }
  }

  private static String canonicalExactNumber(BigDecimal value) {
    if (value == null || value.signum() == 0) {
      return "0";
    }
    return value.stripTrailingZeros().toPlainString();
  }

  /**
   * Compare identifier values after the parser has applied PostgreSQL's
   * lower-case folding to every unquoted component. Quotedness remains
   * observable through the resulting spelling: {@code "D2"} does not match
   * bare {@code d2}, while {@code "d2"} denotes the same identifier value.
   * Calcite drops the quote flag from some validated AS aliases, so requiring
   * identical quote flags here would reject a semantically exact binding.
   */
  private static boolean samePostgresIdentifier(SqlIdentifier left, SqlIdentifier right) {
    return left.names.equals(right.names);
  }

  /**
   * Parser positions identify lexical query blocks in the independently
   * parsed source AST.  Avoid inventing an identifier for generated/unknown
   * positions: missing provenance must remain conservative downstream.
   */
  private static String sourceQueryBlockId(
      SqlSelect select, SourcePositionMap sourcePositions) {
    if (sourcePositions == null) {
      return null;
    }
    ExactSourceIdentity identity = sourcePositions.queryBlockIdentity(select);
    return identity == null ? null : identity.nodeId();
  }

  private static String sourceRelQueryBlockId(
      SqlNode query, SourcePositionMap sourcePositions) {
    SqlSelect select = topLevelSelect(query);
    if (select != null) {
      return sourceQueryBlockId(select, sourcePositions);
    }
    SqlNode body = sourceQueryBody(query);
    if (sourcePositions == null
        || !(body instanceof SqlCall call)
        || !isSetQueryCall(call)) {
      return null;
    }
    ExactSourceIdentity identity = sourcePositions.declarativeQueryIdentity(query);
    return identity == null ? null : identity.nodeId();
  }

  private static SqlNode sourceFilterCondition(
      Filter filter, SourceContext source, int fuel) {
    SqlSelect select = topLevelSelect(source.node());
    if (select == null) {
      return null;
    }
    if (source.clausePhase() == SourceClausePhase.POST_AGGREGATE
        && select.getHaving() != null && filter.getInput() instanceof Aggregate) {
      return select.getHaving();
    }
    if (select.getWhere() != null) {
      return select.getWhere();
    }
    if (fuel == 0) {
      return null;
    }
    SqlNode input = referencedInputQuery(select, source.ctes());
    return input == null
        ? null
        : sourceFilterCondition(filter, source.withNode(input), fuel - 1);
  }

  private static SqlNode topLevelJoinCondition(SqlNode sourceSql) {
    SqlSelect select = topLevelSelect(sourceSql);
    SqlNode from = select == null ? sourceSql : stripAlias(select.getFrom());
    return from instanceof SqlJoin join ? join.getCondition() : null;
  }

  private static String sourceNodeId(
      SourcePositionMap sourcePositions, SqlNode node) {
    return sourcePositions == null ? null : sourcePositions.sourceNodeId(node);
  }

  private static String sourceTextAtNode(
      SourcePositionMap sourcePositions, SqlNode node) {
    return sourcePositions == null ? null : sourcePositions.sourceText(node);
  }

  /**
   * Attach an exact original-statement identity to one independently parsed
   * source AST node.  Rendered {@code sourceSql} remains useful structural
   * metadata, but only this pair lets the importer prove that the node came
   * from the submitted statement. Generated/unknown parser positions emit
   * neither field and therefore remain explicitly unbound.
   */
  private static void emitExactSourceBinding(
      Json out, SourcePositionMap sourcePositions, SqlNode node) {
    ExactSourceIdentity identity = sourcePositions == null
        ? null
        : sourcePositions.expressionIdentity(node);
    if (identity == null) {
      return;
    }
    out.comma();
    out.name("sourceNodeId").value(identity.nodeId());
    out.comma();
    out.name("sourceText").value(identity.text());
  }

  private static void emitExactRelSourceBinding(
      Json out, SourcePositionMap sourcePositions, SqlNode node) {
    ExactSourceIdentity identity = sourcePositions == null
        ? null
        : sourcePositions.relationalSourceIdentity(node);
    if (identity == null) {
      return;
    }
    out.comma();
    out.name("sourceNodeId").value(identity.nodeId());
    out.comma();
    out.name("sourceText").value(identity.text());
  }

  private static SqlSelect topLevelSelect(SqlNode sourceSql) {
    SqlNode query = sourceQueryBody(sourceSql);
    if (query instanceof SqlSelect select) {
      return select;
    }
    return null;
  }

  private static SourceContext sourceForRelInput(
      RelNode rel, SourceContext source, int index) {
    SqlNode sourceSql = source.node();
    if (sourceSql == null) {
      return source.withNode(null);
    }
    if (rel instanceof Join) {
      // `Planner.rel(validated)` is serialized directly above: no RelOpt
      // optimization/reordering phase runs between SqlToRel conversion and
      // this walk. SqlToRel preserves the binary SqlJoin's left/right input
      // order (possibly adding unary operators within either side). The raw
      // IR records each selected operand's parser span and SQL, and Rust
      // conversion rejects a CROSS attestation unless those identities match
      // the corresponding generated child exactly.
      SqlSelect select = topLevelSelect(sourceSql);
      SqlNode from = select == null ? sourceSql : stripAlias(select.getFrom());
      if (from instanceof SqlJoin join) {
        SqlNode relation = index == 0 ? join.getLeft() : join.getRight();
        SqlNode input = stripAlias(relation);
        SqlNode resolved = resolveCteReference(input, source.ctes());
        // Descend into a derived query/CTE body, but retain a direct base
        // relation's complete AS/implicit-alias node so its TableScan can
        // authenticate the exact visible relation and alias rather than only
        // the table-name token.
        return source.withNode(
            resolved != input || isQuerySourceNode(input) ? resolved : relation);
      }
      return source.withNode(null);
    }
    SqlNode setSource = resolveCteReference(sourceSetExpression(sourceSql), source.ctes());
    // With simplifyValues=false Calcite represents a multi-row source VALUES
    // as one UNION ALL input per source ROW. Preserve the ordered row-to-input
    // association only for that exact arity-preserving shape; each child
    // Project can then attach casts and literals to its own source row instead
    // of borrowing a same-valued expression elsewhere in the statement.
    if (rel instanceof SetOp setOp
        && setOp.kind.name().equals("UNION")
        && setOp.all
        && setSource instanceof SqlCall values
        && values.getKind().name().equals("VALUES")) {
      List<List<SqlNode>> rows = sourceValueRows(values);
      List<SqlNode> rowNodes = values.getOperandList();
      boolean exactRows = rows.size() == rel.getInputs().size()
          && rowNodes.size() == rows.size();
      for (int row = 0; exactRows && row < rows.size(); row++) {
        exactRows = rows.get(row).size()
            == rel.getInputs().get(row).getRowType().getFieldCount();
      }
      if (exactRows) {
        return source.withNode(
            index < rowNodes.size() ? stripAlias(rowNodes.get(index)) : null);
      }
    }
    if (rel instanceof SetOp setOp && setSource instanceof SqlCall call
        && sourceSetOperationMatches(setOp, call)) {
      List<SqlNode> operands = call.getOperandList();
      String kind = setOp.kind.name();
      if (operands.size() != rel.getInputs().size()
          && (kind.equals("UNION") || kind.equals("INTERSECT"))) {
        operands = new ArrayList<>();
        flattenAssociativeSourceOperands(call, kind, operands);
      }
      return source.withNode(
          index < operands.size() ? stripAlias(operands.get(index)) : null);
    }
    if (rel.getInputs().size() == 1
        && (rel instanceof Project || rel instanceof Filter || rel instanceof Aggregate
            || rel instanceof Sort)) {
      SqlSelect select = topLevelSelect(sourceSql);
      if (select == null) {
        return source;
      }
      if (select.getFrom() == null && rel.getInput(0) instanceof Values) {
        // Calcite implements a no-FROM SELECT as a relational operator over a
        // synthetic one-row Values input.  SELECT expressions and predicates
        // belong to that parent operator, not to the dummy integer tuple.
        return source.withNode(null).withoutLiteralRecovery();
      }
      if (rel instanceof Sort) {
        return source;
      }

      // Relational clauses are consumed outside-in. A HAVING filter and its
      // Aggregate still belong to this SELECT; a WHERE filter is the boundary
      // after which provenance descends into FROM. This prevents expressions
      // from an inner query level being attached to validator-generated Rex
      // nodes at an outer level.
      if (rel instanceof Filter filter) {
        String sourceClause = sourceFilterClause(filter, source);
        if ("HAVING".equals(sourceClause)) {
          return source;
        }
        SqlNode input = referencedInputQuery(select, source.ctes());
        return input == null ? source : source.withNode(input);
      }
      if (rel instanceof Aggregate aggregate) {
        if (sourceDistinctDedupPrecedesOwnedAggregate(select, aggregate)) {
          // SELECT DISTINCT over grouped/aggregate results has two logical
          // Aggregates. The outer, call-free all-output Aggregate owns only
          // duplicate elimination; retain the same source block through its
          // Project input so the inner Aggregate can consume the exact GROUP
          // BY and aggregate-call roles.
          return source;
        }
        if (aggregate.getInput() instanceof SetOp) {
          // A global aggregate such as COUNT(*) can consume a derived set
          // query without an intervening generated Project. Its Aggregate
          // call still belongs to this SELECT, but the relational input is
          // rooted at the exact FROM subquery rather than at the outer block.
          SqlNode input = referencedInputQuery(select, source.ctes());
          if (input != null) {
            return source.withNode(input);
          }
        }
        if (aggregate.getInput() instanceof Aggregate childAggregate) {
          // Calcite can elide an identity Project between an outer aggregate
          // query and the aggregate owned by its sole direct derived query or
          // CTE input. Descend only when that exact inner SELECT independently
          // owns the generated child Aggregate; arbitrary nested aggregates,
          // joins, and name/arity guesses remain outside this boundary.
          SqlNode input = referencedInputQuery(select, source.ctes());
          SqlSelect innerSelect = topLevelSelect(input);
          if (input != null
              && innerSelect != null
              && sourceOwnsAggregate(innerSelect, childAggregate)) {
            return source.withNode(input);
          }
        }
        return source.beforeAggregate();
      }
      if (rel instanceof Project project) {
        if (source.clausePhase() == SourceClausePhase.POST_AGGREGATE
                && project.getInput() instanceof Aggregate aggregate
                && (sourceOwnsAggregate(select, aggregate)
                    || sourceDistinctProjectFeedsAggregate(select, aggregate))
            || project.getInput() instanceof Filter
                && (select.getWhere() != null
                    || source.clausePhase() == SourceClausePhase.POST_AGGREGATE
                        && select.getHaving() != null)) {
          return source;
        }
        SqlNode input = referencedInputQuery(select, source.ctes());
        if (input != null) {
          return source.withNode(input);
        }
      }
      return source;
    }
    return source.withNode(null);
  }

  /**
   * Distinguish a SELECT's own Aggregate from an Aggregate introduced by
   * inlining a referenced CTE.  Relational traversal must stay in the current
   * query block only when the independently parsed source block itself owns
   * the aggregate calls, grouping clause, or DISTINCT operation.  Otherwise
   * it descends through FROM and resolves the CTE before attaching aggregate
   * or HAVING provenance.
   */
  private static boolean sourceOwnsAggregate(SqlSelect select, Aggregate aggregate) {
    List<SqlCall> sourceCalls = sourceAggregateCalls(select);
    boolean sourceHasAggregateShape = !sourceCalls.isEmpty()
        || select.getGroup() != null && !select.getGroup().isEmpty()
        || select.isDistinct();
    Integer sourceGroupKeyCount = ordinarySourceGroupKeyCount(select);
    return sourceHasAggregateShape
        && alignedSourceAggregateCalls(aggregate, select) != null
        && (sourceGroupKeyCount == null
            || aggregate.getGroupSet().cardinality() == sourceGroupKeyCount);
  }

  private static boolean sourceDistinctDedupPrecedesOwnedAggregate(
      SqlSelect select, Aggregate aggregate) {
    if (!select.isDistinct()
        || !aggregate.getAggCallList().isEmpty()
        || aggregate.getGroupSet().cardinality() != aggregate.getRowType().getFieldCount()
        || !(aggregate.getInput() instanceof Project project)
        || !(project.getInput() instanceof Aggregate)) {
      return false;
    }
    return !sourceAggregateCalls(select).isEmpty()
        || select.getGroup() != null && !select.getGroup().isEmpty()
        || select.getHaving() != null;
  }

  private static boolean sourceDistinctProjectFeedsAggregate(
      SqlSelect select, Aggregate aggregate) {
    if (!select.isDistinct()) {
      return false;
    }
    boolean sourceHasAggregateShape = !sourceAggregateCalls(select).isEmpty()
        || select.getGroup() != null && !select.getGroup().isEmpty()
        || select.getHaving() != null;
    Integer sourceGroupKeyCount = ordinarySourceGroupKeyCount(select);
    return sourceHasAggregateShape
        && (sourceGroupKeyCount == null
            || aggregate.getGroupSet().cardinality() == sourceGroupKeyCount);
  }

  /**
   * Bind one call-free all-output Aggregate to an exact source SELECT
   * DISTINCT.  Calcite uses the same Aggregate shape for a genuine GROUP BY,
   * so downstream code may treat it as duplicate elimination only when the
   * independently parsed source block owns DISTINCT and the complete
   * generated key/type shape agrees.
   */
  private static SourceDistinctAttestation sourceDistinctAttestation(
      Aggregate aggregate, SourceContext source) {
    SqlSelect select = topLevelSelect(source.node());
    if (select == null
        || !select.isDistinct()
        || source.queryBlockId() == null
        || source.sourcePositions() == null
        || !aggregate.getAggCallList().isEmpty()
        || aggregate.getInputs().size() != 1
        || aggregate.getGroupSets().size() != 1
        || aggregate.getGroupSet().cardinality()
            != aggregate.getRowType().getFieldCount()
        || !aggregate.getGroupSets().get(0).equals(aggregate.getGroupSet())
        || aggregate.getInput().getRowType().getFieldCount()
            != aggregate.getRowType().getFieldCount()) {
      return null;
    }
    boolean sourceHasAggregateShape = !sourceAggregateCalls(select).isEmpty()
        || select.getGroup() != null && !select.getGroup().isEmpty()
        || select.getHaving() != null;
    if (sourceHasAggregateShape
        && !sourceDistinctDedupPrecedesOwnedAggregate(select, aggregate)) {
      return null;
    }
    for (int index = 0; index < aggregate.getRowType().getFieldCount(); index++) {
      if (!aggregate.getGroupSet().get(index)
          || !aggregate.getInput().getRowType().getFieldList().get(index).getType()
              .equals(aggregate.getRowType().getFieldList().get(index).getType())) {
        return null;
      }
    }
    ExactSourceIdentity selectIdentity =
        source.sourcePositions().queryBlockIdentity(select);
    if (selectIdentity == null
        || !selectIdentity.nodeId().equals(source.queryBlockId())
        || selectIdentity.text().isEmpty()) {
      return null;
    }
    List<Integer> groupIndexes = aggregate.getGroupSet().asList();
    List<List<Integer>> groupingSets = List.of(
        List.copyOf(aggregate.getGroupSets().get(0).asList()));
    return new SourceDistinctAttestation(
        "SELECT_DISTINCT",
        source.queryBlockId(),
        selectIdentity.nodeId(),
        selectIdentity.text(),
        List.copyOf(groupIndexes),
        groupingSets,
        aggregate.getInput().getRowType().getFieldCount(),
        aggregate.getRowType().getFieldCount());
  }

  /** Return an exact direct GROUP BY arity, or null for grouping-set/DISTINCT
   * shapes whose expanded Aggregate key set is not represented positionally
   * by the top-level source list. */
  private static Integer ordinarySourceGroupKeyCount(SqlSelect select) {
    if (select.isDistinct()) {
      return null;
    }
    SqlNodeList group = select.getGroup();
    if (group == null || group.isEmpty()) {
      return 0;
    }
    for (SqlNode item : group) {
      String kind = item.getKind().name();
      if (kind.equals("GROUPING_SETS") || kind.equals("ROLLUP") || kind.equals("CUBE")) {
        return null;
      }
    }
    return group.size();
  }

  /**
   * Bind every source GROUP BY occurrence to its generated Aggregate-input
   * position.  Keeping the syntactic set nesting (rather than only Calcite's
   * expanded bitsets) closes ordinary GROUP BY, ROLLUP, and GROUPING SETS
   * against coherent metadata mutations and repeated expressions.
   */
  private static SourceGroupingAttestation sourceGroupingAttestation(
      Aggregate aggregate, SourceContext source) {
    SqlSelect select = topLevelSelect(source.node());
    if (select == null
        || source.queryBlockId() == null
        || select.getGroup() == null
        || select.getGroup().isEmpty()
        || select.isDistinct()
            && sourceDistinctDedupPrecedesOwnedAggregate(select, aggregate)) {
      return null;
    }
    ExactSourceIdentity selectIdentity = source.sourcePositions() == null
        ? null
        : source.sourcePositions().queryBlockIdentity(select);
    String sourceSelectNodeId = selectIdentity == null ? null : selectIdentity.nodeId();
    String sourceSelectText = selectIdentity == null ? null : selectIdentity.text();
    String sourceGroupNodeId = sourceNodeId(source.sourcePositions(), select.getGroup());
    String sourceGroupText = sourceTextAtNode(source.sourcePositions(), select.getGroup());
    if (sourceSelectNodeId == null
        || sourceSelectText == null
        || sourceGroupNodeId == null
        || sourceGroupText == null) {
      return null;
    }
    String kind = "GROUP_BY";
    List<List<SqlNode>> sourceOperandSets = new ArrayList<>();
    SqlNode soleGroup = select.getGroup().size() == 1 ? select.getGroup().get(0) : null;
    if (soleGroup instanceof SqlCall groupingCall
        && groupingCall.getKind().name().equals("ROLLUP")) {
      kind = "ROLLUP";
      List<SqlNode> operands = new ArrayList<>();
      for (SqlNode operand : groupingCall.getOperandList()) {
        List<SqlIdentifier> members = groupingSetIdentifiers(operand);
        if (members == null) {
          return null;
        }
        operands.addAll(members);
      }
      if (operands.isEmpty()) {
        return null;
      }
      sourceOperandSets.add(List.copyOf(operands));
    } else if (soleGroup instanceof SqlCall groupingCall
        && groupingCall.getKind().name().equals("GROUPING_SETS")) {
      kind = "GROUPING_SETS";
      if (groupingCall.getOperandList().isEmpty()) {
        return null;
      }
      for (SqlNode operand : groupingCall.getOperandList()) {
        List<SqlIdentifier> members = groupingSetIdentifiers(operand);
        if (members == null) {
          return null;
        }
        sourceOperandSets.add(new ArrayList<>(members));
      }
    } else {
      List<SqlNode> operands = new ArrayList<>();
      for (SqlNode item : select.getGroup()) {
        String itemKind = item.getKind().name();
        if (itemKind.equals("ROLLUP")
            || itemKind.equals("GROUPING_SETS")
            || itemKind.equals("CUBE")) {
          return null;
        }
        operands.add(stripAlias(item));
      }
      sourceOperandSets.add(List.copyOf(operands));
    }

    List<SqlNode> inputExpressions = aggregateInputExpressions(select);
    List<List<Integer>> sourceOperandIndexes = new ArrayList<>();
    List<Integer> groupIndexes = new ArrayList<>();
    for (List<SqlNode> sourceSet : sourceOperandSets) {
      List<Integer> set = new ArrayList<>();
      for (SqlNode operand : sourceSet) {
        int index = resolvedSourceExpressionIndex(select, inputExpressions, operand);
        if (index < 0 || set.contains(index)) {
          return null;
        }
        set.add(index);
        if (!groupIndexes.contains(index)) {
          groupIndexes.add(index);
        }
      }
      sourceOperandIndexes.add(List.copyOf(set));
    }
    List<Integer> generatedGroupIndexes = aggregate.getGroupSet().asList();
    List<List<Integer>> generatedGroupingSets = new ArrayList<>();
    for (var generatedSet : aggregate.getGroupSets()) {
      generatedGroupingSets.add(List.copyOf(generatedSet.asList()));
    }
    List<List<Integer>> expectedGroupingSets = new ArrayList<>();
    if (kind.equals("ROLLUP")) {
      for (int length = groupIndexes.size(); length >= 0; length--) {
        expectedGroupingSets.add(List.copyOf(groupIndexes.subList(0, length)));
      }
    } else if (kind.equals("GROUPING_SETS")) {
      expectedGroupingSets.addAll(sourceOperandIndexes);
    } else {
      expectedGroupingSets.add(List.copyOf(groupIndexes));
    }
    if (!groupIndexes.equals(generatedGroupIndexes)
        || !expectedGroupingSets.equals(generatedGroupingSets)) {
      return null;
    }
    return new SourceGroupingAttestation(
        kind,
        source.queryBlockId(),
        sourceSelectNodeId,
        sourceSelectText,
        select.toString(),
        sourceGroupNodeId,
        sourceGroupText,
        select.getGroup().toString(),
        List.copyOf(groupIndexes),
        List.copyOf(generatedGroupingSets),
        List.copyOf(sourceOperandIndexes),
        List.copyOf(sourceOperandSets),
        select.getWhere() != null,
        select.getHaving() != null);
  }

  /** A SELECT is also a SqlCall; never interpret its positional operands as
   * set-operation branches merely because an inlined RelNode is a SetOp. */
  private static boolean sourceSetOperationMatches(SetOp setOp, SqlCall call) {
    return call.getOperator() instanceof SqlSetOperator sourceSetOperator
        && call.getKind().name().equals(setOp.kind.name())
        && sourceSetOperator.isAll() == setOp.all;
  }

  private static SqlNode sourceQueryBody(SqlNode sourceSql) {
    SqlNode query = sourceSql;
    if (query instanceof SqlOrderBy orderBy) {
      query = orderBy.query;
    }
    if (query instanceof SqlCall call && call.getKind().name().equals("WITH")
        && call.getOperandList().size() >= 2) {
      query = call.getOperandList().get(1);
    }
    return query;
  }

  private static SqlOrderBy sourceTopLevelOrderBy(SqlNode sourceSql) {
    SqlNode query = sourceSql;
    for (int fuel = 0; fuel < 8; fuel++) {
      if (query instanceof SqlOrderBy orderBy) {
        return orderBy;
      }
      if (query instanceof SqlWith with) {
        query = with.body;
        continue;
      }
      if (query instanceof SqlCall call && call.getKind().name().equals("WITH")
          && call.getOperandList().size() >= 2) {
        query = call.getOperandList().get(1);
        continue;
      }
      return null;
    }
    return null;
  }

  /**
   * Bind every generated Sort key to one exact, ordered source ORDER BY item.
   * Direction, NULL placement, and field positions remain independently
   * validated by the Rust importer; the wrapper contributes only exact source
   * identities recovered while it still owns the PostgreSQL parser tree.
   */
  private static SourceOrderAttestation sourceOrderAttestation(
      Sort sort, SourceContext source) {
    boolean hasGeneratedKeys = !sort.getCollation().getFieldCollations().isEmpty();
    SqlOrderBy orderBy = sourceTopLevelOrderBy(source.node());
    boolean hasSourceItems = orderBy != null
        && orderBy.orderList != null
        && !orderBy.orderList.isEmpty();
    if (!hasGeneratedKeys && !hasSourceItems) {
      return null;
    }
    if (!hasGeneratedKeys || !hasSourceItems) {
      throw new UnsupportedOperationException(
          "generated Sort keys and exact source ORDER BY items disagree");
    }
    if (sort.getCollation().getFieldCollations().size() != orderBy.orderList.size()) {
      throw new UnsupportedOperationException(
          "Calcite changed the number of exact source ORDER BY items");
    }
    SourcePositionMap positions = source.sourcePositions();
    ExactSourceIdentity query = positions == null
        ? null
        : positions.orderedQueryIdentity(orderBy.query);
    ExactSourceIdentity orderList = positions == null
        ? null
        : positions.orderListIdentity(orderBy.orderList);
    if (query == null || orderList == null) {
      throw new UnsupportedOperationException(
          "missing exact query or ORDER BY-list source identity");
    }
    if (!positions.hasDirectOrderByBoundary(orderBy.query, orderBy.orderList)) {
      throw new UnsupportedOperationException(
          "missing direct exact ORDER BY clause boundary between "
              + query.nodeId() + " and " + orderList.nodeId());
    }
    List<SourceOrderItemAttestation> items = new ArrayList<>();
    for (SqlNode rawItem : orderBy.orderList) {
      SqlNode expressionNode = stripOrderByDecoration(rawItem);
      ExactSourceIdentity item = positions.orderItemIdentity(rawItem);
      ExactSourceIdentity expression = positions.exactIdentity(expressionNode);
      if (item == null || expression == null) {
        throw new UnsupportedOperationException(
            "missing exact ORDER BY item or expression source identity");
      }
      items.add(new SourceOrderItemAttestation(item, expression));
    }
    return new SourceOrderAttestation(query, orderList, List.copyOf(items));
  }

  private static SqlNode sourceSetExpression(SqlNode sourceSql) {
    SqlNode query = sourceQueryBody(sourceSql);
    if (query instanceof SqlSelect select) {
      SqlNode from = stripAlias(select.getFrom());
      if (from != null) {
        query = from;
      }
    }
    return stripAlias(query);
  }

  private static SqlNode referencedInputQuery(
      SqlSelect select, Map<String, SqlNode> ctes) {
    SqlNode from = stripAlias(select.getFrom());
    SqlNode resolved = resolveCteReference(from, ctes);
    if (resolved != from) {
      return resolved;
    }
    return isQuerySourceNode(from) ? from : null;
  }

  private static SqlNode resolveCteReference(
      SqlNode sourceSql, Map<String, SqlNode> ctes) {
    if (!(sourceSql instanceof SqlIdentifier identifier) || identifier.names.size() != 1) {
      return sourceSql;
    }
    // CTE references are unqualified.  SqlParser has already applied the
    // PostgreSQL identifier rules configured above: bare names are lower-case
    // and quoted names preserve their exact case.  Keep that canonical name
    // rather than folding again and collapsing x with "X".
    String name = identifier.names.get(0);
    return ctes.getOrDefault(name, sourceSql);
  }

  private static boolean isSetQueryCall(SqlCall call) {
    // SqlKind.MINUS is shared by EXCEPT-style set difference and scalar
    // subtraction.  The operator class distinguishes the former; VALUES is a
    // query source but uses its own non-SqlSetOperator implementation.
    return call.getOperator() instanceof SqlSetOperator
        || call.getKind().name().equals("VALUES");
  }

  private static List<List<SqlNode>> sourceValueRows(SqlNode sourceSql) {
    if (sourceSql instanceof SqlOrderBy orderBy) {
      return sourceValueRows(orderBy.query);
    }
    if (sourceSql instanceof SqlSelect select && select.getFrom() == null
        && select.getSelectList() != null) {
      List<SqlNode> row = new ArrayList<>();
      for (SqlNode item : select.getSelectList()) {
        row.add(stripAlias(item));
      }
      return List.of(row);
    }
    if (!(stripAlias(sourceSql) instanceof SqlCall call)) {
      return List.of();
    }
    if (call.getKind().name().equals("UNION")) {
      List<List<SqlNode>> rows = new ArrayList<>();
      for (SqlNode input : call.getOperandList()) {
        rows.addAll(sourceValueRows(input));
      }
      return rows;
    }
    if (call.getKind().name().equals("ROW")) {
      return List.of(call.getOperandList());
    }
    if (!call.getKind().name().equals("VALUES")) {
      return List.of();
    }
    List<List<SqlNode>> rows = new ArrayList<>();
    for (SqlNode row : call.getOperandList()) {
      if (stripAlias(row) instanceof SqlCall rowCall
          && rowCall.getKind().name().equals("ROW")) {
        rows.add(rowCall.getOperandList());
      } else {
        rows.add(List.of(stripAlias(row)));
      }
    }
    return rows;
  }

  private static SqlNode subquerySource(SqlNode sourceSql) {
    if (isQuerySourceNode(sourceSql)) {
      return sourceSql;
    }
    if (sourceSql instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        SqlNode candidate = stripAlias(operand);
        if (isQuerySourceNode(candidate)) {
          return candidate;
        }
      }
    }
    return null;
  }

  private static boolean isQuerySourceNode(SqlNode node) {
    if (node instanceof SqlSelect || node instanceof SqlOrderBy) {
      return true;
    }
    return node instanceof SqlCall call
        && (isSetQueryCall(call)
            || call.getKind().name().equals("WITH"));
  }

  private static List<SqlNode> sourceOperands(
      RexCall rex, SqlNode sourceSql, SourcePositionMap sourcePositions) {
    if (rex.getKind().name().equals("CASE")) {
      SqlCase sourceCase = directSourceCase(rex, sourceSql, sourcePositions);
      if (sourceCase != null) {
        List<SqlNode> operands = sourceCaseOperands(sourceCase);
        if (operands.size() == rex.getOperands().size()) {
          return operands;
        }
      }
    }
    if (sourceSql instanceof SqlCall sourceCall
        && rex.getKind().name().equals("CAST")
        && sourceCall.getKind().name().equals("CAST")
        && rex.getOperands().size() == 1
        && !sourceCastTargetMatchesRex(sourceCall, rex, sourcePositions)) {
      // Calcite can wrap a user CAST in a second validator-generated CAST.
      // Keep the complete source CAST attached to the child until the Rex
      // node whose target typmod actually matches the source is reached.
      return List.of(sourceSql);
    }
    if (sourceSql instanceof SqlCall sourceCall
        && rex.getKind().name().equals("CAST")
        && sourceCall.getKind().name().equals("CAST")
        && rex.getOperands().size() == 1
        && sourceCastTargetMatchesRex(sourceCall, rex, sourcePositions)) {
      // Once the exact source target agrees with this generated CAST, its one
      // Rex operand denotes the source CAST operand rather than the datatype
      // node that occupies the second SqlCall position.
      return List.of(sourceCall.getOperandList().get(0));
    }
    if (sourceSql != null && rex.getKind().name().equals("CAST")
        && rex.getOperands().size() == 1
        && (!(sourceSql instanceof SqlCall sourceCall)
            || !sourceCall.getKind().name().equals("CAST"))) {
      // A validator-generated CAST has no source CAST node. Its single Rex
      // operand still denotes the same source expression, so retain that
      // provenance while the Rust importer discards the implicit coercion.
      return List.of(sourceSql);
    }
    SqlIdentifier idempotentIsNullOperand =
        directIdempotentIsNullConjunctIdentifier(rex, sourceSql);
    if (idempotentIsNullOperand != null) {
      // Calcite applies boolean idempotence to `x IS NULL AND x IS NULL` and
      // emits one IS NULL call. Retain the complete exact AND at that call,
      // but bind its generated InputRef to the direct identifier inside one
      // of the two independently parsed, identical conjuncts. Rust then
      // proves the complete duplicate-conjunct shape before admitting the
      // declarative rewrite.
      return List.of(idempotentIsNullOperand);
    }
    if (sourceSql != null && rex.getOperands().size() == 1
        && (rex.getKind().name().equals("IS_TRUE")
            || rex.getKind().name().equals("IS_FALSE")
            || rex.getKind().name().equals("IS_NOT_TRUE")
            || rex.getKind().name().equals("IS_NOT_FALSE")
            || rex.getKind().name().equals("IS_NULL")
            || rex.getKind().name().equals("IS_NOT_NULL"))
        && (!(sourceSql instanceof SqlCall sourceCall)
            || !sourceCall.getKind().name().equals(rex.getKind().name()))) {
      // Aggregate FILTER and other boolean contexts can add an IS TRUE/FALSE
      // Rex wrapper around the source predicate. The child still denotes the
      // complete source predicate, not its first SQL operand.
      return List.of(sourceSql);
    }
    if (!(sourceSql instanceof SqlCall call)) {
      return List.of();
    }
    String rexKind = rex.getKind().name();
    if (rex instanceof RexSubQuery subQuery
        && rexKind.equals("IN")
        && call.getKind().name().equals("IN")) {
      // A RexSubQuery IN stores only the ordered left-hand scalar values in
      // Rex operands; its query is represented separately by subqueryRel.
      // Calcite's source SqlCall instead stores [left, query]. Flatten an
      // exact source ROW left side positionally, but never lend the SELECT AST
      // to a scalar operand merely because both lists happen to have arity 2.
      if (call.getOperandList().size() != 2
          || rex.getOperands().size() != subQuery.rel.getRowType().getFieldCount()
          || !isQuerySourceNode(stripAlias(call.getOperandList().get(1)))) {
        return List.of();
      }
      SqlNode sourceLeft = stripAlias(call.getOperandList().get(0));
      if (sourceLeft instanceof SqlCall row
          && row.getKind().name().equals("ROW")) {
        return row.getOperandList().size() == rex.getOperands().size()
            ? row.getOperandList()
            : List.of();
      }
      return rex.getOperands().size() == 1 ? List.of(sourceLeft) : List.of();
    }
    if (call.getKind().name().equals("OVER")
        && !call.getOperandList().isEmpty()
        && call.getOperandList().get(0) instanceof SqlCall sourceFunction
        && rex.getOperator().getName().equalsIgnoreCase(sourceFunction.getOperator().getName())
        && rex.getOperands().size() == sourceFunction.getOperandList().size()) {
      // A RexOver's generated operands are the window function arguments,
      // not the Sql OVER call's `[function, window]` operands. Preserve the
      // exact argument edge so a positional input cannot borrow the complete
      // MAX/SUM call as opaque non-identifier provenance.
      return sourceFunction.getOperandList();
    }
    if (rexKind.equals("AND")
        && directAsymmetricBetween(call)
        && exactExpandedBetween(rex)) {
      // Calcite expands one direct PostgreSQL BETWEEN into a pair of
      // comparisons. Both comparisons denote the complete source call; the
      // branches below then select value/lower and value/upper respectively.
      // Returning the raw three source operands here would shift the lower
      // bound onto the <= node and leave both bounds unprovenanced.
      return List.of(sourceSql, sourceSql);
    }
    if (rexKind.equals("OR")
        && call.getKind().name().equals("IS_NOT_DISTINCT_FROM")
        && exactExpandedIsNotDistinctFrom(rex)) {
      // Calcite expands `a IS NOT DISTINCT FROM b` into
      // `(a IS NULL AND b IS NULL) OR IS TRUE(a = b)`.  Both generated
      // branches denote the complete source comparison; their descendants
      // are then mapped positionally to the exact two source operands.
      return List.of(sourceSql, sourceSql);
    }
    if (rexKind.equals("NOT") && rex.getOperands().size() == 1
        && !call.getKind().name().equals("NOT")
        && call.getOperator().getName().toUpperCase(Locale.ROOT).startsWith("NOT ")) {
      // SQL NOT LIKE/IN/BETWEEN are represented by Calcite as an outer Rex
      // NOT around the positive operator. The positive Rex child still maps
      // to the complete source call, not to its first SQL operand.
      if (call.getKind().name().equals("NOT_IN")) {
        SqlCall positive = positiveInForExactExpandedNotIn(rex, call);
        if (positive == null) {
          positive = positiveInForExactNotInSubquery(rex, call);
        }
        return positive == null ? List.of() : List.of(positive);
      }
      return List.of(sourceSql);
    }
    if ((rexKind.equals("AND") || rexKind.equals("OR"))
        && call.getKind().name().equals(rexKind)) {
      List<SqlNode> operands = new ArrayList<>();
      flattenAssociativeSourceOperands(call, rexKind, operands);
      if (rexKind.equals("AND")) {
        List<SqlNode> expanded = new ArrayList<>();
        for (SqlNode operand : operands) {
          expanded.add(operand);
          if (operand instanceof SqlCall sourceCall
              && sourceCall.getKind().name().equals("BETWEEN")) {
            expanded.add(operand);
          }
        }
        if (expanded.size() == rex.getOperands().size()) {
          return expanded;
        }
      } else {
        List<SqlNode> expanded = alignFlattenedOrOperands(rex.getOperands(), operands);
        if (expanded.size() == rex.getOperands().size()) {
          return expanded;
        }
      }
      return operands;
    }
    if (rexKind.equals("OR") && call.getKind().name().equals("IN")
        && call.getOperandList().size() >= 2
        && call.getOperandList().get(1) instanceof SqlNodeList values) {
      List<SqlNode> matched = sourceInComparisons(rex.getOperands(), call, values);
      if (matched.size() == rex.getOperands().size()) {
        return matched;
      }
      if (values.size() == rex.getOperands().size()) {
        List<SqlNode> comparisons = new ArrayList<>();
        SqlNode value = call.getOperandList().get(0);
        for (SqlNode candidate : values) {
          comparisons.add(
              SqlStdOperatorTable.EQUALS.createCall(SqlParserPos.ZERO, value, candidate));
        }
        return comparisons;
      }
    }
    if (rexKind.equals("EQUALS") && call.getKind().name().equals("IN")
        && rex.getOperands().size() == 2 && call.getOperandList().size() >= 2
        && call.getOperandList().get(1) instanceof SqlNodeList values) {
      List<SqlNode> matched = sourceInComparisons(List.of(rex), call, values);
      if (matched.size() == 1) {
        return matched.get(0) instanceof SqlCall comparison
            ? comparison.getOperandList()
            : List.of();
      }
      if (!values.isEmpty() && allSourceNodesEquivalent(values)) {
        // Calcite deduplicates IN ('x', 'x') to one equality. Map that
        // equality to the unique source value rather than the SqlNodeList.
        return List.of(call.getOperandList().get(0), values.get(0));
      }
    }
    if (directAsymmetricBetween(call)) {
      if (rexKind.equals("GREATER_THAN_OR_EQUAL")) {
        return List.of(call.getOperandList().get(0), call.getOperandList().get(1));
      }
      if (rexKind.equals("LESS_THAN_OR_EQUAL")) {
        return List.of(call.getOperandList().get(0), call.getOperandList().get(2));
      }
    }
    if (rexKind.equals("CASE") && call.getOperator().getName().equalsIgnoreCase("COALESCE")
        && call.getOperandList().size() == 2 && rex.getOperands().size() == 3) {
      return List.of(
          call.getOperandList().get(0),
          call.getOperandList().get(0),
          call.getOperandList().get(1));
    }
    SqlCall sourceNullif = sourceCallThroughCasts(sourceSql, "NULLIF");
    if (rexKind.equals("CASE") && sourceNullif != null
        && sourceNullif.getOperandList().size() == 2 && rex.getOperands().size() == 3) {
      SqlNode first = sourceNullif.getOperandList().get(0);
      SqlNode second = sourceNullif.getOperandList().get(1);
      List<SqlNode> operands = new ArrayList<>();
      operands.add(SqlStdOperatorTable.EQUALS.createCall(SqlParserPos.ZERO, first, second));
      operands.add(null);
      operands.add(first);
      return operands;
    }
    return call.getOperandList();
  }

  private static SqlIdentifier directIdempotentIsNullConjunctIdentifier(
      RexCall rex, SqlNode sourceSql) {
    if (!rex.getKind().name().equals("IS_NULL")
        || rex.getOperands().size() != 1
        || !(sourceSql instanceof SqlCall conjunction)
        || !conjunction.getKind().name().equals("AND")
        || conjunction.getOperandList().size() != 2) {
      return null;
    }
    SqlNode leftNode = conjunction.getOperandList().get(0);
    SqlNode rightNode = conjunction.getOperandList().get(1);
    if (!(leftNode instanceof SqlCall left)
        || !(rightNode instanceof SqlCall right)
        || !left.getKind().name().equals("IS_NULL")
        || !right.getKind().name().equals("IS_NULL")
        || left.getOperandList().size() != 1
        || right.getOperandList().size() != 1
        || !(left.getOperandList().get(0) instanceof SqlIdentifier leftIdentifier)
        || !(right.getOperandList().get(0) instanceof SqlIdentifier rightIdentifier)
        || !left.toString().equals(right.toString())
        || !leftIdentifier.toString().equals(rightIdentifier.toString())) {
      return null;
    }
    return leftIdentifier;
  }

  private static boolean directAsymmetricBetween(SqlCall source) {
    return source.getKind().name().equals("BETWEEN")
        && source.getOperandList().size() == 3
        && source.getOperator().getName().equalsIgnoreCase("BETWEEN ASYMMETRIC");
  }

  private static boolean exactExpandedBetween(RexCall rex) {
    if (rex.getOperands().size() != 2
        || !(rex.getOperands().get(0) instanceof RexCall lower)
        || !(rex.getOperands().get(1) instanceof RexCall upper)
        || !lower.getKind().name().equals("GREATER_THAN_OR_EQUAL")
        || !upper.getKind().name().equals("LESS_THAN_OR_EQUAL")
        || lower.getOperands().size() != 2
        || upper.getOperands().size() != 2) {
      return false;
    }
    return lower.getOperands().get(0).equals(upper.getOperands().get(0));
  }

  private static SqlCall positiveInForExactExpandedNotIn(
      RexCall rex, SqlCall source) {
    if (rex.getOperands().size() != 1
        || source.getOperandList().size() < 2
        || !(source.getOperandList().get(1) instanceof SqlNodeList values)) {
      return null;
    }
    RexNode positive = rex.getOperands().get(0);
    List<RexNode> comparisons;
    if (positive instanceof RexCall positiveCall
        && positiveCall.getKind().name().equals("OR")) {
      comparisons = positiveCall.getOperands();
    } else if (positive instanceof RexCall positiveCall
        && positiveCall.getKind().name().equals("EQUALS")) {
      comparisons = List.of(positiveCall);
    } else {
      return null;
    }
    List<SqlNode> matched = sourceInComparisons(comparisons, source, values);
    if (matched.isEmpty()
        || matched.size() != comparisons.size()
        || matched.size() != distinctSourceNodeCount(values)) {
      return null;
    }
    return SqlStdOperatorTable.IN.createCall(
        source.getParserPosition(), source.getOperandList().get(0), values);
  }

  private static SqlCall positiveInForExactNotInSubquery(
      RexCall rex, SqlCall source) {
    if (rex.getOperands().size() != 1
        || source.getOperandList().size() != 2
        || !(rex.getOperands().get(0) instanceof RexSubQuery positive)
        || !positive.getKind().name().equals("IN")
        || positive.getOperands().size() != 1
        || positive.rel.getRowType().getFieldCount() != 1) {
      return null;
    }
    SqlNode sourceValue = source.getOperandList().get(0);
    SqlNode sourceQuery = stripAlias(source.getOperandList().get(1));
    SqlSelect sourceSelect = topLevelSelect(sourceQuery);
    if (sourceValue == null
        || sourceSelect == null
        || sourceSelect.getSelectList() == null
        || sourceSelect.getSelectList().size() != 1
        || !windowExpressionAssociationMatches(
            positive.getOperands().get(0), sourceValue)) {
      return null;
    }
    // Calcite represents source `x NOT IN (SELECT y ...)` as an outer NOT
    // around a positive RexSubQuery IN. Rebuild only that exact positive
    // source call so the nested relational traversal enters the parsed SELECT
    // and can bind its own WHERE literals. The outer NOT retains the complete
    // NOT_IN source node; no source negation is erased or invented here.
    return SqlStdOperatorTable.IN.createCall(
        source.getParserPosition(), sourceValue, sourceQuery);
  }

  private static boolean exactExpandedIsNotDistinctFrom(RexCall rex) {
    if (rex.getOperands().size() != 2
        || !(rex.getOperands().get(0) instanceof RexCall nulls)
        || !nulls.getKind().name().equals("AND")
        || nulls.getOperands().size() != 2
        || !(nulls.getOperands().get(0) instanceof RexCall leftNull)
        || !(nulls.getOperands().get(1) instanceof RexCall rightNull)
        || !leftNull.getKind().name().equals("IS_NULL")
        || !rightNull.getKind().name().equals("IS_NULL")
        || leftNull.getOperands().size() != 1
        || rightNull.getOperands().size() != 1
        || !(rex.getOperands().get(1) instanceof RexCall isTrue)
        || !isTrue.getKind().name().equals("IS_TRUE")
        || isTrue.getOperands().size() != 1
        || !(isTrue.getOperands().get(0) instanceof RexCall equals)
        || !equals.getKind().name().equals("EQUALS")
        || equals.getOperands().size() != 2) {
      return false;
    }
    return leftNull.getOperands().get(0).equals(equals.getOperands().get(0))
        && rightNull.getOperands().get(0).equals(equals.getOperands().get(1));
  }

  private static SqlCall sourceCallThroughCasts(SqlNode sourceSql, String operator) {
    SqlNode current = sourceSql;
    while (current instanceof SqlCall call && call.getKind().name().equals("CAST")
        && !call.getOperandList().isEmpty()) {
      current = call.getOperandList().get(0);
    }
    if (current instanceof SqlCall call
        && call.getOperator().getName().equalsIgnoreCase(operator)) {
      return call;
    }
    return null;
  }

  private static SqlCase directSourceCase(
      RexCall rex, SqlNode sourceSql, SourcePositionMap sourcePositions) {
    if (sourceSql instanceof SqlCase sourceCase) {
      return sourceCase;
    }
    if (sourceSql instanceof SqlCall call
        && call.getKind().name().equals("CAST")
        && sourceCastTargetMatchesRex(call, rex, sourcePositions)
        && call.getOperandList().size() >= 2
        && call.getOperandList().get(0) instanceof SqlCase sourceCase
        && call.getOperandList().subList(2, call.getOperandList().size()).stream()
            .allMatch(Objects::isNull)) {
      return sourceCase;
    }
    return null;
  }

  private static boolean hasUnsupportedCollapsedSourceCast(
      RexNode rex, SqlNode sourceSql, SourcePositionMap sourcePositions) {
    if (!(sourceSql instanceof SqlCall sourceCast)
        || !sourceCast.getKind().name().equals("CAST")
        || rex.getKind().name().equals("CAST")
        || !sourceCastTargetMatchesRex(sourceCast, rex, sourcePositions)
        || sourceCast.getOperandList().size() < 2
        || sourceCast.getOperandList().subList(2, sourceCast.getOperandList().size()).stream()
            .anyMatch(Objects::nonNull)) {
      return false;
    }
    SqlNode operand = sourceCast.getOperandList().get(0);
    if (rex instanceof RexInputRef && operand instanceof SqlIdentifier identifier) {
      return !identifier.isStar();
    }
    return rex instanceof RexCall call
        && call.getKind().name().equals("CASE")
        && operand instanceof SqlCase sourceCase
        && windowExpressionAssociationMatches(call, sourceCase);
  }

  private static List<SqlNode> sourceCaseOperands(SqlCase sourceCase) {
    List<SqlNode> operands = new ArrayList<>();
    SqlNode value = sourceCase.getValueOperand();
    SqlNodeList whens = sourceCase.getWhenOperands();
    SqlNodeList thens = sourceCase.getThenOperands();
    if (whens.size() != thens.size()) {
      return List.of();
    }
    for (int i = 0; i < whens.size(); i++) {
      SqlNode condition = whens.get(i);
      if (value != null) {
        condition = SqlStdOperatorTable.EQUALS.createCall(SqlParserPos.ZERO, value, condition);
      }
      operands.add(condition);
      operands.add(thens.get(i));
    }
    operands.add(sourceCase.getElseOperand());
    return operands;
  }

  /**
   * Return the one terminal generated CASE operand whose source role is an
   * omitted ELSE, or {@code -1} when the complete generated/source shape is
   * not exact.  This is deliberately stricter than recognizing a NULL value:
   * every preceding generated operand must remain associated with the same
   * ordered source CASE role, the generated NULL must have the CASE result
   * type, and the source NULL must borrow the owning CASE's exact identity and
   * be followed directly by END in the submitted statement.
   */
  private static int exactImplicitCaseElseIndex(
      RexCall generated, SqlCase sourceCase, List<SqlNode> sourceOperands,
      SourceContext source) {
    SourcePositionMap sourcePositions = source.sourcePositions();
    if (sourceCase == null
        || sourcePositions == null
        || !generated.getKind().name().equals("CASE")
        || sourceOperands.size() < 3
        || sourceOperands.size() % 2 == 0
        || sourceOperands.size() != generated.getOperands().size()
        || !sourcePositions.exactImplicitCaseElse(sourceCase)) {
      return -1;
    }
    int terminal = sourceOperands.size() - 1;
    if (sourceOperands.get(terminal) != sourceCase.getElseOperand()
        || !(generated.getOperands().get(terminal) instanceof RexLiteral implicitElse)
        || implicitElse.getTypeName() != SqlTypeName.NULL
        || implicitElse.getValue() != null
        || !implicitElse.getType().isNullable()
        || !implicitElse.getType().equals(generated.getType())) {
      return -1;
    }
    SqlSelect owner = topLevelSelect(source.recoveryRoot());
    boolean exactOwner = owner != null
        && (sourcePositions.exactlyContains(owner, sourceCase)
            || isExactDirectOrderByDescendant(sourceCase, owner, source));
    for (int i = 0; i < terminal; i++) {
      SqlNode sourceOperand = sourceOperands.get(i);
      if (sourceOperand == null
          || !windowExpressionAssociationMatches(
                  generated.getOperands().get(i), sourceOperand)
              && !(exactOwner
                  && containsExactExplicitSelectAliasReference(
                      sourceOperand, owner, source)
                  && hiddenOrderExpressionAssociationMatches(
                      generated.getOperands().get(i), sourceOperand, owner,
                      sourcePositions, 16))) {
        return -1;
      }
    }
    return terminal;
  }

  private static boolean containsExactExplicitSelectAliasReference(
      SqlNode node, SqlSelect owner, SourceContext source) {
    SourcePositionMap sourcePositions = source.sourcePositions();
    if (node instanceof SqlIdentifier identifier && identifier.isSimple()) {
      SqlNode definition = explicitSelectAliasExpression(owner, identifier);
      return definition != null
          && (sourcePositions.exactlyContains(owner, identifier)
              || isExactDirectOrderByDescendant(identifier, owner, source))
          && sourcePositions.exactlyContains(owner, definition);
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        if (containsExactExplicitSelectAliasReference(item, owner, source)) {
          return true;
        }
      }
    } else if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        if (containsExactExplicitSelectAliasReference(operand, owner, source)) {
          return true;
        }
      }
    }
    return false;
  }

  private static boolean isExactDirectOrderByDescendant(
      SqlNode node, SqlSelect owner, SourceContext source) {
    SqlNode universe = source.literalUniverse();
    SqlOrderBy orderBy = sourceTopLevelOrderBy(universe);
    return orderBy != null
        && orderBy.orderList != null
        && sourceProjectionSelect(universe) == owner
        && containsNodeWithoutNestedWith(orderBy.orderList, node);
  }

  private static boolean sourceCastTargetMatchesRex(
      SqlCall sourceCast, RexNode rex, SourcePositionMap sourcePositions) {
    if (sourceCast.getOperandList().size() < 2 || sourceCast.getOperandList().get(1) == null) {
      return false;
    }
    String sourceTypeText = sourceCast.getOperandList().get(1).toString();
    PostgresTypeSpec sourceType;
    try {
      sourceType = classifyPostgresType(sourceTypeText);
    } catch (IllegalArgumentException ignored) {
      sourceType = exactNormalizedDoubleSourceType(
          sourceCast, sourceTypeText, sourcePositions);
      if (sourceType == null) {
        return false;
      }
    }
    if (sourceType.type() != rex.getType().getSqlTypeName()) {
      return false;
    }
    if (sourceType.type() != SqlTypeName.CHAR && sourceType.type() != SqlTypeName.VARCHAR) {
      return true;
    }
    return sourceType.precision() == RelDataType.PRECISION_NOT_SPECIFIED
        || sourceType.precision() == rex.getType().getPrecision();
  }

  /**
   * Calcite renders both parsed PostgreSQL {@code DOUBLE PRECISION} and
   * {@code FLOAT8} datatype nodes as {@code DOUBLE}.  Recover that one lossy
   * display normalization only when the datatype node's exact submitted text
   * independently proves one of those PostgreSQL spellings.  The shared
   * declaration classifier intentionally continues to reject bare
   * {@code DOUBLE}, which PostgreSQL does not accept as a type name.
   */
  private static PostgresTypeSpec exactNormalizedDoubleSourceType(
      SqlCall sourceCast, String renderedType, SourcePositionMap sourcePositions) {
    if (!renderedType.equalsIgnoreCase("DOUBLE")
        || sourcePositions == null
        || sourceCast.getOperandList().size() < 2) {
      return null;
    }
    String exactType = sourcePositions.sourceText(sourceCast.getOperandList().get(1));
    if (exactType == null) {
      return null;
    }
    String normalized = trimPostgresSqlWhitespace(exactType)
        .replaceAll("\\s+", " ")
        .toUpperCase(Locale.ROOT);
    if (!normalized.equals("DOUBLE PRECISION") && !normalized.equals("FLOAT8")) {
      return null;
    }
    return new PostgresTypeSpec(
        SqlTypeName.DOUBLE,
        RelDataType.PRECISION_NOT_SPECIFIED,
        RelDataType.SCALE_NOT_SPECIFIED,
        false);
  }

  private static boolean allSourceNodesEquivalent(SqlNodeList nodes) {
    if (nodes.isEmpty()) {
      return false;
    }
    String first = nodes.get(0).toString();
    for (int i = 1; i < nodes.size(); i++) {
      if (!first.equals(nodes.get(i).toString())) {
        return false;
      }
    }
    return true;
  }

  private static List<SqlNode> sourceInComparisons(
      List<RexNode> rexComparisons, SqlCall sourceIn, SqlNodeList sourceValues) {
    List<SqlNode> comparisons = new ArrayList<>();
    SqlNode sourceValue = sourceIn.getOperandList().get(0);
    List<SqlNode> orderedDistinctValues = new ArrayList<>();
    List<String> exactTexts = new ArrayList<>();
    for (SqlNode candidate : sourceValues) {
      String exactText = candidate.toString();
      if (!exactTexts.contains(exactText)) {
        exactTexts.add(exactText);
        orderedDistinctValues.add(candidate);
      }
    }
    if (rexComparisons.size() != orderedDistinctValues.size()) {
      return List.of();
    }
    for (int index = 0; index < rexComparisons.size(); index++) {
      RexNode rexNode = rexComparisons.get(index);
      if (!(rexNode instanceof RexCall comparison)
          || !comparison.getKind().name().equals("EQUALS")
          || comparison.getOperands().size() != 2) {
        return List.of();
      }
      RexLiteral rexLiteral = rexLiteralThroughCasts(comparison.getOperands().get(1));
      SqlNode sourceCandidate = orderedDistinctValues.get(index);
      SqlLiteral sourceLiteral = sourceLiteralThroughCasts(sourceCandidate);
      CanonicalLiteral rexCanonical = rexLiteral == null
          ? null
          : canonicalRexLiteral(rexLiteral);
      CanonicalLiteral sourceCanonical = sourceLiteral == null
          ? null
          : canonicalSourceLiteral(sourceLiteral);
      if (rexCanonical == null || !rexCanonical.equals(sourceCanonical)) {
        return List.of();
      }
      comparisons.add(
          SqlStdOperatorTable.EQUALS.createCall(SqlParserPos.ZERO, sourceValue, sourceCandidate));
    }
    return comparisons;
  }

  private static List<SqlNode> alignFlattenedOrOperands(
      List<RexNode> rexOperands, List<SqlNode> sourceOperands) {
    List<SqlNode> aligned = new ArrayList<>();
    int rexIndex = 0;
    for (SqlNode sourceOperand : sourceOperands) {
      if (sourceOperand instanceof SqlCall sourceCall
          && sourceCall.getKind().name().equals("IN")
          && sourceCall.getOperandList().size() >= 2
          && sourceCall.getOperandList().get(1) instanceof SqlNodeList sourceValues) {
        int maximumComparisons = distinctSourceNodeCount(sourceValues);
        if (rexIndex + maximumComparisons > rexOperands.size()) {
          return List.of();
        }
        List<SqlNode> comparisons = sourceInComparisons(
            rexOperands.subList(rexIndex, rexIndex + maximumComparisons),
            sourceCall,
            sourceValues);
        if (comparisons.size() != maximumComparisons) {
          return List.of();
        }
        aligned.addAll(comparisons);
        rexIndex += maximumComparisons;
      } else {
        if (rexIndex >= rexOperands.size()) {
          return List.of();
        }
        aligned.add(sourceOperand);
        rexIndex++;
      }
    }
    return rexIndex == rexOperands.size() ? aligned : List.of();
  }

  private static int distinctSourceNodeCount(SqlNodeList nodes) {
    List<String> texts = new ArrayList<>();
    for (SqlNode node : nodes) {
      String text = node.toString();
      if (!texts.contains(text)) {
        texts.add(text);
      }
    }
    return texts.size();
  }

  private static RexLiteral rexLiteralThroughCasts(RexNode rex) {
    RexNode node = rex;
    while (node instanceof RexCall call && call.getKind().name().equals("CAST")
        && call.getOperands().size() == 1) {
      node = call.getOperands().get(0);
    }
    return node instanceof RexLiteral literal ? literal : null;
  }

  private static SqlLiteral sourceLiteralThroughCasts(SqlNode source) {
    SqlNode node = source;
    while (node instanceof SqlCall call && call.getKind().name().equals("CAST")
        && !call.getOperandList().isEmpty()) {
      node = call.getOperandList().get(0);
    }
    return node instanceof SqlLiteral literal ? literal : null;
  }

  private static void flattenAssociativeSourceOperands(
      SqlNode sourceSql, String kind, List<SqlNode> operands) {
    if (sourceSql instanceof SqlCall call && call.getKind().name().equals(kind)) {
      for (SqlNode operand : call.getOperandList()) {
        flattenAssociativeSourceOperands(operand, kind, operands);
      }
    } else {
      operands.add(sourceSql);
    }
  }

  private enum SourceClausePhase {
    UNKNOWN,
    POST_AGGREGATE,
    PRE_AGGREGATE
  }

  private record SourceInSubqueryOrderAttestation(
      String kind,
      String queryBlockId,
      String selectNodeId,
      String selectText,
      String orderByNodeId,
      String orderByText,
      String sourceSelectSql,
      String sourceOrderBySql,
      String projectItemNodeId,
      String projectItemText,
      String sourceProjectItemSql,
      int projectInputIndex,
      String projectBaseFieldName,
      String projectFieldType,
      boolean projectFieldNullable,
      String orderItemNodeId,
      String orderItemText,
      String sourceOrderItemSql,
      String direction,
      String nullDirection,
      String sourceRelationNodeId,
      String sourceRelationText,
      String sourceRelationSql,
      List<String> baseTable,
      int orderFieldIndex,
      String orderBaseFieldName,
      String orderFieldType,
      boolean orderFieldNullable,
      int generatedProjectArity,
      int generatedSortInputArity) {}

  private record SourceGroupingAttestation(
      String kind,
      String queryBlockId,
      String sourceSelectNodeId,
      String sourceSelectText,
      String sourceSelectSql,
      String sourceGroupNodeId,
      String sourceGroupText,
      String sourceGroupSql,
      List<Integer> groupIndexes,
      List<List<Integer>> groupingSets,
      List<List<Integer>> sourceOperandIndexes,
      List<List<SqlNode>> sourceOperands,
      boolean sourceHasWhere,
      boolean sourceHasHaving) {}

  private record SourceDistinctAttestation(
      String kind,
      String queryBlockId,
      String sourceSelectNodeId,
      String sourceSelectText,
      List<Integer> groupIndexes,
      List<List<Integer>> groupingSets,
      int inputOutputArity,
      int outputArity) {}

  private record SourceWhereAttestation(
      String queryBlockId,
      String ownerNodeId,
      String sourceConditionNodeId,
      String sourceConditionSql,
      String sourceConditionKind,
      String sourceConditionOperator,
      String generatedConditionSql,
      int filterOutputArity,
      int inputOutputArity,
      List<String> variablesSet,
      List<SourceWhereInputBinding> inputBindings,
      List<SourceWhereAnalysisErrorBinding> analysisErrors) {}

  private record SourceWhereInputBinding(
      String path,
      int inputIndex,
      String sourceSql,
      String sourceRelationNodeId,
      String sourceRelationSql,
      List<String> baseTable,
      int tableFieldIndex,
      String baseFieldName,
      String generatedFieldName) {}

  private record SourceWhereAnalysisErrorBinding(
      String kind,
      String rexPath,
      int identifierOperand,
      int literalOperand,
      String generatedComparisonSql,
      int inputIndex,
      List<String> baseTable,
      int tableFieldIndex,
      String baseFieldName,
      String sourceLiteralCanonicalValue,
      String generatedLiteralCanonicalValue) {}

  private record SourceWhereInputOrigin(
      TableScan scan,
      DirectTableSource sourceTable,
      int tableFieldIndex,
      String sourceRelationNodeId,
      String sourceRelationSql) {}

  private record SourceNativeHavingAttestation(
      String kind,
      String queryBlockId,
      String ownerNodeId,
      String sourceOwnerSql,
      String sourceOwnerText,
      String sourceSelectSql,
      String sourceSelectText,
      String sourceConditionNodeId,
      String sourceConditionSql,
      String sourceConditionText,
      String generatedConditionSql,
      int aggregateOutputArity,
      int aggregateCallCount,
      List<SourceNativeHavingOperandBinding> operandBindings) {}

  private record SourceNativeHavingOperandBinding(
      String path,
      int aggregateOutputIndex,
      String sourceSql,
      String sourceKind,
      String sourceOperator) {}

  private record SourceAggregateBinding(SqlCall call, SqlNode filter) {}

  private record AggregateInputSource(SqlNode role, SqlNode definition) {}

  /**
   * One exact base-relation occurrence from the independently parsed source
   * AST.  {@code columnAliases} is ordered and may be a proper prefix of the
   * table row, exactly as PostgreSQL permits for a relation alias column list.
   * It is never inferred from Calcite output labels.
   */
  private record DirectTableSource(
      SqlIdentifier table, SqlIdentifier alias, List<SqlIdentifier> columnAliases) {}

  private record SourceWhereWildcardSegment(int start, int width) {}

  private record SourceRelInputColumn(int inputOrdinal, int inputOutputIndex) {}

  private record SourceRelOutputLineage(
      int outputIndex,
      String kind,
      String generatedFieldName,
      ExactSourceIdentity source,
      List<SourceRelInputColumn> inputs) {}

  private record SourceRelCorrespondence(
      String sourceRole,
      String generatedType,
      String queryBlockId,
      ExactSourceIdentity source,
      List<SourceRelOutputLineage> outputs,
      List<SourceRelCorrespondence> inputs) {}

  private record SourceTableBinding(
      SqlNode relation,
      SqlIdentifier table,
      SqlIdentifier alias,
      DirectTableSource source) {}

  private record SourceCteUse(
      SqlNode relation,
      SqlIdentifier reference,
      SqlIdentifier definitionName,
      SqlNode definitionQuery,
      SqlWithItem definitionItem,
      SqlNodeList definitionList,
      SqlNode definitionBody,
      SqlWith definitionWith,
      String referenceScopeKind,
      SqlNode referenceScope) {}

  private record CteDefinitionBinding(SqlWith owner, SqlWithItem item) {}

  private record CteReferenceScope(String kind, SqlNode container) {}

  private record AlignedOrderByInput(
      SqlNode relation, DirectTableSource source, TableScan scan) {}

  private record CanonicalLiteral(String family, String canonicalValue) {}

  private record SourceOrderAliasReference(
      SqlNode orderItem, SqlNode expression, SqlIdentifier reference, String name) {}

  private record SourceOrderAliasInputBinding(
      String sourceRelationNodeId,
      String sourceRelationSql,
      String sourceTableNodeId,
      String sourceTableSql,
      String sourceAliasNodeId,
      String sourceAliasSql,
      List<String> baseTable) {}

  private record SourceQueryAnalysisError(
      String kind,
      String sqlState,
      String queryBlockId,
      String sourceQueryBlockSql,
      String sourceOrderItemNodeId,
      String sourceOrderItemSql,
      String sourceOrderListNodeId,
      String sourceOrderListSql,
      String sourceOrderExpressionNodeId,
      String sourceOrderExpressionSql,
      String sourceAliasReferenceNodeId,
      String sourceAliasReferenceSql,
      String sourceOutputAliasNodeId,
      String sourceOutputAliasSql,
      String sourceFromNodeId,
      String sourceFromSql,
      String outputAlias,
      List<SourceOrderAliasInputBinding> inputBindings) {}

  private record SourceAmbiguousColumnError(
      String kind,
      String sqlState,
      String queryBlockId,
      String sourceQueryBlockSql,
      String sourceIdentifierNodeId,
      String sourceIdentifierSql,
      String sourceRelationNodeId,
      String sourceRelationSql,
      String identifierName,
      boolean identifierQuoted,
      int duplicateCount,
      List<SourceAmbiguousColumnOutput> matchingOutputs) {}

  private record SourceAmbiguousColumnOutput(
      int outputIndex,
      String outputName,
      String sourceOutputItemNodeId,
      String sourceOutputItemSql,
      String sourceOriginRelationNodeId,
      String sourceOriginRelationSql) {}

  /** Internal exact source namespace entry. The output item is supplied by
   * the enclosing SELECT wildcard; originRelation identifies the exact FROM
   * input whose public row contributes this position. */
  private record SourceDerivedPublicOutput(
      String outputName,
      SqlNode sourceOutputItem,
      SqlNode sourceOriginRelation,
      RelDataType outputType) {}

  private record ExactSourceIdentity(String nodeId, String text) {}

  private record SourceOrderItemAttestation(
      ExactSourceIdentity item, ExactSourceIdentity expression) {}

  private record SourceOrderAttestation(
      ExactSourceIdentity query,
      ExactSourceIdentity orderList,
      List<SourceOrderItemAttestation> items) {}

  private record SourceProjectedExpansion(
      String kind,
      SqlIdentifier reference,
      SqlNode definition,
      SqlNode projectItem,
      SqlNode outputAlias,
      SqlSelect innerSelect,
      SqlNode outerFrom,
      SqlSelect outerSelect,
      Integer publicOutputIndex,
      SourceCteUse cteUse) {}

  private record ProjectedSourceResolution(
      SqlNode source, SourceProjectedExpansion expansion, SqlNode matchedDefinition) {
    static ProjectedSourceResolution direct(SqlNode source) {
      return new ProjectedSourceResolution(source, null, null);
    }

    static ProjectedSourceResolution exactCrossScopeReference(
        SqlNode source, SqlNode matchedDefinition) {
      return new ProjectedSourceResolution(source, null, matchedDefinition);
    }
  }

  private record SourceContext(
      SqlNode node,
      SqlNode recoveryRoot,
      SqlNode literalUniverse,
      CteProvenanceScopes cteScopes,
      Map<String, SqlNode> ctes,
      boolean allowLiteralRecovery,
      boolean allowDirectProjectedOperandExpansion,
      SourceClausePhase clausePhase,
      String queryBlockId,
      String rootQueryBlockId,
      SourcePositionMap sourcePositions) {
    static SourceContext empty() {
      return new SourceContext(
          null, null, null, CteProvenanceScopes.empty(), Map.of(), false, false,
          SourceClausePhase.UNKNOWN, null, null, null);
    }

    static SourceContext root(SqlNode node) {
      return root(node, null);
    }

    static SourceContext root(SqlNode node, SourcePositionMap sourcePositions) {
      CteProvenanceScopes scopes = CteProvenanceScopes.forRoot(node);
      String rootQueryBlockId = sourceRelQueryBlockId(node, sourcePositions);
      return new SourceContext(
          node, literalRecoveryRoot(node), node, scopes,
          scopes.environmentFor(node, Map.of()), true, false,
          SourceClausePhase.POST_AGGREGATE,
          rootQueryBlockId,
          rootQueryBlockId,
          sourcePositions);
    }

    SourceContext withNode(SqlNode next) {
      SqlNode nextRecoveryRoot = startsLiteralRecoveryScope(next)
          ? literalRecoveryRoot(next)
          : recoveryRoot;
      boolean nextAllowsRecovery = next != null || allowLiteralRecovery;
      SourceClausePhase nextClausePhase = next != node && topLevelSelect(next) != null
          ? SourceClausePhase.POST_AGGREGATE
          : clausePhase;
      String nextIdentity = sourceRelQueryBlockId(next, sourcePositions);
      String nextQueryBlockId = nextIdentity == null ? queryBlockId : nextIdentity;
      return new SourceContext(
          next, nextRecoveryRoot, literalUniverse, cteScopes,
          cteScopes.environmentFor(next, ctes), nextAllowsRecovery,
          allowDirectProjectedOperandExpansion,
          nextClausePhase, nextQueryBlockId, rootQueryBlockId, sourcePositions);
    }

    SourceContext nestedRoot(SqlNode next) {
      String nestedQueryBlockId = sourceRelQueryBlockId(next, sourcePositions);
      return new SourceContext(
          next, literalRecoveryRoot(next), literalUniverse, cteScopes,
          cteScopes.environmentFor(next, ctes), next != null,
          false,
          SourceClausePhase.POST_AGGREGATE,
          nestedQueryBlockId,
          nestedQueryBlockId,
          sourcePositions);
    }

    SourceContext withoutLiteralRecovery() {
      return new SourceContext(
          node, recoveryRoot, literalUniverse, cteScopes, ctes, false,
          allowDirectProjectedOperandExpansion,
          clausePhase, queryBlockId, rootQueryBlockId, sourcePositions);
    }

    SourceContext beforeAggregate() {
      return new SourceContext(
          node, recoveryRoot, literalUniverse, cteScopes, ctes,
          allowLiteralRecovery, allowDirectProjectedOperandExpansion,
          SourceClausePhase.PRE_AGGREGATE, queryBlockId,
          rootQueryBlockId, sourcePositions);
    }

    SourceContext withDirectProjectedOperandExpansion() {
      return new SourceContext(
          node, recoveryRoot, literalUniverse, cteScopes, ctes,
          allowLiteralRecovery, true, clausePhase, queryBlockId,
          rootQueryBlockId, sourcePositions);
    }

  }

  /**
   * PostgreSQL CTE source provenance is lexical and ordered.  The environment
   * attached to a nonrecursive CTE body contains the enclosing CTEs plus only
   * preceding siblings; the WITH main body sees every sibling.  Identity keys
   * tie each environment to the exact independently parsed source AST node, so
   * relational traversal cannot silently reuse a same-spelled node from a
   * different scope.
   */
  private static final class CteProvenanceScopes {
    private final IdentityHashMap<SqlNode, Map<String, SqlNode>> environments =
        new IdentityHashMap<>();

    static CteProvenanceScopes empty() {
      return new CteProvenanceScopes();
    }

    static CteProvenanceScopes forRoot(SqlNode root) {
      CteProvenanceScopes scopes = new CteProvenanceScopes();
      scopes.indexNode(root, Map.of());
      return scopes;
    }

    Map<String, SqlNode> environmentFor(
        SqlNode node, Map<String, SqlNode> inherited) {
      if (node == null) {
        return inherited;
      }
      Map<String, SqlNode> exact = environments.get(node);
      if (exact != null) {
        return exact;
      }
      if (startsLiteralRecoveryScope(node)) {
        throw new IllegalArgumentException(
            "cannot align PostgreSQL query scope with an exact CTE provenance environment: "
                + node);
      }
      // Validator-generated scalar calls are not members of the independently
      // parsed source tree.  They remain inside the current lexical query and
      // may safely inherit its environment; query-shaped nodes never do so.
      return inherited;
    }

    private Map<String, SqlNode> indexNode(
        SqlNode node, Map<String, SqlNode> environment) {
      if (node == null) {
        return environment;
      }
      if (node instanceof SqlOrderBy orderBy) {
        Map<String, SqlNode> queryEnvironment = indexNode(orderBy.query, environment);
        register(orderBy, queryEnvironment);
        for (SqlNode operand : orderBy.getOperandList()) {
          if (operand != orderBy.query) {
            indexNode(operand, queryEnvironment);
          }
        }
        return queryEnvironment;
      }
      if (node instanceof SqlWith with) {
        LinkedHashMap<String, SqlNode> visible = new LinkedHashMap<>(environment);
        Set<String> localNames = new HashSet<>();
        for (SqlNode rawItem : with.withList) {
          if (!(rawItem instanceof SqlWithItem item)
              || item.name == null || item.name.names.size() != 1
              || item.query == null) {
            throw new IllegalArgumentException(
                "unsupported PostgreSQL WITH item in source provenance: " + rawItem);
          }
          if (item.recursive != null && item.recursive.booleanValue()) {
            throw new IllegalArgumentException(
                "recursive PostgreSQL WITH provenance is not supported");
          }
          String canonicalName = item.name.names.get(0);
          if (!localNames.add(canonicalName)) {
            throw new IllegalArgumentException(
                "ambiguous PostgreSQL CTE identifier in source provenance: " + canonicalName);
          }
          Map<String, SqlNode> definitionEnvironment = Map.copyOf(visible);
          indexNode(item.query, definitionEnvironment);
          visible.put(canonicalName, item.query);
        }
        Map<String, SqlNode> bodyEnvironment = Map.copyOf(visible);
        indexNode(with.body, bodyEnvironment);
        register(with, bodyEnvironment);
        return bodyEnvironment;
      }

      register(node, environment);
      if (node instanceof SqlNodeList list) {
        for (SqlNode item : list) {
          indexNode(item, environment);
        }
      } else if (node instanceof SqlCall call) {
        for (SqlNode operand : call.getOperandList()) {
          indexNode(operand, environment);
        }
      }
      return environment;
    }

    private void register(SqlNode node, Map<String, SqlNode> environment) {
      Map<String, SqlNode> previous = environments.putIfAbsent(node, environment);
      if (previous != null && !previous.equals(environment)) {
        throw new IllegalArgumentException(
            "source SQL node appears in multiple PostgreSQL CTE provenance environments: "
                + node);
      }
    }
  }

  private static List<SqlNode> directCteQueries(SqlNode root) {
    SqlNode query = root instanceof SqlOrderBy orderBy ? orderBy.query : root;
    if (!(query instanceof SqlWith with)) {
      return List.of();
    }
    List<SqlNode> queries = new ArrayList<>();
    for (SqlNode rawItem : with.withList) {
      if (!(rawItem instanceof SqlWithItem item) || item.query == null) {
        throw new IllegalArgumentException(
            "unsupported PostgreSQL WITH item during literal provenance recovery: " + rawItem);
      }
      queries.add(item.query);
    }
    return queries;
  }

  private static SqlNode literalRecoveryRoot(SqlNode node) {
    if (node instanceof SqlSelect || node instanceof SqlOrderBy
        || node instanceof SqlCall call
            && (call.getKind().name().equals("WITH") || isSetQueryCall(call))) {
      return sourceQueryBody(node);
    }
    return node;
  }

  private static boolean startsLiteralRecoveryScope(SqlNode node) {
    if (node instanceof SqlSelect || node instanceof SqlOrderBy) {
      return true;
    }
    if (!(node instanceof SqlCall call)) {
      return false;
    }
    return isSetQueryCall(call)
        || call.getKind().name().equals("WITH")
        || call.getKind().name().equals("ROW");
  }

  private static void emitRexLiteralFields(Json out, RexLiteral literal) {
    out.comma();
    out.name("literalTypeName").value(literal.getTypeName().getName());
    out.comma();
    out.name("literalValue").value(nullableToString(literal.getValue()));
    out.comma();
    // RexLiteral.getValue2() is the calculator carrier, not an exact SQL
    // value view.  For DECIMAL it narrows BigDecimal.unscaledValue() through
    // longValue(), silently wrapping as soon as the unscaled value exceeds
    // signed BIGINT.  Logos uses this field as an independent exact payload
    // cross-check, so retain the arbitrary-precision BigInteger instead.
    Object literalValue2 = literal.getTypeName() == SqlTypeName.DECIMAL
        ? RexLiteral.bigDecimalValue(literal).unscaledValue()
        : literal.getValue2();
    out.name("literalValue2").value(nullableToString(literalValue2));
    String valueAsString = literalValueAsString(literal);
    if (valueAsString != null) {
      out.comma();
      out.name("literalValueAsString").value(valueAsString);
    }

    String dateLiteral = dateLiteralValue(literal);
    if (dateLiteral != null) {
      out.comma();
      out.name("dateLiteral").value(dateLiteral);
    }

    String timeLiteral = timeLiteralValue(literal);
    if (timeLiteral != null) {
      out.comma();
      out.name("timeLiteral").value(timeLiteral);
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

  }

  private static String literalValueAsString(RexLiteral literal) {
    try {
      return literal.getValueAs(String.class);
    } catch (RuntimeException | AssertionError e) {
      return null;
    }
  }

  private static SqlNode uniqueCharacterLiteralSource(
      RexLiteral literal, SqlNode sourceRoot) {
    if (sourceRoot == null
        || (literal.getTypeName() != SqlTypeName.CHAR
            && literal.getTypeName() != SqlTypeName.VARCHAR)) {
      return null;
    }
    String rexValue = literalValueAsString(literal);
    if (rexValue == null) {
      return null;
    }
    String semanticValue = trimTrailingSpaces(rexValue);
    List<CharacterLiteralSource> candidates = new ArrayList<>();
    collectCharacterLiterals(sourceRoot, candidates);
    SqlNode matched = null;
    for (CharacterLiteralSource candidate : candidates) {
      if (!trimTrailingSpaces(candidate.value()).equals(semanticValue)) {
        continue;
      }
      if (matched != null && !matched.toString().equals(candidate.node().toString())) {
        return null;
      }
      matched = candidate.node();
    }
    return matched;
  }

  private static SqlNode uniqueCharacterLiteralSourceAcrossQuery(
      RexLiteral literal, SqlNode sourceRoot) {
    if (sourceRoot == null
        || (literal.getTypeName() != SqlTypeName.CHAR
            && literal.getTypeName() != SqlTypeName.VARCHAR)) {
      return null;
    }
    String rexValue = literalValueAsString(literal);
    if (rexValue == null) {
      return null;
    }
    String semanticValue = trimTrailingSpaces(rexValue);
    List<CharacterLiteralSource> candidates = new ArrayList<>();
    collectAllCharacterLiterals(sourceRoot, candidates);
    SqlNode matched = null;
    for (CharacterLiteralSource candidate : candidates) {
      if (!trimTrailingSpaces(candidate.value()).equals(semanticValue)) {
        continue;
      }
      if (matched != null && !matched.toString().equals(candidate.node().toString())) {
        return null;
      }
      matched = candidate.node();
    }
    return matched;
  }

  private static SqlNode uniqueStringConcatSource(RexCall rex, SqlNode sourceRoot) {
    RexCall concat = rexStringConcatCall(rex);
    if (concat == null || sourceRoot == null) {
      return null;
    }
    List<String> rexLiterals = new ArrayList<>();
    collectRexCharacterLiteralValues(concat, rexLiterals);
    if (rexLiterals.isEmpty()) {
      return null;
    }
    List<SqlNode> candidates = new ArrayList<>();
    collectAllStringConcatSources(sourceRoot, candidates);
    SqlNode matched = null;
    for (SqlNode candidate : candidates) {
      List<String> sourceLiterals = new ArrayList<>();
      collectSourceCharacterLiteralValues(candidate, sourceLiterals);
      if (!sourceLiterals.equals(rexLiterals)) {
        continue;
      }
      if (matched != null && !matched.toString().equals(candidate.toString())) {
        return null;
      }
      matched = candidate;
    }
    return matched;
  }

  private static RexCall rexStringConcatCall(RexCall call) {
    if (call.getOperator().getName().equals("||")) {
      return call;
    }
    if (call.getKind().name().equals("CAST") && call.getOperands().size() == 1
        && call.getOperands().get(0) instanceof RexCall operand
        && operand.getOperator().getName().equals("||")) {
      return operand;
    }
    return null;
  }

  private static void collectRexCharacterLiteralValues(
      RexNode node, List<String> values) {
    if (node instanceof RexLiteral literal
        && (literal.getTypeName() == SqlTypeName.CHAR
            || literal.getTypeName() == SqlTypeName.VARCHAR)) {
      String value = literalValueAsString(literal);
      if (value != null) {
        values.add(trimTrailingSpaces(value));
      }
      return;
    }
    if (node instanceof RexCall call) {
      for (RexNode operand : call.getOperands()) {
        collectRexCharacterLiteralValues(operand, values);
      }
    }
  }

  private static void collectSourceCharacterLiteralValues(
      SqlNode node, List<String> values) {
    if (node instanceof SqlLiteral literal) {
      String value = sourceCharacterLiteralValue(literal);
      if (value != null) {
        values.add(trimTrailingSpaces(value));
      }
      return;
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectSourceCharacterLiteralValues(item, values);
      }
    } else if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        collectSourceCharacterLiteralValues(operand, values);
      }
    }
  }

  private static void collectAllStringConcatSources(
      SqlNode node, List<SqlNode> candidates) {
    if (node == null) {
      return;
    }
    if (node instanceof SqlCall call && call.getKind().name().equals("CAST")
        && !call.getOperandList().isEmpty()
        && stripAlias(call.getOperandList().get(0)) instanceof SqlCall operand
        && operand.getOperator().getName().equals("||")) {
      candidates.add(call);
      return;
    }
    if (node instanceof SqlCall call && call.getOperator().getName().equals("||")) {
      candidates.add(call);
      return;
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectAllStringConcatSources(item, candidates);
      }
    } else if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        collectAllStringConcatSources(operand, candidates);
      }
    }
  }

  private static SqlNode uniqueNullLiteralSource(SqlNode sourceRoot) {
    if (sourceRoot == null) {
      return null;
    }
    List<SqlNode> candidates = new ArrayList<>();
    collectNullLiterals(sourceRoot, candidates);
    if (candidates.isEmpty()) {
      return null;
    }
    SqlNode matched = candidates.get(0);
    for (int i = 1; i < candidates.size(); i++) {
      if (!matched.toString().equals(candidates.get(i).toString())) {
        return null;
      }
    }
    return matched;
  }

  private static SqlNode uniqueNullLiteralSourceAcrossQuery(SqlNode sourceRoot) {
    if (sourceRoot == null) {
      return null;
    }
    List<SqlNode> candidates = new ArrayList<>();
    collectAllNullLiterals(sourceRoot, candidates);
    if (candidates.isEmpty()) {
      return null;
    }
    SqlNode matched = candidates.get(0);
    for (int i = 1; i < candidates.size(); i++) {
      if (!matched.toString().equals(candidates.get(i).toString())) {
        return null;
      }
    }
    return matched;
  }

  private static void collectAllCharacterLiterals(
      SqlNode node, List<CharacterLiteralSource> literals) {
    if (node == null) {
      return;
    }
    if (node instanceof SqlCall call && call.getKind().name().equals("CAST")
        && !call.getOperandList().isEmpty()
        && call.getOperandList().get(0) instanceof SqlLiteral literal
        && sourceCharacterLiteralValue(literal) != null) {
      literals.add(new CharacterLiteralSource(call, literal.getStringValue()));
      return;
    }
    if (node instanceof SqlLiteral literal) {
      String value = sourceCharacterLiteralValue(literal);
      if (value != null) {
        literals.add(new CharacterLiteralSource(literal, value));
      }
      return;
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectAllCharacterLiterals(item, literals);
      }
    } else if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        collectAllCharacterLiterals(operand, literals);
      }
    }
  }

  private static void collectAllNullLiterals(SqlNode node, List<SqlNode> literals) {
    if (node == null) {
      return;
    }
    if (node instanceof SqlCall call && call.getKind().name().equals("CAST")
        && !call.getOperandList().isEmpty()
        && call.getOperandList().get(0) instanceof SqlLiteral literal
        && literal.getTypeName() == SqlTypeName.NULL) {
      literals.add(call);
      return;
    }
    if (node instanceof SqlLiteral literal) {
      if (literal.getTypeName() == SqlTypeName.NULL) {
        literals.add(literal);
      }
      return;
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectAllNullLiterals(item, literals);
      }
    } else if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        collectAllNullLiterals(operand, literals);
      }
    }
  }

  private static void collectCharacterLiterals(
      SqlNode node, List<CharacterLiteralSource> literals) {
    collectCharacterLiterals(node, literals, true);
  }

  private static void collectCharacterLiterals(
      SqlNode node, List<CharacterLiteralSource> literals, boolean isRoot) {
    if (node == null) {
      return;
    }
    if (isRoot && node instanceof SqlOrderBy orderBy) {
      collectCharacterLiterals(orderBy.query, literals, true);
      return;
    }
    if (isRoot && node instanceof SqlCall withCall
        && withCall.getKind().name().equals("WITH")) {
      for (SqlNode cte : directCteQueries(node)) {
        collectCharacterLiterals(cte, literals, true);
      }
      List<SqlNode> operands = withCall.getOperandList();
      if (!operands.isEmpty()) {
        collectCharacterLiterals(operands.get(operands.size() - 1), literals, true);
      }
      return;
    }
    if (isRoot && node instanceof SqlCall setCall && isSetQueryCall(setCall)) {
      // A validator-generated coercion Project can sit above several set
      // branches. Search each direct branch as a recovery root, while the
      // recursive calls below still stop at subqueries nested inside a branch.
      for (SqlNode operand : setCall.getOperandList()) {
        collectCharacterLiterals(operand, literals, true);
      }
      return;
    }
    if (!isRoot && startsLiteralRecoveryScope(node)) {
      return;
    }
    if (node instanceof SqlCall call && call.getKind().name().equals("CAST")
        && !call.getOperandList().isEmpty()
        && call.getOperandList().get(0) instanceof SqlLiteral literal
        && sourceCharacterLiteralValue(literal) != null) {
      literals.add(new CharacterLiteralSource(call, literal.getStringValue()));
      return;
    }
    if (node instanceof SqlLiteral literal) {
      String value = sourceCharacterLiteralValue(literal);
      if (value != null) {
        literals.add(new CharacterLiteralSource(literal, value));
      }
      return;
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectCharacterLiterals(item, literals, false);
      }
      return;
    }
    if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        collectCharacterLiterals(operand, literals, false);
      }
    }
  }

  private static void collectNullLiterals(SqlNode node, List<SqlNode> literals) {
    collectNullLiterals(node, literals, true);
  }

  private static void collectNullLiterals(
      SqlNode node, List<SqlNode> literals, boolean isRoot) {
    if (node == null) {
      return;
    }
    if (isRoot && node instanceof SqlOrderBy orderBy) {
      collectNullLiterals(orderBy.query, literals, true);
      return;
    }
    if (isRoot && node instanceof SqlCall withCall
        && withCall.getKind().name().equals("WITH")) {
      for (SqlNode cte : directCteQueries(node)) {
        collectNullLiterals(cte, literals, true);
      }
      List<SqlNode> operands = withCall.getOperandList();
      if (!operands.isEmpty()) {
        collectNullLiterals(operands.get(operands.size() - 1), literals, true);
      }
      return;
    }
    if (isRoot && node instanceof SqlCall setCall && isSetQueryCall(setCall)) {
      for (SqlNode operand : setCall.getOperandList()) {
        collectNullLiterals(operand, literals, true);
      }
      return;
    }
    if (!isRoot && startsLiteralRecoveryScope(node)) {
      return;
    }
    if (node instanceof SqlCall call && call.getKind().name().equals("CAST")
        && !call.getOperandList().isEmpty()
        && call.getOperandList().get(0) instanceof SqlLiteral literal
        && literal.getTypeName() == SqlTypeName.NULL) {
      literals.add(call);
      return;
    }
    if (node instanceof SqlLiteral literal) {
      if (literal.getTypeName() == SqlTypeName.NULL) {
        literals.add(literal);
      }
      return;
    }
    if (node instanceof SqlNodeList list) {
      for (SqlNode item : list) {
        collectNullLiterals(item, literals, false);
      }
      return;
    }
    if (node instanceof SqlCall call) {
      for (SqlNode operand : call.getOperandList()) {
        collectNullLiterals(operand, literals, false);
      }
    }
  }

  private static String trimTrailingSpaces(String value) {
    int end = value.length();
    while (end > 0 && value.charAt(end - 1) == ' ') {
      end--;
    }
    return value.substring(0, end);
  }

  private static String sourceCharacterLiteralValue(SqlLiteral literal) {
    if (literal.getTypeName() != SqlTypeName.CHAR
        && literal.getTypeName() != SqlTypeName.VARCHAR
        && literal.getTypeName() != SqlTypeName.UNKNOWN) {
      return null;
    }
    try {
      return literal.getStringValue();
    } catch (RuntimeException | AssertionError e) {
      // SqlUnknownLiteral may expose a textual carrier while getStringValue
      // still assumes Calcite's NlsString representation. Such a node is not
      // independent character-literal authority; withhold recovery instead
      // of letting a best-effort provenance scan abort query serialization.
      return null;
    }
  }

  private record CharacterLiteralSource(SqlNode node, String value) {}

  private static String dateLiteralValue(RexLiteral literal) {
    if (literal.getTypeName() != SqlTypeName.DATE) {
      return null;
    }
    try {
      DateString value = literal.getValueAs(DateString.class);
      return value == null ? null : value.toString();
    } catch (RuntimeException | AssertionError e) {
      return null;
    }
  }

  private static String timeLiteralValue(RexLiteral literal) {
    if (literal.getTypeName() != SqlTypeName.TIME) {
      return null;
    }
    try {
      TimeString value = literal.getValueAs(TimeString.class);
      if (value == null) {
        return null;
      }
      int precision = literal.getType().getPrecision();
      return precision < 0 ? value.toString() : value.toString(precision);
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

  private static void emitAggregateCall(
      Json out, org.apache.calcite.rel.core.AggregateCall call, SqlCall sourceCall,
      SourcePositionMap sourcePositions) {
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
    if (sourceCall != null) {
      out.comma();
      out.name("sourceSql").value(sourceCall.toString());
      emitExactSourceBinding(out, sourcePositions, sourceCall);
      out.comma();
      out.name("sourceKind").value(sourceCall.getKind().name());
      out.comma();
      out.name("sourceOperator").value(sourceCall.getOperator().getName());
      out.comma();
      out.name("sourceDistinct")
          .value(sourceCall.getFunctionQuantifier() != null
              && sourceCall.getFunctionQuantifier().toString().equalsIgnoreCase("DISTINCT"));
      out.comma();
      out.name("sourceOperands");
      out.beginArray();
      for (int i = 0; i < sourceCall.getOperandList().size(); i++) {
        if (i > 0) {
          out.comma();
        }
        emitSourceNodeProvenance(
            out, sourceCall.getOperandList().get(i), sourcePositions);
      }
      out.endArray();
    }
    out.endObject();
  }

  private static void emitSourceNodeProvenance(
      Json out, SqlNode node, SourcePositionMap sourcePositions) {
    out.beginObject();
    if (node != null) {
      out.name("sourceSql").value(node.toString());
      emitExactSourceBinding(out, sourcePositions, node);
      out.comma();
      out.name("sourceKind").value(node.getKind().name());
      if (node instanceof SqlIdentifier identifier) {
        emitSourceIdentifierMetadata(out, identifier, sourcePositions);
      }
      if (node instanceof SqlCall call) {
        out.comma();
        out.name("sourceOperator").value(call.getOperator().getName());
        out.comma();
        out.name("sourceOperands");
        out.beginArray();
        for (int i = 0; i < call.getOperandList().size(); i++) {
          if (i > 0) {
            out.comma();
          }
          emitSourceNodeProvenance(
              out, call.getOperandList().get(i), sourcePositions);
        }
        out.endArray();
      }
    }
    out.endObject();
  }

  private static void emitSourceIdentifierMetadata(
      Json out, SqlIdentifier identifier, SourcePositionMap sourcePositions) {
    out.comma();
    out.name("sourceIdentifierNames");
    emitIdentifierNames(out, identifier);
    out.comma();
    out.name("sourceIdentifierQuoted");
    emitIdentifierQuoted(out, identifier, sourcePositions);
  }

  private static void emitIdentifierNames(Json out, SqlIdentifier identifier) {
    out.beginArray();
    for (int i = 0; i < identifier.names.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      out.value(identifier.names.get(i));
    }
    out.endArray();
  }

  private static void emitIdentifierQuoted(
      Json out, SqlIdentifier identifier, SourcePositionMap sourcePositions) {
    if (sourcePositions == null) {
      throw new UnsupportedOperationException(
          "source identifier quotedness has no original-statement position map");
    }
    out.beginArray();
    for (int i = 0; i < identifier.names.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      out.value(sourcePositions.sourceIdentifierComponentQuoted(identifier, i));
    }
    out.endArray();
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

  private static void emitIntegerList(Json out, List<Integer> values) {
    out.beginArray();
    for (int i = 0; i < values.size(); i++) {
      if (i > 0) {
        out.comma();
      }
      out.value(values.get(i));
    }
    out.endArray();
  }

  private static List<TableDef> parseCreateTables(String schemaSql) {
    schemaSql = stripSqlComments(schemaSql);
    boolean[] codePositions = schemaCodePositions(schemaSql);
    boolean[] consumedPositions = new boolean[schemaSql.length()];
    List<TableDef> tables = new ArrayList<>();
    Set<String> relationNamespace = new HashSet<>();
    String identifier = "(?:[A-Za-z_][A-Za-z0-9_$]*|\"(?:\"\"|[^\"])+\")";
    rejectSchemaPattern(
        schemaSql,
        codePositions,
        Pattern.compile("(?is)alter\\s+table\\b"),
        "ALTER TABLE schema mutations are not supported; put constraints in CREATE TABLE");
    rejectSchemaPattern(
        schemaSql,
        codePositions,
        Pattern.compile("(?is)create\\s+table\\s+" + identifier + "\\s*\\."),
        "schema-qualified CREATE TABLE names are not supported");
    Pattern tableStartPattern = Pattern.compile(
        "(?is)create\\s+table\\s+(" + identifier + ")\\s*\\(");
    Matcher matcher = tableStartPattern.matcher(schemaSql);
    while (matcher.find()) {
      if (!codePositions[matcher.start()]) {
        continue;
      }
      String tableName = matcher.group(1);
      int bodyStart = matcher.end();
      int bodyEnd = findMatchingParen(schemaSql, bodyStart - 1);
      if (bodyEnd < 0) {
        throw new IllegalArgumentException(
            "unterminated CREATE TABLE column list for " + tableName);
      }
      int trailingClauseStart = skipPostgresSqlWhitespace(schemaSql, bodyEnd + 1);
      if (trailingClauseStart < schemaSql.length()
          && schemaSql.charAt(trailingClauseStart) != ';') {
        int trailingClauseEnd = schemaSql.indexOf(';', trailingClauseStart);
        if (trailingClauseEnd < 0) {
          trailingClauseEnd = schemaSql.length();
        }
        throw new IllegalArgumentException(
            "unsupported trailing CREATE TABLE clause: "
                + trimPostgresSqlWhitespace(
                    schemaSql.substring(trailingClauseStart, trailingClauseEnd)));
      }
      String body = schemaSql.substring(bodyStart, bodyEnd);
      List<ColumnDef> columns = new ArrayList<>();
      Set<String> columnNames = new HashSet<>();
      Set<String> declaredNotNull = new HashSet<>();
      List<List<String>> primaryKeyCandidates = new ArrayList<>();
      List<TableConstraintDef> tableConstraints = new ArrayList<>();
      Set<String> namedTableConstraints = new HashSet<>();
      List<String> explicitIndexNames = new ArrayList<>();
      List<String> tableEntries = splitTopLevelCommas(body);
      boolean emptyTableBody = tableEntries.size() == 1
          && trimPostgresSqlWhitespace(tableEntries.get(0)).isEmpty();
      for (String part : tableEntries) {
        String trimmed = trimPostgresSqlWhitespace(part);
        if (trimmed.isEmpty()) {
          if (emptyTableBody) {
            continue;
          }
          throw new IllegalArgumentException(
              "empty entry in CREATE TABLE column or constraint list for " + tableName);
        }
        if (isTableConstraint(trimmed)) {
          TableConstraintDef constraint = parseTableConstraint(trimmed);
          if (constraint.name != null && !namedTableConstraints.add(constraint.name)) {
            throw new IllegalArgumentException(
                "duplicate named table constraint " + constraint.name + " in " + tableName);
          }
          if (constraint.name != null && constraint.kind.producesIndex) {
            explicitIndexNames.add(constraint.name);
          }
          tableConstraints.add(constraint);
          continue;
        }
        int nameEnd = postgresIdentifierEnd(trimmed, 0);
        if (nameEnd <= 0
            || nameEnd >= trimmed.length()
            || !isPostgresSqlWhitespace(trimmed.charAt(nameEnd))) {
          throw new IllegalArgumentException(
              "invalid PostgreSQL column identifier or missing type: " + trimmed);
        }
        String columnName = canonicalPostgresSchemaIdentifier(trimmed.substring(0, nameEnd));
        if (columnName.isEmpty()) {
          throw new IllegalArgumentException(
              "PostgreSQL column identifiers must not be empty: " + trimmed);
        }
        if (!columnNames.add(columnName)) {
          throw new IllegalArgumentException(
              "duplicate PostgreSQL column identity in table " + tableName + ": " + columnName);
        }
        ColumnConstraintFlags flags = parseColumnConstraintFlags(trimmed);
        if (flags.notNull) {
          declaredNotNull.add(columnName);
        }
        if (flags.primaryKey) {
          primaryKeyCandidates.add(List.of(columnName));
          if (flags.primaryKeyName != null) {
            explicitIndexNames.add(flags.primaryKeyName);
          }
        }
        String declaredType = columnTypeDeclaration(trimmed);
        if (declaredType.isEmpty()) {
          throw new IllegalArgumentException(
              "column declaration is missing its PostgreSQL type: " + trimmed);
        }
        columns.add(ColumnDef.parse(
            columnName,
            declaredType,
            hasExplicitColumnCollation(trimmed)));
      }
      String canonicalTableName = canonicalPostgresSchemaIdentifier(tableName);
      if (!relationNamespace.add(canonicalTableName)) {
        throw new IllegalArgumentException(
            "duplicate PostgreSQL relation identity in schema: " + canonicalTableName);
      }
      for (TableConstraintDef constraint : tableConstraints) {
        for (String constraintColumn : constraint.columns) {
          if (!columnNames.contains(constraintColumn)) {
            throw new IllegalArgumentException(
                constraint.kind.sqlName + " for table " + canonicalTableName
                    + " names unknown column " + constraintColumn);
          }
        }
        if (constraint.kind == TableConstraintKind.PRIMARY_KEY) {
          primaryKeyCandidates.add(constraint.columns);
        }
      }
      for (String explicitIndexName : explicitIndexNames) {
        if (!relationNamespace.add(explicitIndexName)) {
          throw new IllegalArgumentException(
              "PostgreSQL relation namespace collision for explicit index-producing constraint: "
                  + explicitIndexName);
        }
      }
      if (primaryKeyCandidates.size() > 1) {
        throw new IllegalArgumentException(
            "multiple primary-key declarations for table " + canonicalTableName);
      }
      List<String> primaryKey = primaryKeyCandidates.isEmpty()
          ? List.of()
          : primaryKeyCandidates.get(0);
      for (String keyColumn : primaryKey) {
        if (!columnNames.contains(keyColumn)) {
          throw new IllegalArgumentException(
              "primary key for table " + canonicalTableName
                  + " names unknown column " + keyColumn);
        }
        declaredNotNull.add(keyColumn);
      }
      List<String> notNull = new ArrayList<>();
      for (ColumnDef column : columns) {
        if (declaredNotNull.contains(column.name)) {
          notNull.add(column.name);
        }
      }
      List<UniqueConstraintDef> unique = new ArrayList<>();
      List<ForeignKeyDef> foreignKeys = new ArrayList<>();
      List<CheckDef> checks = new ArrayList<>();
      for (TableConstraintDef constraint : tableConstraints) {
        if (constraint.kind == TableConstraintKind.UNIQUE) {
          unique.add(new UniqueConstraintDef(constraint.name, constraint.columns));
        } else if (constraint.kind == TableConstraintKind.FOREIGN_KEY) {
          ForeignKeySpec foreignKey = constraint.foreignKey;
          foreignKeys.add(new ForeignKeyDef(
              constraint.name,
              constraint.columns,
              foreignKey.referencedTable,
              foreignKey.referencedColumns,
              foreignKey.referentialActions));
        } else if (constraint.kind == TableConstraintKind.CHECK) {
          checks.add(new CheckDef(
              constraint.name,
              constraint.checkExpression,
              parseIntegrityPredicate(constraint.checkExpression, columns, "CHECK")));
        }
      }
      tables.add(new TableDef(
          canonicalTableName,
          List.copyOf(columns),
          new TableConstraints(
              notNull,
              primaryKey,
              unique,
              foreignKeys,
              checks,
              List.of())));
      for (int index = matcher.start(); index <= bodyEnd; index++) {
        consumedPositions[index] = true;
      }
      matcher.region(bodyEnd + 1, schemaSql.length());
    }
    List<ParsedUniqueIndex> indexes = parseCreateUniqueIndexes(
        schemaSql, codePositions, consumedPositions);
    Map<String, Integer> tablePositions = new HashMap<>();
    for (int tableIndex = 0; tableIndex < tables.size(); tableIndex++) {
      tablePositions.put(tables.get(tableIndex).name, tableIndex);
    }
    for (ParsedUniqueIndex parsed : indexes) {
      if (!relationNamespace.add(parsed.index.name)) {
        throw new IllegalArgumentException(
            "PostgreSQL relation namespace collision for CREATE UNIQUE INDEX: "
                + parsed.index.name);
      }
      Integer tableIndex = tablePositions.get(parsed.tableName);
      if (tableIndex == null) {
        throw new IllegalArgumentException(
            "CREATE UNIQUE INDEX " + parsed.index.name
                + " names unknown table " + parsed.tableName);
      }
      TableDef table = tables.get(tableIndex);
      UniqueIndexDef index = bindUniqueIndex(parsed.index, table);
      tables.set(tableIndex, new TableDef(
          table.name,
          table.columns,
          table.constraints.withUniqueIndex(index)));
    }
    validateForeignKeys(tables);
    rejectUnconsumedSchemaCode(schemaSql, consumedPositions);
    return tables;
  }

  private static void rejectUnconsumedSchemaCode(
      String schemaSql, boolean[] consumedPositions) {
    for (int index = 0; index < schemaSql.length(); index++) {
      char current = schemaSql.charAt(index);
      if (!consumedPositions[index]
          && !isPostgresSqlWhitespace(current)
          && current != ';') {
        int end = schemaSql.indexOf(';', index);
        if (end < 0) {
          end = schemaSql.length();
        }
        end = Math.min(end, index + 120);
        throw new IllegalArgumentException(
            "unsupported or unconsumed schema statement: "
                + trimPostgresSqlWhitespace(schemaSql.substring(index, end)));
      }
    }
  }

  private static void rejectSchemaPattern(
      String schemaSql, boolean[] codePositions, Pattern pattern, String message) {
    Matcher matcher = pattern.matcher(schemaSql);
    while (matcher.find()) {
      if (codePositions[matcher.start()]) {
        throw new IllegalArgumentException(message);
      }
    }
  }

  /** Marks positions outside SQL quoted tokens in a comment-stripped schema.
   *
   * The CREATE TABLE matcher is intentionally permissive about whitespace and
   * quoted relation identifiers. Checking only the match's keyword start
   * keeps those real identifiers available to the regex while rejecting
   * CREATE TABLE text embedded in string, identifier, bracket, or dollar
   * quotes. Token bodies retain their original width, so positions line up
   * exactly with the original string.
   */
  private static boolean[] schemaCodePositions(String sql) {
    boolean[] code = new boolean[sql.length()];
    for (int index = 0; index < sql.length();) {
      char current = sql.charAt(index);
      if (current == '\'' || current == '"' || current == '`') {
        index = quotedTokenEnd(sql, index, current);
        continue;
      }
      if (current == '[') {
        index = bracketQuotedTokenEnd(sql, index);
        continue;
      }
      if (current == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(sql, index);
        if (delimiterEnd >= 0) {
          String delimiter = sql.substring(index, delimiterEnd);
          int close = sql.indexOf(delimiter, delimiterEnd);
          if (close < 0) {
            throw new IllegalArgumentException("unterminated dollar-quoted token in schema");
          }
          index = close + delimiter.length();
          continue;
        }
      }
      code[index] = true;
      index++;
    }
    return code;
  }

  private static int findMatchingParen(String text, int openIndex) {
    int depth = 0;
    for (int index = openIndex; index < text.length();) {
      char current = text.charAt(index);
      if (current == '\'' || current == '"' || current == '`') {
        index = quotedTokenEnd(text, index, current);
        continue;
      }
      if (current == '[') {
        index = bracketQuotedTokenEnd(text, index);
        continue;
      }
      if (current == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(text, index);
        if (delimiterEnd >= 0) {
          String delimiter = text.substring(index, delimiterEnd);
          int close = text.indexOf(delimiter, delimiterEnd);
          if (close < 0) {
            throw new IllegalArgumentException("unterminated dollar-quoted token in schema");
          }
          index = close + delimiter.length();
          continue;
        }
      }
      if (current == '(') {
        depth++;
      } else if (current == ')') {
        depth--;
        if (depth == 0) {
          return index;
        }
        if (depth < 0) {
          throw new IllegalArgumentException("unbalanced closing parenthesis in schema");
        }
      }
      index++;
    }
    return -1;
  }

  private static List<String> splitTopLevelCommas(String text) {
    List<String> parts = new ArrayList<>();
    int depth = 0;
    int start = 0;
    for (int index = 0; index < text.length();) {
      char current = text.charAt(index);
      if (current == '\'' || current == '"' || current == '`') {
        index = quotedTokenEnd(text, index, current);
        continue;
      }
      if (current == '[') {
        index = bracketQuotedTokenEnd(text, index);
        continue;
      }
      if (current == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(text, index);
        if (delimiterEnd >= 0) {
          String delimiter = text.substring(index, delimiterEnd);
          int close = text.indexOf(delimiter, delimiterEnd);
          if (close < 0) {
            throw new IllegalArgumentException("unterminated dollar-quoted token in schema");
          }
          index = close + delimiter.length();
          continue;
        }
      }
      if (current == '(') {
        depth++;
      } else if (current == ')') {
        depth--;
        if (depth < 0) {
          throw new IllegalArgumentException(
              "unbalanced closing parenthesis in CREATE TABLE column list");
        }
      } else if (current == ',' && depth == 0) {
        parts.add(text.substring(start, index));
        start = index + 1;
      }
      index++;
    }
    if (depth != 0) {
      throw new IllegalArgumentException(
          "unterminated parenthesized expression in CREATE TABLE column list");
    }
    parts.add(text.substring(start));
    return parts;
  }

  private static boolean isTableConstraint(String text) {
    int start = skipPostgresSqlWhitespace(text, 0);
    int end = bareWordEnd(text, start);
    if (end <= start) {
      return false;
    }
    return switch (text.substring(start, end).toUpperCase(Locale.ROOT)) {
      case "PRIMARY", "FOREIGN", "UNIQUE", "KEY", "INDEX", "FULLTEXT", "SPATIAL",
          "CONSTRAINT", "CHECK", "EXCLUDE" -> true;
      default -> false;
    };
  }

  /** Parses the complete supported table-constraint grammar. */
  private static TableConstraintDef parseTableConstraint(String declaration) {
    int index = skipPostgresSqlWhitespace(declaration, 0);
    String constraintName = null;
    if (matchesKeywordAt(declaration, index, "CONSTRAINT")) {
      index = skipPostgresSqlWhitespace(declaration, index + "CONSTRAINT".length());
      int nameEnd = postgresIdentifierEnd(declaration, index);
      if (nameEnd <= index) {
        throw new IllegalArgumentException(
            "named table constraint is missing its PostgreSQL identifier: " + declaration);
      }
      constraintName =
          canonicalPostgresSchemaIdentifier(declaration.substring(index, nameEnd));
      if (constraintName.isEmpty()) {
        throw new IllegalArgumentException(
            "named table constraint has an empty PostgreSQL identifier: " + declaration);
      }
      index = skipPostgresSqlWhitespace(declaration, nameEnd);
    }
    TableConstraintKind kind;
    if (matchesKeywordAt(declaration, index, "PRIMARY")) {
      index = skipPostgresSqlWhitespace(declaration, index + "PRIMARY".length());
      if (!matchesKeywordAt(declaration, index, "KEY")) {
        throw new IllegalArgumentException("malformed PRIMARY KEY declaration: " + declaration);
      }
      index = skipPostgresSqlWhitespace(declaration, index + "KEY".length());
      kind = TableConstraintKind.PRIMARY_KEY;
    } else if (matchesKeywordAt(declaration, index, "UNIQUE")) {
      index = skipPostgresSqlWhitespace(declaration, index + "UNIQUE".length());
      kind = TableConstraintKind.UNIQUE;
    } else if (matchesKeywordAt(declaration, index, "FOREIGN")) {
      index = skipPostgresSqlWhitespace(declaration, index + "FOREIGN".length());
      if (!matchesKeywordAt(declaration, index, "KEY")) {
        throw new IllegalArgumentException("malformed FOREIGN KEY declaration: " + declaration);
      }
      index = skipPostgresSqlWhitespace(declaration, index + "KEY".length());
      kind = TableConstraintKind.FOREIGN_KEY;
    } else if (matchesKeywordAt(declaration, index, "CHECK")) {
      index = skipPostgresSqlWhitespace(declaration, index + "CHECK".length());
      kind = TableConstraintKind.CHECK;
    } else {
      throw new IllegalArgumentException(
          "unsupported table constraint; expected PRIMARY KEY, UNIQUE, FOREIGN KEY, or CHECK: "
              + declaration);
    }
    if (kind == TableConstraintKind.CHECK) {
      if (index >= declaration.length() || declaration.charAt(index) != '(') {
        throw new IllegalArgumentException(
            "CHECK is missing its parenthesized expression: " + declaration);
      }
      int close = findMatchingParen(declaration, index);
      if (close < 0) {
        throw new IllegalArgumentException("unterminated CHECK expression: " + declaration);
      }
      String expression = trimPostgresSqlWhitespace(declaration.substring(index + 1, close));
      if (expression.isEmpty()) {
        throw new IllegalArgumentException("CHECK expression must not be empty");
      }
      if (!trimPostgresSqlWhitespace(declaration.substring(close + 1)).isEmpty()) {
        throw new IllegalArgumentException(
            "unsupported trailing CHECK syntax: "
                + trimPostgresSqlWhitespace(declaration.substring(close + 1)));
      }
      return new TableConstraintDef(
          kind, constraintName, List.of(), null, expression);
    }
    if (index >= declaration.length() || declaration.charAt(index) != '(') {
      throw new IllegalArgumentException(
          kind.sqlName + " is missing its parenthesized column list: " + declaration);
    }
    int close = findMatchingParen(declaration, index);
    if (close < 0) {
      throw new IllegalArgumentException(
          "unterminated " + kind.sqlName + " column list: " + declaration);
    }
    List<String> columns = parseConstraintColumns(
        declaration.substring(index + 1, close), kind.sqlName);
    int tailStart = skipPostgresSqlWhitespace(declaration, close + 1);
    if (kind != TableConstraintKind.FOREIGN_KEY) {
      if (tailStart != declaration.length()) {
        throw new IllegalArgumentException(
            "unsupported trailing " + kind.sqlName + " syntax: "
                + trimPostgresSqlWhitespace(declaration.substring(tailStart)));
      }
      return new TableConstraintDef(kind, constraintName, columns, null, null);
    }

    if (!matchesKeywordAt(declaration, tailStart, "REFERENCES")) {
      throw new IllegalArgumentException(
          "FOREIGN KEY is missing REFERENCES: " + declaration);
    }
    int referencedTableStart = skipPostgresSqlWhitespace(
        declaration, tailStart + "REFERENCES".length());
    int referencedTableEnd = postgresIdentifierEnd(declaration, referencedTableStart);
    if (referencedTableEnd <= referencedTableStart) {
      throw new IllegalArgumentException(
          "FOREIGN KEY REFERENCES is missing its table: " + declaration);
    }
    String referencedTable = canonicalPostgresSchemaIdentifier(
        declaration.substring(referencedTableStart, referencedTableEnd));
    int referencedColumnsStart = skipPostgresSqlWhitespace(declaration, referencedTableEnd);
    if (referencedColumnsStart >= declaration.length()
        || declaration.charAt(referencedColumnsStart) != '(') {
      throw new IllegalArgumentException(
          "FOREIGN KEY REFERENCES is missing its parenthesized column list: " + declaration);
    }
    int referencedColumnsEnd = findMatchingParen(declaration, referencedColumnsStart);
    if (referencedColumnsEnd < 0) {
      throw new IllegalArgumentException(
          "unterminated FOREIGN KEY referenced column list: " + declaration);
    }
    List<String> referencedColumns = parseConstraintColumns(
        declaration.substring(referencedColumnsStart + 1, referencedColumnsEnd),
        "FOREIGN KEY referenced key");
    if (columns.size() != referencedColumns.size()) {
      throw new IllegalArgumentException(
          "FOREIGN KEY source and referenced column lists have different arity");
    }
    String actions = parseForeignKeyTail(
        declaration.substring(referencedColumnsEnd + 1), declaration);
    return new TableConstraintDef(
        kind,
        constraintName,
        columns,
        new ForeignKeySpec(referencedTable, referencedColumns, actions),
        null);
  }

  private static List<String> parseConstraintColumns(String body, String kind) {
    List<String> columns = new ArrayList<>();
    Set<String> names = new HashSet<>();
    for (String rawColumn : splitTopLevelCommas(body)) {
      String token = trimPostgresSqlWhitespace(rawColumn);
      int end = postgresIdentifierEnd(token, 0);
      if (token.isEmpty() || end != token.length()) {
        throw new IllegalArgumentException(
            kind + " entries must be PostgreSQL column identifiers: "
                + trimPostgresSqlWhitespace(rawColumn));
      }
      String name = canonicalPostgresSchemaIdentifier(token);
      if (name.isEmpty()) {
        throw new IllegalArgumentException(
            kind + " entries must not be empty PostgreSQL identifiers");
      }
      if (!names.add(name)) {
        throw new IllegalArgumentException("duplicate " + kind + " column: " + name);
      }
      columns.add(name);
    }
    if (columns.isEmpty()) {
      throw new IllegalArgumentException(kind + " column list must not be empty");
    }
    return List.copyOf(columns);
  }

  private static String parseForeignKeyTail(String rawTail, String declaration) {
    String tail = trimPostgresSqlWhitespace(rawTail);
    int index = 0;
    if (matchesKeywordAt(tail, index, "MATCH")) {
      int matchStart = skipPostgresSqlWhitespace(tail, index + "MATCH".length());
      if (!matchesKeywordAt(tail, matchStart, "SIMPLE")) {
        throw new IllegalArgumentException(
            "only PostgreSQL MATCH SIMPLE foreign keys are supported: " + declaration);
      }
      index = skipPostgresSqlWhitespace(tail, matchStart + "SIMPLE".length());
    }
    List<String> actions = new ArrayList<>();
    Set<String> events = new HashSet<>();
    while (index < tail.length()) {
      if (!matchesKeywordAt(tail, index, "ON")) {
        throw new IllegalArgumentException(
            "unsupported trailing FOREIGN KEY syntax: " + tail.substring(index));
      }
      int eventStart = skipPostgresSqlWhitespace(tail, index + "ON".length());
      String event;
      if (matchesKeywordAt(tail, eventStart, "DELETE")) {
        event = "DELETE";
      } else if (matchesKeywordAt(tail, eventStart, "UPDATE")) {
        event = "UPDATE";
      } else {
        throw new IllegalArgumentException(
            "FOREIGN KEY ON must name DELETE or UPDATE: " + declaration);
      }
      if (!events.add(event)) {
        throw new IllegalArgumentException(
            "duplicate FOREIGN KEY ON " + event + " action: " + declaration);
      }
      int actionStart = skipPostgresSqlWhitespace(tail, eventStart + event.length());
      String action;
      int actionEnd;
      if (matchesKeywordAt(tail, actionStart, "CASCADE")) {
        action = "CASCADE";
        actionEnd = actionStart + "CASCADE".length();
      } else if (matchesKeywordAt(tail, actionStart, "RESTRICT")) {
        action = "RESTRICT";
        actionEnd = actionStart + "RESTRICT".length();
      } else if (matchesKeywordAt(tail, actionStart, "SET")) {
        int nullStart = skipPostgresSqlWhitespace(tail, actionStart + "SET".length());
        if (!matchesKeywordAt(tail, nullStart, "NULL")) {
          throw new IllegalArgumentException(
              "only SET NULL is supported for FOREIGN KEY actions: " + declaration);
        }
        action = "SET NULL";
        actionEnd = nullStart + "NULL".length();
      } else if (matchesKeywordAt(tail, actionStart, "NO")) {
        int actionKeyword = skipPostgresSqlWhitespace(tail, actionStart + "NO".length());
        if (!matchesKeywordAt(tail, actionKeyword, "ACTION")) {
          throw new IllegalArgumentException(
              "malformed FOREIGN KEY NO ACTION clause: " + declaration);
        }
        action = "NO ACTION";
        actionEnd = actionKeyword + "ACTION".length();
      } else {
        throw new IllegalArgumentException(
            "unsupported FOREIGN KEY referential action: " + tail.substring(actionStart));
      }
      actions.add("ON " + event + " " + action);
      index = skipPostgresSqlWhitespace(tail, actionEnd);
    }
    return actions.isEmpty() ? null : String.join(" ", actions);
  }

  private static List<ParsedUniqueIndex> parseCreateUniqueIndexes(
      String schemaSql, boolean[] codePositions, boolean[] consumedPositions) {
    String identifier = "(?:[A-Za-z_][A-Za-z0-9_$]*|\"(?:\"\"|[^\"])+\")";
    Pattern startPattern = Pattern.compile(
        "(?is)create\\s+unique\\s+index\\s+(" + identifier + ")\\s+on\\s+"
            + "((?:" + identifier + "\\s*\\.\\s*)?" + identifier + ")\\s*"
            + "(?:using\\s+([A-Za-z_][A-Za-z0-9_$]*)\\s*)?\\(");
    Matcher matcher = startPattern.matcher(schemaSql);
    List<ParsedUniqueIndex> indexes = new ArrayList<>();
    while (matcher.find()) {
      if (!codePositions[matcher.start()]) {
        continue;
      }
      String method = matcher.group(3);
      if (method != null && !method.equalsIgnoreCase("btree")) {
        throw new IllegalArgumentException(
            "CREATE UNIQUE INDEX supports only PostgreSQL btree logical uniqueness; found "
                + method);
      }
      int termsEnd = findMatchingParen(schemaSql, matcher.end() - 1);
      if (termsEnd < 0) {
        throw new IllegalArgumentException(
            "unterminated CREATE UNIQUE INDEX term list for " + matcher.group(1));
      }
      int statementEnd = nextSchemaStatementEnd(schemaSql, termsEnd + 1, codePositions);
      String tail = trimPostgresSqlWhitespace(schemaSql.substring(termsEnd + 1, statementEnd));
      String predicateSql = null;
      if (!tail.isEmpty()) {
        if (!matchesKeywordAt(tail, 0, "WHERE")) {
          throw new IllegalArgumentException(
              "unsupported trailing CREATE UNIQUE INDEX syntax: " + tail);
        }
        predicateSql = trimPostgresSqlWhitespace(tail.substring("WHERE".length()));
        if (predicateSql.isEmpty()) {
          throw new IllegalArgumentException("CREATE UNIQUE INDEX WHERE predicate is empty");
        }
      }
      List<String> rawTerms = new ArrayList<>();
      for (String rawTerm : splitTopLevelCommas(
          schemaSql.substring(matcher.end(), termsEnd))) {
        String term = trimPostgresSqlWhitespace(rawTerm);
        if (term.isEmpty()) {
          throw new IllegalArgumentException(
              "CREATE UNIQUE INDEX contains an empty term: " + matcher.group(1));
        }
        rawTerms.add(term);
      }
      if (rawTerms.isEmpty()) {
        throw new IllegalArgumentException(
            "CREATE UNIQUE INDEX term list must not be empty: " + matcher.group(1));
      }
      String indexName = canonicalPostgresSchemaIdentifier(matcher.group(1));
      String tableName = canonicalIndexTableReference(matcher.group(2));
      indexes.add(new ParsedUniqueIndex(
          tableName,
          new UnboundUniqueIndexDef(
              indexName, List.copyOf(rawTerms), predicateSql)));
      for (int position = matcher.start(); position < statementEnd; position++) {
        consumedPositions[position] = true;
      }
      matcher.region(
          statementEnd < schemaSql.length() ? statementEnd + 1 : statementEnd,
          schemaSql.length());
    }
    return List.copyOf(indexes);
  }

  private static int nextSchemaStatementEnd(
      String schemaSql, int start, boolean[] codePositions) {
    for (int index = start; index < schemaSql.length(); index++) {
      if (schemaSql.charAt(index) == ';' && codePositions[index]) {
        return index;
      }
    }
    return schemaSql.length();
  }

  private static String canonicalIndexTableReference(String rawReference) {
    String reference = trimPostgresSqlWhitespace(rawReference);
    int firstEnd = postgresIdentifierEnd(reference, 0);
    if (firstEnd <= 0) {
      throw new IllegalArgumentException(
          "CREATE UNIQUE INDEX is missing its PostgreSQL table identifier");
    }
    String first = canonicalPostgresSchemaIdentifier(reference.substring(0, firstEnd));
    int index = skipPostgresSqlWhitespace(reference, firstEnd);
    if (index == reference.length()) {
      return first;
    }
    if (reference.charAt(index) != '.') {
      throw new IllegalArgumentException(
          "malformed CREATE UNIQUE INDEX table reference: " + rawReference);
    }
    int secondStart = skipPostgresSqlWhitespace(reference, index + 1);
    int secondEnd = postgresIdentifierEnd(reference, secondStart);
    if (secondEnd <= secondStart
        || skipPostgresSqlWhitespace(reference, secondEnd) != reference.length()) {
      throw new IllegalArgumentException(
          "malformed CREATE UNIQUE INDEX qualified table reference: " + rawReference);
    }
    if (!first.equals("public")) {
      throw new IllegalArgumentException(
          "only the PostgreSQL public schema is supported for CREATE UNIQUE INDEX; found "
              + first);
    }
    return canonicalPostgresSchemaIdentifier(reference.substring(secondStart, secondEnd));
  }

  private static UniqueIndexDef bindUniqueIndex(
      UnboundUniqueIndexDef unbound, TableDef table) {
    List<UniqueIndexTermDef> terms = new ArrayList<>();
    for (String rawTerm : unbound.rawTerms) {
      terms.add(parseUniqueIndexTerm(rawTerm, table.columns));
    }
    IntegrityPredicateDef predicate = unbound.predicateSql == null
        ? null
        : parseIntegrityPredicate(
            unbound.predicateSql, table.columns, "CREATE UNIQUE INDEX predicate");
    return new UniqueIndexDef(
        unbound.name,
        List.copyOf(terms),
        predicate,
        unbound.predicateSql);
  }

  private static UniqueIndexTermDef parseUniqueIndexTerm(
      String rawTerm, List<ColumnDef> columns) {
    IntegrityExpressionParser parser = new IntegrityExpressionParser(rawTerm, columns);
    IntegrityValueDef expression = parser.parseValue();
    String operatorClass = null;
    String direction = "asc";
    String nulls = null;
    if (parser.matchKeyword("varchar_pattern_ops")) {
      operatorClass = "varchar_pattern_ops";
    } else if (parser.peekIdentifierEndingWith("_ops")) {
      throw parser.failure(
          "unsupported PostgreSQL unique-index operator class " + parser.peekRaw());
    }
    if (operatorClass != null && !varcharPatternOpsAccepts(expression.sqlType())) {
      throw parser.failure(
          "varchar_pattern_ops does not accept PostgreSQL type " + expression.sqlType());
    }
    if (parser.matchKeyword("ASC")) {
      direction = "asc";
    } else if (parser.matchKeyword("DESC")) {
      direction = "desc";
    }
    if (parser.matchKeyword("NULLS")) {
      if (parser.matchKeyword("FIRST")) {
        nulls = "first";
      } else if (parser.matchKeyword("LAST")) {
        nulls = "last";
      } else {
        throw parser.failure("NULLS must be followed by FIRST or LAST");
      }
    }
    parser.requireEnd("unique-index term");
    return new UniqueIndexTermDef(
        expression,
        trimPostgresSqlWhitespace(rawTerm),
        direction,
        nulls,
        operatorClass);
  }

  private static IntegrityPredicateDef parseIntegrityPredicate(
      String sql, List<ColumnDef> columns, String context) {
    try {
      IntegrityExpressionParser parser = new IntegrityExpressionParser(sql, columns);
      IntegrityPredicateDef predicate = parser.parsePredicate();
      parser.requireEnd(context);
      return predicate;
    } catch (IntegrityParseFailure failure) {
      throw new IllegalArgumentException(
          "unsupported or malformed " + context + ": " + failure.getMessage(), failure);
    }
  }

  /**
   * Closed parser for the PostgreSQL integrity-expression fragment present in
   * the frozen benchmark. The raw SQL remains the wire authority; this parser
   * exists to make the Java boundary reject unknown columns, incompatible
   * equality operands, and syntax that the Rust lowering cannot model.
   */
  private static final class IntegrityExpressionParser {
    private final List<IntegrityToken> tokens;
    private final Map<String, ColumnDef> columns;
    private int position;

    IntegrityExpressionParser(String sql, List<ColumnDef> columns) {
      this.tokens = tokenizeIntegrityExpression(sql);
      this.columns = columnDefsByName(columns);
    }

    IntegrityPredicateDef parsePredicate() {
      return parseOrPredicate();
    }

    private IntegrityPredicateDef parseOrPredicate() {
      IntegrityPredicateDef predicate = parseAndPredicate();
      while (matchKeyword("OR")) {
        predicate = new IntegrityOrDef(predicate, parseAndPredicate());
      }
      return predicate;
    }

    private IntegrityPredicateDef parseAndPredicate() {
      IntegrityPredicateDef predicate = parseNotPredicate();
      while (matchKeyword("AND")) {
        predicate = new IntegrityAndDef(predicate, parseNotPredicate());
      }
      return predicate;
    }

    private IntegrityPredicateDef parseNotPredicate() {
      if (matchKeyword("NOT")) {
        return new IntegrityNotDef(parseNotPredicate());
      }
      return parsePrimaryPredicate();
    }

    private IntegrityPredicateDef parsePrimaryPredicate() {
      if (peekSymbol("(")) {
        int saved = position;
        position++;
        try {
          IntegrityPredicateDef nested = parseOrPredicate();
          requireSymbol(")", "parenthesized predicate");
          return nested;
        } catch (IntegrityParseFailure failure) {
          position = saved;
        }
      }
      IntegrityValueDef left = parseValue();
      if (matchKeyword("IS")) {
        if (matchKeyword("NOT")) {
          if (!matchKeyword("NULL")) {
            throw failure("only IS NOT NULL is supported in integrity predicates");
          }
          return new IntegrityIsNotNullDef(left);
        }
        if (matchKeyword("NULL")) {
          return new IntegrityIsNullDef(left);
        }
        if (matchKeyword("TRUE")) {
          requireBoolean(left, "IS TRUE operand");
          return new IntegrityTruthDef(left);
        }
        throw failure("only IS NULL, IS NOT NULL, and IS TRUE are supported");
      }
      String comparison = null;
      if (matchSymbol("=")) {
        comparison = "equal";
      } else if (matchSymbol("<>")) {
        comparison = "not_equal";
      }
      if (comparison != null) {
        if (matchKeyword("ANY")) {
          requireSymbol("(", "ANY");
          if (!matchKeyword("ARRAY")) {
            throw failure("ANY must use an explicit ARRAY literal");
          }
          requireSymbol("[", "ANY ARRAY");
          List<IntegrityValueDef> values = new ArrayList<>();
          if (peekSymbol("]")) {
            throw failure("ANY ARRAY must not be empty");
          }
          do {
            IntegrityValueDef value = parseValue();
            requireComparable(left, value, "ANY equality");
            values.add(value);
          } while (matchSymbol(","));
          requireSymbol("]", "ANY ARRAY");
          requireSymbol(")", "ANY");
          return new IntegrityAnyDef(comparison, left, values);
        }
        IntegrityValueDef right = parseValue();
        requireComparable(left, right, "integrity comparison");
        return new IntegrityComparisonDef(comparison, left, right);
      }
      requireBoolean(left, "bare integrity predicate");
      return new IntegrityTruthDef(left);
    }

    IntegrityValueDef parseValue() {
      IntegrityValueDef value = parseValueAtom();
      while (matchSymbol("::")) {
        IntegrityToken type = peek();
        if (type.kind != IntegrityTokenKind.IDENTIFIER || type.quoted) {
          throw failure("PostgreSQL cast target must be an unquoted type name");
        }
        position++;
        String target = switch (type.value.toLowerCase(Locale.ROOT)) {
          case "text" -> "text";
          case "integer", "int", "int4" -> "integer";
          default -> throw failure(
              "unsupported integrity-expression cast target " + type.raw);
        };
        validateIntegrityCast(value, target);
        value = new IntegrityCastDef(value, target);
      }
      return value;
    }

    private IntegrityValueDef parseValueAtom() {
      if (matchSymbol("(")) {
        IntegrityValueDef nested = parseValue();
        requireSymbol(")", "parenthesized value expression");
        return nested;
      }
      IntegrityToken token = peek();
      if (token.kind == IntegrityTokenKind.STRING) {
        position++;
        return new IntegrityLiteralDef(token.value, "unknown");
      }
      if (token.kind == IntegrityTokenKind.INTEGER) {
        position++;
        try {
          Integer.parseInt(token.value);
        } catch (NumberFormatException error) {
          throw failure("integer literal is outside PostgreSQL integer range: " + token.raw);
        }
        return new IntegrityLiteralDef(token.value, "integer");
      }
      if (matchKeyword("TRUE")) {
        return new IntegrityLiteralDef("true", "boolean");
      }
      if (matchKeyword("FALSE")) {
        return new IntegrityLiteralDef("false", "boolean");
      }
      if (matchKeyword("NULL")) {
        return new IntegrityLiteralDef("null", "null");
      }
      if (token.kind != IntegrityTokenKind.IDENTIFIER) {
        throw failure("expected a supported integrity value expression, found " + token.raw);
      }
      if (!token.quoted && token.value.equalsIgnoreCase("lower")
          && peekSymbol(1, "(")) {
        position += 2;
        IntegrityValueDef argument = parseValue();
        requireSymbol(")", "lower");
        if (!isIntegrityStringType(argument.sqlType())
            && !argument.sqlType().equals("unknown")) {
          throw failure("lower requires a PostgreSQL string operand");
        }
        return new IntegrityLowerDef(argument);
      }
      if (!token.quoted && token.value.equalsIgnoreCase("coalesce")
          && peekSymbol(1, "(")) {
        position += 2;
        List<IntegrityValueDef> arguments = new ArrayList<>();
        arguments.add(parseValue());
        if (!matchSymbol(",")) {
          throw failure("coalesce requires at least two arguments");
        }
        do {
          arguments.add(parseValue());
        } while (matchSymbol(","));
        requireSymbol(")", "coalesce");
        String commonType = integrityCommonType(arguments);
        return new IntegrityCoalesceDef(arguments, commonType);
      }
      position++;
      String columnName = token.quoted
          ? token.value
          : token.value.toLowerCase(Locale.ROOT);
      ColumnDef column = columns.get(columnName);
      if (column == null) {
        throw failure("unknown integrity-expression column " + token.raw);
      }
      return new IntegrityColumnDef(column.name, integritySqlType(column));
    }

    private String integrityCommonType(List<IntegrityValueDef> arguments) {
      String common = "null";
      for (IntegrityValueDef argument : arguments) {
        String candidate = argument.sqlType();
        if (candidate.equals("null")) {
          continue;
        }
        if (common.equals("null") || common.equals("unknown")) {
          common = candidate;
          continue;
        }
        if (candidate.equals("unknown")) {
          continue;
        }
        if (!integrityTypesComparable(common, candidate)) {
          throw failure(
              "coalesce arguments have incompatible PostgreSQL types "
                  + common + " and " + candidate);
        }
        if (isIntegrityStringType(common) && isIntegrityStringType(candidate)
            && !common.equals(candidate)) {
          common = postgresIntegrityCommonStringType(common, candidate);
        } else if (isIntegrityNumericType(common) && isIntegrityNumericType(candidate)) {
          common = widerIntegrityNumericType(common, candidate);
        }
      }
      return common.equals("null") ? "unknown" : common;
    }

    private void validateIntegrityCast(IntegrityValueDef expression, String target) {
      String source = expression.sqlType();
      if (target.equals("text")) {
        if (!isIntegrityStringType(source) && !source.equals("unknown")) {
          throw failure("the frozen integrity grammar casts only string values to text");
        }
        return;
      }
      if (!source.equals("unknown") && !isIntegrityIntegerType(source)) {
        throw failure("the frozen integrity grammar casts only integer-like values to integer");
      }
      if (expression instanceof IntegrityLiteralDef literal && source.equals("unknown")) {
        try {
          Integer.parseInt(literal.raw());
        } catch (NumberFormatException error) {
          throw failure(
              "string literal cannot be evaluated as PostgreSQL integer: " + literal.raw());
        }
      }
    }

    private void requireComparable(
        IntegrityValueDef left, IntegrityValueDef right, String context) {
      if (!integrityTypesComparable(left.sqlType(), right.sqlType())) {
        throw failure(
            context + " has incompatible PostgreSQL types "
                + left.sqlType() + " and " + right.sqlType());
      }
    }

    private void requireBoolean(IntegrityValueDef expression, String context) {
      if (!expression.sqlType().equals("boolean")) {
        throw failure(context + " must have PostgreSQL boolean type, found "
            + expression.sqlType());
      }
    }

    boolean matchKeyword(String keyword) {
      IntegrityToken token = peek();
      if (token.kind == IntegrityTokenKind.IDENTIFIER
          && !token.quoted
          && token.value.equalsIgnoreCase(keyword)) {
        position++;
        return true;
      }
      return false;
    }

    boolean peekIdentifierEndingWith(String suffix) {
      IntegrityToken token = peek();
      return token.kind == IntegrityTokenKind.IDENTIFIER
          && !token.quoted
          && token.value.toLowerCase(Locale.ROOT).endsWith(suffix.toLowerCase(Locale.ROOT));
    }

    String peekRaw() {
      return peek().raw;
    }

    private boolean matchSymbol(String symbol) {
      if (peekSymbol(symbol)) {
        position++;
        return true;
      }
      return false;
    }

    private boolean peekSymbol(String symbol) {
      return peekSymbol(0, symbol);
    }

    private boolean peekSymbol(int lookahead, String symbol) {
      int index = Math.min(position + lookahead, tokens.size() - 1);
      IntegrityToken token = tokens.get(index);
      return token.kind == IntegrityTokenKind.SYMBOL && token.value.equals(symbol);
    }

    private void requireSymbol(String symbol, String context) {
      if (!matchSymbol(symbol)) {
        throw failure(context + " is missing " + symbol + "; found " + peek().raw);
      }
    }

    void requireEnd(String context) {
      if (peek().kind != IntegrityTokenKind.END) {
        throw failure("unsupported trailing " + context + " syntax at " + peek().raw);
      }
    }

    IntegrityParseFailure failure(String message) {
      return new IntegrityParseFailure(message);
    }

    private IntegrityToken peek() {
      return tokens.get(position);
    }
  }

  private static List<IntegrityToken> tokenizeIntegrityExpression(String sql) {
    List<IntegrityToken> tokens = new ArrayList<>();
    for (int index = 0; index < sql.length();) {
      char current = sql.charAt(index);
      if (isPostgresSqlWhitespace(current)) {
        index++;
        continue;
      }
      if (current == '"') {
        int end = quotedTokenEnd(sql, index, '"');
        String raw = sql.substring(index, end);
        tokens.add(new IntegrityToken(
            IntegrityTokenKind.IDENTIFIER,
            raw,
            canonicalPostgresSchemaIdentifier(raw),
            true));
        index = end;
        continue;
      }
      if (current == '\'') {
        int end = index + 1;
        StringBuilder value = new StringBuilder();
        boolean closed = false;
        while (end < sql.length()) {
          char character = sql.charAt(end);
          if (character == '\'') {
            if (end + 1 < sql.length() && sql.charAt(end + 1) == '\'') {
              value.append('\'');
              end += 2;
              continue;
            }
            end++;
            closed = true;
            break;
          }
          value.append(character);
          end++;
        }
        if (!closed) {
          throw new IntegrityParseFailure("unterminated PostgreSQL string literal");
        }
        tokens.add(new IntegrityToken(
            IntegrityTokenKind.STRING,
            sql.substring(index, end),
            value.toString(),
            false));
        index = end;
        continue;
      }
      if (Character.isDigit(current)
          || (current == '-' && index + 1 < sql.length()
              && Character.isDigit(sql.charAt(index + 1)))) {
        int end = current == '-' ? index + 2 : index + 1;
        while (end < sql.length() && Character.isDigit(sql.charAt(end))) {
          end++;
        }
        String raw = sql.substring(index, end);
        tokens.add(new IntegrityToken(
            IntegrityTokenKind.INTEGER, raw, raw, false));
        index = end;
        continue;
      }
      if (isBareIdentifierStart(current)) {
        int end = index + 1;
        while (end < sql.length() && isBareIdentifierPart(sql.charAt(end))) {
          end++;
        }
        String raw = sql.substring(index, end);
        tokens.add(new IntegrityToken(
            IntegrityTokenKind.IDENTIFIER,
            raw,
            raw.toLowerCase(Locale.ROOT),
            false));
        index = end;
        continue;
      }
      String symbol = null;
      if (index + 1 < sql.length()) {
        String pair = sql.substring(index, index + 2);
        if (pair.equals("::") || pair.equals("<>")) {
          symbol = pair;
        }
      }
      if (symbol == null && "()[],=".indexOf(current) >= 0) {
        symbol = Character.toString(current);
      }
      if (symbol == null) {
        throw new IntegrityParseFailure(
            "unsupported integrity-expression token " + current);
      }
      tokens.add(new IntegrityToken(
          IntegrityTokenKind.SYMBOL, symbol, symbol, false));
      index += symbol.length();
    }
    tokens.add(new IntegrityToken(IntegrityTokenKind.END, "end of expression", "", false));
    return List.copyOf(tokens);
  }

  private static boolean integrityTypesComparable(String left, String right) {
    if (left.equals("unknown") || right.equals("unknown")
        || left.equals("null") || right.equals("null")) {
      return true;
    }
    return left.equals(right)
        || isIntegrityStringType(left) && isIntegrityStringType(right)
        || isIntegrityNumericType(left) && isIntegrityNumericType(right);
  }

  private static boolean isIntegrityNumericType(String type) {
    return isIntegrityIntegerType(type)
        || type.equals("float") || type.equals("double") || type.equals("decimal");
  }

  private static String widerIntegrityNumericType(String left, String right) {
    List<String> precedence = List.of("integer", "bigInt", "decimal", "float", "double");
    return precedence.indexOf(left) >= precedence.indexOf(right) ? left : right;
  }

  private enum IntegrityTokenKind {
    IDENTIFIER,
    STRING,
    INTEGER,
    SYMBOL,
    END
  }

  private record IntegrityToken(
      IntegrityTokenKind kind, String raw, String value, boolean quoted) {}

  private static final class IntegrityParseFailure extends IllegalArgumentException {
    IntegrityParseFailure(String message) {
      super(message);
    }
  }

  private static void validateForeignKeys(List<TableDef> tables) {
    Map<String, TableDef> byName = new HashMap<>();
    for (TableDef table : tables) {
      byName.put(table.name, table);
    }
    for (TableDef table : tables) {
      Map<String, ColumnDef> sourceColumns = columnDefsByName(table.columns);
      for (ForeignKeyDef foreignKey : table.constraints.foreignKeys) {
        TableDef referenced = byName.get(foreignKey.referencedTable);
        if (referenced == null) {
          throw new IllegalArgumentException(
              "FOREIGN KEY on table " + table.name + " references unknown table "
                  + foreignKey.referencedTable);
        }
        Map<String, ColumnDef> referencedColumns = columnDefsByName(referenced.columns);
        boolean referencedKey = foreignKey.referencedColumns.equals(
            referenced.constraints.primaryKey);
        for (UniqueConstraintDef unique : referenced.constraints.unique) {
          referencedKey |= foreignKey.referencedColumns.equals(unique.columns);
        }
        for (UniqueIndexDef uniqueIndex : referenced.constraints.uniqueIndexes) {
          if (uniqueIndex.predicate == null) {
            List<String> simpleColumns = new ArrayList<>();
            boolean simple = true;
            for (UniqueIndexTermDef term : uniqueIndex.terms) {
              if (term.expression instanceof IntegrityColumnDef column
                  && term.operatorClass == null) {
                simpleColumns.add(column.name);
              } else {
                simple = false;
                break;
              }
            }
            referencedKey |= simple && foreignKey.referencedColumns.equals(simpleColumns);
          }
        }
        if (!referencedKey) {
          throw new IllegalArgumentException(
              "FOREIGN KEY on table " + table.name + " references non-unique key "
                  + foreignKey.referencedTable + foreignKey.referencedColumns);
        }
        for (int columnIndex = 0; columnIndex < foreignKey.columns.size(); columnIndex++) {
          ColumnDef source = sourceColumns.get(foreignKey.columns.get(columnIndex));
          ColumnDef target = referencedColumns.get(
              foreignKey.referencedColumns.get(columnIndex));
          if (source == null || target == null) {
            throw new IllegalArgumentException(
                "FOREIGN KEY on table " + table.name + " names an unknown column");
          }
          if (!postgresIntegrityEqualityCompatible(source, target)) {
            throw new IllegalArgumentException(
                "FOREIGN KEY equality types are incompatible for " + table.name + "."
                    + source.name + " and " + referenced.name + "." + target.name);
          }
        }
      }
    }
  }

  private static Map<String, ColumnDef> columnDefsByName(List<ColumnDef> columns) {
    Map<String, ColumnDef> byName = new HashMap<>();
    for (ColumnDef column : columns) {
      byName.put(column.name, column);
    }
    return byName;
  }

  private static boolean postgresIntegrityEqualityCompatible(
      ColumnDef left, ColumnDef right) {
    String leftType = integritySqlType(left);
    String rightType = integritySqlType(right);
    if (sameFormalIntegrityType(left, right, leftType, rightType)) {
      return true;
    }
    return isIntegrityIntegerType(leftType) && isIntegrityIntegerType(rightType);
  }

  private static boolean sameFormalIntegrityType(
      ColumnDef left, ColumnDef right, String leftType, String rightType) {
    if (!leftType.equals(rightType)) {
      return false;
    }
    return switch (leftType) {
      case "varchar", "char", "decimal", "timestamp", "timestampTz" ->
        left.precision == right.precision && left.scale == right.scale;
      default -> true;
    };
  }

  private static boolean varcharPatternOpsAccepts(String type) {
    return type.equals("text") || type.equals("varchar");
  }

  private static String postgresIntegrityCommonStringType(String left, String right) {
    if (left.equals("text") || right.equals("text")) {
      return "text";
    }
    return switch (left) {
      case "varchar" -> "varchar";
      case "char", "bpchar" -> "bpchar";
      default -> throw new IllegalArgumentException(
          "unsupported PostgreSQL character type " + left);
    };
  }

  private static boolean isIntegrityIntegerType(String type) {
    return type.equals("integer") || type.equals("bigInt");
  }

  private static boolean isIntegrityStringType(String type) {
    return type.equals("text") || type.equals("varchar") || type.equals("char")
        || type.equals("bpchar");
  }

  private static String integritySqlType(ColumnDef column) {
    String declared = column.declaredType.toUpperCase(Locale.ROOT);
    return switch (column.type) {
      case INTEGER -> "integer";
      case BIGINT -> "bigInt";
      case FLOAT -> "float";
      case DOUBLE -> "double";
      case DECIMAL -> "decimal";
      case BOOLEAN -> "boolean";
      case DATE -> "date";
      case TIME -> "time";
      case TIMESTAMP -> "timestamp";
      case TIMESTAMP_WITH_LOCAL_TIME_ZONE -> "timestampTz";
      case CHAR -> declared.startsWith("BPCHAR") ? "bpchar" : "char";
      case VARCHAR -> declared.startsWith("TEXT") ? "text" : "varchar";
      default -> throw new IllegalArgumentException(
          "unsupported integrity-constraint column type " + column.declaredType);
    };
  }

  private static ColumnConstraintFlags parseColumnConstraintFlags(String declaration) {
    int index = skipPostgresSqlWhitespace(declaration, columnConstraintStart(declaration));
    boolean notNull = false;
    boolean primaryKey = false;
    String primaryKeyName = null;
    while (index < declaration.length()) {
      String constraintName = null;
      if (matchesKeywordAt(declaration, index, "CONSTRAINT")) {
        int nameStart =
            skipPostgresSqlWhitespace(declaration, index + "CONSTRAINT".length());
        int nameEnd = postgresIdentifierEnd(declaration, nameStart);
        if (nameEnd <= nameStart) {
          throw new IllegalArgumentException(
              "inline CONSTRAINT is missing its PostgreSQL identifier: " + declaration);
        }
        constraintName =
            canonicalPostgresSchemaIdentifier(declaration.substring(nameStart, nameEnd));
        if (constraintName.isEmpty()) {
          throw new IllegalArgumentException(
              "inline CONSTRAINT has an empty PostgreSQL identifier: " + declaration);
        }
        if (nameEnd < declaration.length()
            && !isPostgresSqlWhitespace(declaration.charAt(nameEnd))) {
          throw new IllegalArgumentException(
              "inline CONSTRAINT name is not followed by a constraint: " + declaration);
        }
        index = skipPostgresSqlWhitespace(declaration, nameEnd);
      }
      if (matchesKeywordAt(declaration, index, "NOT")) {
        int nullStart = skipPostgresSqlWhitespace(declaration, index + "NOT".length());
        if (!matchesKeywordAt(declaration, nullStart, "NULL")) {
          throw new IllegalArgumentException(
              "malformed inline NOT NULL declaration: " + declaration);
        }
        if (notNull) {
          throw new IllegalArgumentException(
              "duplicate inline NOT NULL declaration: " + declaration);
        }
        notNull = true;
        index = skipPostgresSqlWhitespace(declaration, nullStart + "NULL".length());
        continue;
      }
      if (matchesKeywordAt(declaration, index, "PRIMARY")) {
        int keyStart = skipPostgresSqlWhitespace(declaration, index + "PRIMARY".length());
        if (!matchesKeywordAt(declaration, keyStart, "KEY")) {
          throw new IllegalArgumentException(
              "malformed inline PRIMARY KEY declaration: " + declaration);
        }
        if (primaryKey) {
          throw new IllegalArgumentException(
              "duplicate inline PRIMARY KEY declaration: " + declaration);
        }
        primaryKey = true;
        primaryKeyName = constraintName;
        index = skipPostgresSqlWhitespace(declaration, keyStart + "KEY".length());
        continue;
      }
      if (constraintName != null) {
        throw new IllegalArgumentException(
            "named inline constraints support only NOT NULL and PRIMARY KEY: " + declaration);
      }
      throw new IllegalArgumentException(
          "unsupported or malformed column-constraint tail: " + declaration.substring(index));
    }
    return new ColumnConstraintFlags(notNull, primaryKey, primaryKeyName);
  }

  private static int bareWordEnd(String text, int start) {
    if (start >= text.length() || !isBareIdentifierStart(text.charAt(start))) {
      return start;
    }
    int end = start + 1;
    while (end < text.length() && isBareIdentifierPart(text.charAt(end))) {
      end++;
    }
    return end;
  }

  private static boolean matchesKeywordAt(String text, int start, String keyword) {
    int end = start + keyword.length();
    return start >= 0
        && end <= text.length()
        && text.regionMatches(true, start, keyword, 0, keyword.length())
        && (start == 0 || !isBareIdentifierPart(text.charAt(start - 1)))
        && (end == text.length() || !isBareIdentifierPart(text.charAt(end)));
  }

  private static int postgresIdentifierEnd(String text, int start) {
    if (start >= text.length()) {
      return start;
    }
    if (text.charAt(start) == '"') {
      return quotedTokenEnd(text, start, '"');
    }
    return bareWordEnd(text, start);
  }

  private static String columnTypeDeclaration(String columnDeclaration) {
    String declaration = trimPostgresSqlWhitespace(stripSqlComments(columnDeclaration));
    int typeStart = columnNameEnd(declaration);
    while (typeStart < declaration.length()
        && isPostgresSqlWhitespace(declaration.charAt(typeStart))) {
      typeStart++;
    }
    if (typeStart >= declaration.length()) {
      return "";
    }

    int constraintStart = columnConstraintStart(declaration);
    return trimPostgresSqlWhitespace(declaration.substring(typeStart, constraintStart));
  }

  private static int columnConstraintStart(String declaration) {
    int typeStart = columnNameEnd(declaration);
    while (typeStart < declaration.length()
        && isPostgresSqlWhitespace(declaration.charAt(typeStart))) {
      typeStart++;
    }
    int depth = 0;
    char quote = 0;
    for (int i = typeStart; i < declaration.length();) {
      char c = declaration.charAt(i);
      if (quote != 0) {
        if (c == quote) {
          if (i + 1 < declaration.length() && declaration.charAt(i + 1) == quote) {
            i += 2;
            continue;
          }
          quote = 0;
        }
        i++;
        continue;
      }
      if (c == '\'' || c == '"' || c == '`') {
        quote = c;
        i++;
        continue;
      }
      if (c == '(') {
        depth++;
        i++;
        continue;
      }
      if (c == ')') {
        depth = Math.max(0, depth - 1);
        i++;
        continue;
      }
      if (depth == 0 && (Character.isLetter(c) || c == '_')) {
        int wordEnd = i + 1;
        while (wordEnd < declaration.length()) {
          char next = declaration.charAt(wordEnd);
          if (!Character.isLetterOrDigit(next) && next != '_') {
            break;
          }
          wordEnd++;
        }
        if (i > typeStart && isColumnConstraintKeyword(declaration.substring(i, wordEnd))) {
          return i;
        }
        i = wordEnd;
        continue;
      }
      i++;
    }
    return declaration.length();
  }

  private static int columnNameEnd(String declaration) {
    return postgresIdentifierEnd(declaration, 0);
  }

  private static boolean isColumnConstraintKeyword(String word) {
    return switch (word.toUpperCase(Locale.ROOT)) {
      case "NOT", "NULL", "DEFAULT", "GENERATED", "COLLATE", "CONSTRAINT",
          "PRIMARY", "UNIQUE", "REFERENCES", "CHECK", "AUTO_INCREMENT", "COMMENT",
          "ON", "KEY", "ENCODING", "COMPRESSION" -> true;
      default -> false;
    };
  }

  private static boolean hasExplicitColumnCollation(String columnDeclaration) {
    String declaration = trimPostgresSqlWhitespace(stripSqlComments(columnDeclaration));
    int start = columnNameEnd(declaration);
    int depth = 0;
    for (int i = start; i < declaration.length();) {
      char c = declaration.charAt(i);
      if (c == '\'' || c == '"' || c == '`') {
        i = quotedTokenEnd(declaration, i, c);
        continue;
      }
      if (c == '[') {
        i = bracketQuotedTokenEnd(declaration, i);
        continue;
      }
      if (c == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(declaration, i);
        if (delimiterEnd >= 0) {
          String delimiter = declaration.substring(i, delimiterEnd);
          int close = declaration.indexOf(delimiter, delimiterEnd);
          if (close < 0) {
            throw new IllegalArgumentException("unterminated dollar-quoted token in schema");
          }
          i = close + delimiter.length();
          continue;
        }
      }
      if (c == '(') {
        depth++;
        i++;
        continue;
      }
      if (c == ')') {
        depth--;
        if (depth < 0) {
          throw new IllegalArgumentException(
              "unbalanced closing parenthesis in column declaration");
        }
        i++;
        continue;
      }
      if (depth == 0 && (Character.isLetter(c) || c == '_')) {
        int wordEnd = i + 1;
        while (wordEnd < declaration.length()) {
          char next = declaration.charAt(wordEnd);
          if (!Character.isLetterOrDigit(next) && next != '_') {
            break;
          }
          wordEnd++;
        }
        if (declaration.substring(i, wordEnd).equalsIgnoreCase("COLLATE")) {
          return true;
        }
        i = wordEnd;
        continue;
      }
      i++;
    }
    if (depth != 0) {
      throw new IllegalArgumentException("unbalanced parenthesis in column declaration");
    }
    return false;
  }

  private static final Pattern POSTGRES_CHARACTER_TYPE = Pattern.compile(
      "(VARCHAR|CHAR|CHARACTER|CHARACTER VARYING)(?:\\s*\\(\\s*([0-9]+)\\s*\\))?");
  private static final Pattern POSTGRES_NUMERIC_TYPE = Pattern.compile(
      "(DECIMAL|NUMERIC)(?:\\s*\\(\\s*([0-9]+)"
          + "(?:\\s*,\\s*([0-9]+))?\\s*\\))?");
  private static final Pattern POSTGRES_FLOAT_TYPE = Pattern.compile(
      "FLOAT(?:\\s*\\(\\s*([0-9]+)\\s*\\))?");
  private static final Pattern POSTGRES_TIME_TYPE = Pattern.compile(
      "TIME(?:\\s*\\(\\s*([0-9]+)\\s*\\))?");
  private static final Pattern POSTGRES_TIMESTAMP_TYPE = Pattern.compile(
      "TIMESTAMP(?:\\s*\\(\\s*([0-9]+)\\s*\\))?"
          + "(?: (WITH|WITHOUT) TIME ZONE)?");
  private static final Pattern POSTGRES_TIMESTAMPTZ_TYPE = Pattern.compile(
      "TIMESTAMPTZ(?:\\s*\\(\\s*([0-9]+)\\s*\\))?");

  /** The one closed interpretation of PostgreSQL type names accepted by this frontend. */
  private record PostgresTypeSpec(
      SqlTypeName type, int precision, int scale, boolean timestampWithTimeZone) {}

  private static PostgresTypeSpec classifyPostgresType(String rawType) {
    String type = trimPostgresSqlWhitespace(rawType)
        .replaceAll("\\s+", " ")
        .toUpperCase(Locale.ROOT);
    int noPrecision = RelDataType.PRECISION_NOT_SPECIFIED;
    int noScale = RelDataType.SCALE_NOT_SPECIFIED;
    PostgresTypeSpec simple = switch (type) {
      case "TEXT" -> new PostgresTypeSpec(SqlTypeName.VARCHAR, noPrecision, noScale, false);
      case "BPCHAR" -> new PostgresTypeSpec(SqlTypeName.CHAR, noPrecision, noScale, false);
      case "BOOLEAN", "BOOL" ->
          new PostgresTypeSpec(SqlTypeName.BOOLEAN, noPrecision, noScale, false);
      case "DATE" -> new PostgresTypeSpec(SqlTypeName.DATE, noPrecision, noScale, false);
      case "BIGINT", "INT8" ->
          new PostgresTypeSpec(SqlTypeName.BIGINT, noPrecision, noScale, false);
      case "INT", "INTEGER" ->
          new PostgresTypeSpec(SqlTypeName.INTEGER, noPrecision, noScale, false);
      case "REAL", "FLOAT4" ->
          new PostgresTypeSpec(SqlTypeName.FLOAT, noPrecision, noScale, false);
      case "FLOAT8", "DOUBLE PRECISION" ->
          new PostgresTypeSpec(SqlTypeName.DOUBLE, noPrecision, noScale, false);
      default -> null;
    };
    if (simple != null) {
      return simple;
    }

    Matcher character = POSTGRES_CHARACTER_TYPE.matcher(type);
    if (character.matches()) {
      int precision = parsePostgresTypeModifier(character.group(2), rawType, noPrecision);
      if (precision != noPrecision && (precision < 1 || precision > 10_485_760)) {
        throw new IllegalArgumentException(
            "PostgreSQL character length must be between 1 and 10485760: " + rawType);
      }
      SqlTypeName sqlType = character.group(1).equals("VARCHAR")
              || character.group(1).equals("CHARACTER VARYING")
          ? SqlTypeName.VARCHAR
          : SqlTypeName.CHAR;
      return new PostgresTypeSpec(sqlType, precision, noScale, false);
    }

    Matcher numeric = POSTGRES_NUMERIC_TYPE.matcher(type);
    if (numeric.matches()) {
      int precision = parsePostgresTypeModifier(numeric.group(2), rawType, noPrecision);
      boolean scaleIsExplicit = numeric.group(3) != null;
      int scale = parsePostgresTypeModifier(numeric.group(3), rawType, noScale);
      if (precision != noPrecision && (precision < 1 || precision > 1000)) {
        throw new IllegalArgumentException(
            "PostgreSQL NUMERIC precision must be between 1 and 1000: " + rawType);
      }
      if (scaleIsExplicit && scale > 1000) {
        throw new IllegalArgumentException(
            "PostgreSQL NUMERIC scale must be between 0 and 1000: " + rawType);
      }
      return new PostgresTypeSpec(SqlTypeName.DECIMAL, precision, scale, false);
    }

    Matcher floating = POSTGRES_FLOAT_TYPE.matcher(type);
    if (floating.matches()) {
      int precision = parsePostgresTypeModifier(floating.group(1), rawType, noPrecision);
      if (precision != noPrecision && (precision < 1 || precision > 53)) {
        throw new IllegalArgumentException(
            "PostgreSQL FLOAT precision must be between 1 and 53: " + rawType);
      }
      SqlTypeName sqlType = precision != noPrecision && precision <= 24
          ? SqlTypeName.FLOAT
          : SqlTypeName.DOUBLE;
      return new PostgresTypeSpec(sqlType, precision, noScale, false);
    }

    Matcher time = POSTGRES_TIME_TYPE.matcher(type);
    if (time.matches()) {
      int precision = checkedTemporalPrecision(time.group(1), rawType, noPrecision);
      return new PostgresTypeSpec(SqlTypeName.TIME, precision, noScale, false);
    }

    Matcher timestamp = POSTGRES_TIMESTAMP_TYPE.matcher(type);
    if (timestamp.matches()) {
      int precision = checkedTemporalPrecision(timestamp.group(1), rawType, noPrecision);
      boolean withTimeZone = "WITH".equals(timestamp.group(2));
      SqlTypeName sqlType = withTimeZone
          ? SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE
          : SqlTypeName.TIMESTAMP;
      return new PostgresTypeSpec(sqlType, precision, noScale, withTimeZone);
    }

    Matcher timestamptz = POSTGRES_TIMESTAMPTZ_TYPE.matcher(type);
    if (timestamptz.matches()) {
      int precision = checkedTemporalPrecision(timestamptz.group(1), rawType, noPrecision);
      return new PostgresTypeSpec(
          SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE, precision, noScale, true);
    }

    throw new IllegalArgumentException(
        "unsupported or malformed PostgreSQL column type: " + rawType);
  }

  private static int checkedTemporalPrecision(
      String rawPrecision, String rawType, int unspecified) {
    int precision = parsePostgresTypeModifier(rawPrecision, rawType, unspecified);
    if (precision != unspecified && (precision < 0 || precision > 6)) {
      throw new IllegalArgumentException(
          "PostgreSQL temporal precision must be between 0 and 6: " + rawType);
    }
    return precision;
  }

  private static int parsePostgresTypeModifier(
      String rawModifier, String rawType, int unspecified) {
    if (rawModifier == null) {
      return unspecified;
    }
    try {
      return Integer.parseInt(rawModifier);
    } catch (NumberFormatException ignored) {
      throw new IllegalArgumentException(
          "PostgreSQL type modifier is out of range: " + rawType);
    }
  }

  private static String canonicalPostgresSchemaIdentifier(String name) {
    if (name.startsWith("`") || name.endsWith("`")) {
      throw new IllegalArgumentException(
          "PostgreSQL does not accept backtick-quoted identifiers: " + name);
    }
    if (name.isEmpty() || postgresIdentifierEnd(name, 0) != name.length()) {
      throw new IllegalArgumentException("invalid PostgreSQL schema identifier: " + name);
    }
    boolean quoted = name.startsWith("\"") && name.endsWith("\"");
    String canonical = quoted
        ? name.substring(1, name.length() - 1).replace("\"\"", "\"")
        : name.toLowerCase(Locale.ROOT);
    if (canonical.isEmpty()) {
      throw new IllegalArgumentException("PostgreSQL schema identifiers must not be empty");
    }
    if (canonical.indexOf('\0') >= 0) {
      throw new IllegalArgumentException("PostgreSQL schema identifiers must not contain NUL");
    }
    int byteLength = canonical.getBytes(StandardCharsets.UTF_8).length;
    if (byteLength > 63) {
      throw new IllegalArgumentException(
          "PostgreSQL schema identifier exceeds the 63-byte limit: " + byteLength + " bytes");
    }
    if (!quoted && POSTGRES_BARE_SCHEMA_IDENTIFIER_KEYWORDS.contains(canonical)) {
      throw new IllegalArgumentException(
          "PostgreSQL reserved keyword requires identifier quoting: " + canonical);
    }
    return canonical;
  }

  /**
   * Calcite represents both PostgreSQL grouping sublists {@code (a, b)} and
   * the observably different composite expression {@code ROW(a, b)} with a
   * ROW-shaped source node, and its pretty-printer erases the latter keyword.
   * Detect explicit ROW lexically before parsing so it cannot be flattened
   * into two grouping keys. Protected SQL text cannot impersonate syntax.
   */
  private static boolean containsExplicitRowInGroupBy(String sql) {
    int depth = 0;
    Integer pendingGroupDepth = null;
    Set<Integer> activeGroupDepths = new HashSet<>();

    for (int index = 0; index < sql.length();) {
      char current = sql.charAt(index);
      char next = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;
      if (isPostgresSqlWhitespace(current)) {
        index++;
        continue;
      }
      if (current == '-' && next == '-') {
        index += 2;
        while (index < sql.length()
            && sql.charAt(index) != '\n' && sql.charAt(index) != '\r') {
          index++;
        }
        continue;
      }
      if (current == '/' && next == '*') {
        int commentDepth = 1;
        index += 2;
        while (index < sql.length() && commentDepth > 0) {
          char block = sql.charAt(index);
          char blockNext = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;
          if (block == '/' && blockNext == '*') {
            commentDepth++;
            index += 2;
          } else if (block == '*' && blockNext == '/') {
            commentDepth--;
            index += 2;
          } else {
            index++;
          }
        }
        if (commentDepth != 0) {
          throw new IllegalArgumentException("unterminated block comment in SQL query file");
        }
        continue;
      }
      if (current == '\'' || current == '"' || current == '`') {
        index = quotedTokenEnd(sql, index, current);
        pendingGroupDepth = null;
        continue;
      }
      if (current == '[') {
        index = bracketQuotedTokenEnd(sql, index);
        pendingGroupDepth = null;
        continue;
      }
      if (current == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(sql, index);
        if (delimiterEnd >= 0) {
          String delimiter = sql.substring(index, delimiterEnd);
          int close = sql.indexOf(delimiter, delimiterEnd);
          if (close < 0) {
            throw new IllegalArgumentException("unterminated dollar-quoted SQL string");
          }
          index = close + delimiter.length();
          pendingGroupDepth = null;
          continue;
        }
      }
      if (isBareIdentifierStart(current)) {
        int end = index + 1;
        while (end < sql.length() && isBareIdentifierPart(sql.charAt(end))) {
          end++;
        }
        String word = sql.substring(index, end).toUpperCase(Locale.ROOT);
        int currentDepth = depth;
        boolean insideGroupClause = activeGroupDepths.stream()
            .anyMatch(groupDepth -> groupDepth <= currentDepth);
        if (insideGroupClause && word.equals("ROW")) {
          return true;
        }
        if (activeGroupDepths.contains(depth)
            && Set.of("HAVING", "WINDOW", "ORDER", "LIMIT", "OFFSET", "FETCH",
                      "UNION", "INTERSECT", "EXCEPT", "FOR")
                .contains(word)) {
          activeGroupDepths.remove(depth);
        }
        if (pendingGroupDepth != null
            && pendingGroupDepth == depth
            && word.equals("BY")) {
          activeGroupDepths.add(depth);
          pendingGroupDepth = null;
        } else {
          pendingGroupDepth = word.equals("GROUP") ? depth : null;
        }
        index = end;
        continue;
      }
      if (current == '(') {
        depth++;
        pendingGroupDepth = null;
        index++;
        continue;
      }
      if (current == ')') {
        int closingDepth = depth;
        activeGroupDepths.removeIf(groupDepth -> groupDepth >= closingDepth);
        depth = Math.max(0, depth - 1);
        pendingGroupDepth = null;
        index++;
        continue;
      }
      if (current == ';') {
        activeGroupDepths.clear();
      }
      pendingGroupDepth = null;
      index++;
    }
    return false;
  }

  private static List<String> splitQueries(String sql) {
    List<String> queries = new ArrayList<>();
    int start = 0;
    for (int index = 0; index < sql.length();) {
      char current = sql.charAt(index);
      char next = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;
      if (current == '-' && next == '-') {
        index += 2;
        while (index < sql.length()
            && sql.charAt(index) != '\n' && sql.charAt(index) != '\r') {
          index++;
        }
        continue;
      }
      if (current == '/' && next == '*') {
        int depth = 1;
        index += 2;
        while (index < sql.length() && depth > 0) {
          char block = sql.charAt(index);
          char blockNext = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;
          if (block == '/' && blockNext == '*') {
            depth++;
            index += 2;
          } else if (block == '*' && blockNext == '/') {
            depth--;
            index += 2;
          } else {
            index++;
          }
        }
        if (depth != 0) {
          throw new IllegalArgumentException("unterminated block comment in SQL query file");
        }
        continue;
      }
      if (current == '\'' || current == '"' || current == '`') {
        index = quotedTokenEnd(sql, index, current);
        continue;
      }
      if (current == '[') {
        index = bracketQuotedTokenEnd(sql, index);
        continue;
      }
      if (current == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(sql, index);
        if (delimiterEnd >= 0) {
          String delimiter = sql.substring(index, delimiterEnd);
          int close = sql.indexOf(delimiter, delimiterEnd);
          if (close < 0) {
            throw new IllegalArgumentException("unterminated dollar-quoted SQL string");
          }
          index = close + delimiter.length();
          continue;
        }
      }
      if (current == ';') {
        addQuery(sql.substring(start, index), queries);
        start = index + 1;
      }
      index++;
    }
    addQuery(sql.substring(start), queries);
    return queries;
  }

  private static int quotedTokenEnd(String sql, int start, char quote) {
    int index = start + 1;
    boolean backslashEscapes = quote == '\'' && isPostgresEscapeStringQuote(sql, start);
    while (index < sql.length()) {
      char current = sql.charAt(index++);
      if (current == '\\' && backslashEscapes && index < sql.length()) {
        index++;
      } else if (current == quote) {
        if (index < sql.length() && sql.charAt(index) == quote) {
          index++;
        } else {
          return index;
        }
      }
    }
    throw new IllegalArgumentException("unterminated quoted token in SQL query file");
  }

  private static boolean isPostgresEscapeStringQuote(String sql, int quoteStart) {
    if (quoteStart == 0) {
      return false;
    }
    char prefix = sql.charAt(quoteStart - 1);
    if (prefix != 'E' && prefix != 'e') {
      return false;
    }
    if (quoteStart == 1) {
      return true;
    }
    char beforePrefix = sql.charAt(quoteStart - 2);
    return !isBareIdentifierPart(beforePrefix) && beforePrefix < 0x80;
  }

  private static int bracketQuotedTokenEnd(String sql, int start) {
    int index = start + 1;
    while (index < sql.length()) {
      if (sql.charAt(index++) == ']') {
        if (index < sql.length() && sql.charAt(index) == ']') {
          index++;
        } else {
          return index;
        }
      }
    }
    throw new IllegalArgumentException("unterminated bracket-quoted identifier in SQL query file");
  }

  private static void addQuery(String query, List<String> queries) {
    String trimmed = trimPostgresSqlWhitespace(query);
    if (!trimmed.isEmpty() && containsSqlToken(trimmed)) {
      queries.add(trimmed);
    }
  }

  private static boolean containsSqlToken(String sql) {
    for (int index = 0; index < sql.length();) {
      char current = sql.charAt(index);
      char next = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;
      if (isPostgresSqlWhitespace(current)) {
        index++;
      } else if (current == '-' && next == '-') {
        index += 2;
        while (index < sql.length()
            && sql.charAt(index) != '\n' && sql.charAt(index) != '\r') {
          index++;
        }
      } else if (current == '/' && next == '*') {
        int depth = 1;
        index += 2;
        while (index < sql.length() && depth > 0) {
          char block = sql.charAt(index);
          char blockNext = index + 1 < sql.length() ? sql.charAt(index + 1) : 0;
          if (block == '/' && blockNext == '*') {
            depth++;
            index += 2;
          } else if (block == '*' && blockNext == '/') {
            depth--;
            index += 2;
          } else {
            index++;
          }
        }
        if (depth != 0) {
          throw new IllegalArgumentException("unterminated block comment in SQL query file");
        }
      } else {
        return true;
      }
    }
    return false;
  }

  private static Map<String, String> parseArgs(String[] args, List<String> sqlPaths) {
    Map<String, String> opts = new LinkedHashMap<>();
    for (int i = 0; i < args.length; i++) {
      String arg = args[i];
      if (!arg.startsWith("--") || arg.length() == 2) {
        throw new IllegalArgumentException("unexpected positional argument: " + arg);
      }
      String name = arg.substring(2);
      if (!CLI_OPTIONS.contains(name)) {
        throw new IllegalArgumentException("unknown option: --" + name);
      }
      if (i + 1 >= args.length || args[i + 1].startsWith("--")) {
        throw new IllegalArgumentException("missing value for option: --" + name);
      }
      String value = args[++i];
      if (name.equals("sql")) {
        sqlPaths.add(value);
        continue;
      }
      String previous = opts.putIfAbsent(name, value);
      if (previous != null) {
        throw new IllegalArgumentException("duplicate option: --" + name);
      }
    }
    return opts;
  }

  private static String canonicalDefaultCollation(String value) {
    if (value.equalsIgnoreCase("unspecified")) {
      return "unspecified";
    }
    if (value.equalsIgnoreCase("C")) {
      return "C";
    }
    throw new IllegalArgumentException(
        "unsupported default collation " + value + "; expected unspecified or C");
  }

  private static String canonicalServerEncoding(String value) {
    if (value.equalsIgnoreCase("unspecified")) {
      return "unspecified";
    }
    if (value.equalsIgnoreCase("UTF8") || value.equalsIgnoreCase("UTF-8")) {
      return "UTF8";
    }
    throw new IllegalArgumentException(
        "unsupported server encoding " + value + "; expected unspecified or UTF8");
  }

  private static String canonicalCharacterClassification(String value) {
    if (value.equalsIgnoreCase("unspecified")) {
      return "unspecified";
    }
    if (value.equalsIgnoreCase("C")) {
      return "C";
    }
    throw new IllegalArgumentException(
        "unsupported character classification " + value + "; expected unspecified or C");
  }

  private static String canonicalLocaleProvider(String value) {
    if (value.equalsIgnoreCase("unspecified")) {
      return "unspecified";
    }
    if (value.equalsIgnoreCase("libc")) {
      return "libc";
    }
    throw new IllegalArgumentException(
        "unsupported locale provider " + value + "; expected unspecified or libc");
  }

  private static void usage() {
    System.err.println(
        "Usage: calcite-ir --schema <schema.sql> --sql <query.sql> "
            + "[--default-collation unspecified|C] "
            + "[--character-classification unspecified|C] "
            + "[--locale-provider unspecified|libc] "
            + "[--server-encoding unspecified|UTF8]");
  }

  private enum TableConstraintKind {
    PRIMARY_KEY("PRIMARY KEY", true),
    UNIQUE("UNIQUE", true),
    FOREIGN_KEY("FOREIGN KEY", false),
    CHECK("CHECK", false);

    private final String sqlName;
    private final boolean producesIndex;

    TableConstraintKind(String sqlName, boolean producesIndex) {
      this.sqlName = sqlName;
      this.producesIndex = producesIndex;
    }
  }

  private record TableConstraintDef(
      TableConstraintKind kind,
      String name,
      List<String> columns,
      ForeignKeySpec foreignKey,
      String checkExpression) {
    private TableConstraintDef {
      columns = List.copyOf(columns);
    }
  }

  private record ForeignKeySpec(
      String referencedTable,
      List<String> referencedColumns,
      String referentialActions) {
    private ForeignKeySpec {
      referencedColumns = List.copyOf(referencedColumns);
    }
  }

  private record UniqueConstraintDef(String name, List<String> columns) {
    private UniqueConstraintDef {
      columns = List.copyOf(columns);
    }
  }

  private record ForeignKeyDef(
      String name,
      List<String> columns,
      String referencedTable,
      List<String> referencedColumns,
      String referentialActions) {
    private ForeignKeyDef {
      columns = List.copyOf(columns);
      referencedColumns = List.copyOf(referencedColumns);
    }
  }

  private record CheckDef(
      String name, String expression, IntegrityPredicateDef validatedExpression) {}

  private record UniqueIndexTermDef(
      IntegrityValueDef expression,
      String sourceSql,
      String direction,
      String nulls,
      String operatorClass) {}

  private record UniqueIndexDef(
      String name,
      List<UniqueIndexTermDef> terms,
      IntegrityPredicateDef predicate,
      String predicateSql) {
    private UniqueIndexDef {
      terms = List.copyOf(terms);
    }
  }

  private record UnboundUniqueIndexDef(
      String name, List<String> rawTerms, String predicateSql) {
    private UnboundUniqueIndexDef {
      rawTerms = List.copyOf(rawTerms);
    }
  }

  private record ParsedUniqueIndex(String tableName, UnboundUniqueIndexDef index) {}

  private interface IntegrityValueDef {
    String sqlType();
  }

  private record IntegrityColumnDef(
      String name, String sqlType) implements IntegrityValueDef {}

  private record IntegrityLiteralDef(
      String raw, String sqlType) implements IntegrityValueDef {}

  private record IntegrityCastDef(
      IntegrityValueDef expression, String sqlType) implements IntegrityValueDef {}

  private record IntegrityLowerDef(
      IntegrityValueDef expression) implements IntegrityValueDef {
    @Override
    public String sqlType() {
      return "text";
    }
  }

  private record IntegrityCoalesceDef(
      List<IntegrityValueDef> arguments, String sqlType) implements IntegrityValueDef {
    private IntegrityCoalesceDef {
      arguments = List.copyOf(arguments);
    }
  }

  private interface IntegrityPredicateDef {}

  private record IntegrityTruthDef(
      IntegrityValueDef expression) implements IntegrityPredicateDef {}

  private record IntegrityIsNullDef(
      IntegrityValueDef expression) implements IntegrityPredicateDef {}

  private record IntegrityIsNotNullDef(
      IntegrityValueDef expression) implements IntegrityPredicateDef {}

  private record IntegrityComparisonDef(
      String comparison,
      IntegrityValueDef left,
      IntegrityValueDef right) implements IntegrityPredicateDef {}

  private record IntegrityAnyDef(
      String comparison,
      IntegrityValueDef left,
      List<IntegrityValueDef> values) implements IntegrityPredicateDef {
    private IntegrityAnyDef {
      values = List.copyOf(values);
    }
  }

  private record IntegrityAndDef(
      IntegrityPredicateDef left,
      IntegrityPredicateDef right) implements IntegrityPredicateDef {}

  private record IntegrityOrDef(
      IntegrityPredicateDef left,
      IntegrityPredicateDef right) implements IntegrityPredicateDef {}

  private record IntegrityNotDef(
      IntegrityPredicateDef predicate) implements IntegrityPredicateDef {}

  private record TableConstraints(
      List<String> notNull,
      List<String> primaryKey,
      List<UniqueConstraintDef> unique,
      List<ForeignKeyDef> foreignKeys,
      List<CheckDef> checks,
      List<UniqueIndexDef> uniqueIndexes) {
    private TableConstraints {
      notNull = List.copyOf(notNull);
      primaryKey = List.copyOf(primaryKey);
      unique = List.copyOf(unique);
      foreignKeys = List.copyOf(foreignKeys);
      checks = List.copyOf(checks);
      uniqueIndexes = List.copyOf(uniqueIndexes);
    }

    boolean isEmpty() {
      return notNull.isEmpty()
          && primaryKey.isEmpty()
          && unique.isEmpty()
          && foreignKeys.isEmpty()
          && checks.isEmpty()
          && uniqueIndexes.isEmpty();
    }

    TableConstraints withUniqueIndex(UniqueIndexDef index) {
      List<UniqueIndexDef> extended = new ArrayList<>(uniqueIndexes);
      extended.add(index);
      return new TableConstraints(
          notNull, primaryKey, unique, foreignKeys, checks, extended);
    }
  }

  private record ColumnConstraintFlags(
      boolean notNull, boolean primaryKey, String primaryKeyName) {}

  private record TableDef(
      String name, List<ColumnDef> columns, TableConstraints constraints) {}

  private record ColumnDef(
      String name, String declaredType, SqlTypeName type, int precision, int scale,
      boolean timestampWithTimeZone, boolean explicitCollation) {
    static ColumnDef parse(String name, String rawType, boolean explicitCollation) {
      PostgresTypeSpec postgresType = classifyPostgresType(rawType);
      int precision = postgresType.precision();
      SqlTypeName type = postgresType.type();
      if (type == SqlTypeName.FLOAT || type == SqlTypeName.DOUBLE) {
        precision = RelDataType.PRECISION_NOT_SPECIFIED;
      }
      if ((type == SqlTypeName.TIMESTAMP || type == SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE)
          && precision == RelDataType.PRECISION_NOT_SPECIFIED) {
        precision = 6;
      }
      return new ColumnDef(
          name,
          trimPostgresSqlWhitespace(rawType),
          type,
          precision,
          postgresType.scale(),
          postgresType.timestampWithTimeZone(),
          explicitCollation);
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
      if (precision >= 0 && scale != RelDataType.SCALE_NOT_SPECIFIED) {
        return typeName + "(" + precision + ", " + scale + ")";
      }
      if (precision >= 0) {
        return typeName + "(" + precision + ")";
      }
      return typeName;
    }
  }

  private static String stripSqlComments(String sql) {
    StringBuilder stripped = new StringBuilder(sql.length());
    char quote = 0;
    boolean backslashEscapes = false;
    boolean lineComment = false;
    int blockCommentDepth = 0;
    for (int i = 0; i < sql.length();) {
      char c = sql.charAt(i);
      char next = i + 1 < sql.length() ? sql.charAt(i + 1) : 0;
      if (lineComment) {
        if (c == '\n' || c == '\r') {
          lineComment = false;
          stripped.append(c);
        }
        i++;
        continue;
      }
      if (blockCommentDepth > 0) {
        if (c == '/' && next == '*') {
          blockCommentDepth++;
          i += 2;
        } else if (c == '*' && next == '/') {
          blockCommentDepth--;
          i += 2;
        } else {
          if (c == '\n' || c == '\r') {
            stripped.append(c);
          }
          i++;
        }
        continue;
      }
      if (quote != 0) {
        stripped.append(c);
        if (c == '\\' && backslashEscapes && i + 1 < sql.length()) {
          stripped.append(next);
          i += 2;
          continue;
        }
        if (c == quote) {
          if (next == quote) {
            stripped.append(next);
            i += 2;
            continue;
          }
          quote = 0;
          backslashEscapes = false;
        }
        i++;
        continue;
      }
      if (c == '\'' || c == '"' || c == '`') {
        quote = c;
        backslashEscapes = c == '\'' && isPostgresEscapeStringQuote(sql, i);
        stripped.append(c);
        i++;
      } else if (c == '$') {
        int delimiterEnd = dollarQuoteDelimiterEnd(sql, i);
        if (delimiterEnd < 0) {
          stripped.append(c);
          i++;
          continue;
        }
        String delimiter = sql.substring(i, delimiterEnd);
        int close = sql.indexOf(delimiter, delimiterEnd);
        if (close < 0) {
          throw new IllegalArgumentException("unterminated dollar-quoted token in schema");
        }
        int tokenEnd = close + delimiter.length();
        stripped.append(sql, i, tokenEnd);
        i = tokenEnd;
      } else if (c == '-' && next == '-') {
        lineComment = true;
        stripped.append(' ');
        i += 2;
      } else if (c == '/' && next == '*') {
        blockCommentDepth = 1;
        stripped.append(' ');
        i += 2;
      } else {
        stripped.append(c);
        i++;
      }
    }
    if (blockCommentDepth != 0 || quote != 0) {
      throw new IllegalArgumentException("unterminated SQL comment or quoted token in schema");
    }
    return stripped.toString();
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
        if (column.precision >= 0 && column.scale != RelDataType.SCALE_NOT_SPECIFIED) {
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
          if (typeName == SqlTypeName.TIME
              || typeName == SqlTypeName.TIMESTAMP
              || typeName == SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE) {
            return 6;
          }
          return super.getMaxPrecision(typeName);
        }

        @Override public int getDefaultPrecision(SqlTypeName typeName) {
          if (typeName == SqlTypeName.TIME
              || typeName == SqlTypeName.TIMESTAMP
              || typeName == SqlTypeName.TIMESTAMP_WITH_LOCAL_TIME_ZONE) {
            return 6;
          }
          return super.getDefaultPrecision(typeName);
        }

        @Override public RelDataType deriveSumType(
            RelDataTypeFactory typeFactory, RelDataType argumentType) {
          if (argumentType.getSqlTypeName() == SqlTypeName.INTEGER) {
            // PostgreSQL returns bigint for SUM(integer). The wrapper also
            // preserves Calcite's operand nullability here; its aggregate
            // inference separately makes an empty-group SUM nullable. Other
            // input families retain Calcite's behavior until Logos can
            // represent PostgreSQL's wider result types exactly.
            RelDataType resultType = typeFactory.createSqlType(SqlTypeName.BIGINT);
            return typeFactory.createTypeWithNullability(
                resultType, argumentType.isNullable());
          }
          return super.deriveSumType(typeFactory, argumentType);
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

    Json rawJson(String value) {
      sb.append(value);
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
