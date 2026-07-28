SELECT "nation"."n_name", "nation0"."n_name0", EXTRACT(YEAR FROM "lineitem"."l_shipdate") AS "l_year", COALESCE(SUM("lineitem"."l_extendedprice" * (1 - "lineitem"."l_discount")), 0) AS "revenue"
FROM "supplier",
    "lineitem",
    "orders",
    "customer",
    "nation",
    "nation" AS "nation0" ("n_nationkey0", "n_name0", "n_regionkey0", "n_comment0")
WHERE "supplier"."s_suppkey" = "lineitem"."l_suppkey" AND "orders"."o_orderkey" = "lineitem"."l_orderkey" AND ("customer"."c_custkey" = "orders"."o_custkey" AND "supplier"."s_nationkey" = "nation"."n_nationkey") AND ("customer"."c_nationkey" = "nation0"."n_nationkey0" AND ("nation"."n_name" = 'KENYA' AND "nation0"."n_name0" = 'CANADA' OR "nation"."n_name" = 'CANADA' AND "nation0"."n_name0" = 'KENYA') AND ("lineitem"."l_shipdate" >= DATE '1995-01-01' AND "lineitem"."l_shipdate" <= DATE '1996-12-31'))
GROUP BY "nation"."n_name", "nation0"."n_name0", EXTRACT(YEAR FROM "lineitem"."l_shipdate")
ORDER BY "nation"."n_name", "nation0"."n_name0", 3
FETCH NEXT 1 ROWS ONLY;
