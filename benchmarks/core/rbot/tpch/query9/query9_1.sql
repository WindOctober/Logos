SELECT "nation"."n_name" AS "nation", EXTRACT(YEAR FROM "orders"."o_orderdate") AS "o_year", COALESCE(SUM("lineitem"."l_extendedprice" * (1 - "lineitem"."l_discount") - "partsupp"."ps_supplycost" * "lineitem"."l_quantity"), 0) AS "sum_profit"
FROM "part",
    "supplier",
    "lineitem",
    "partsupp",
    "orders",
    "nation"
WHERE "supplier"."s_suppkey" = "lineitem"."l_suppkey" AND ("partsupp"."ps_suppkey" = "lineitem"."l_suppkey" AND "partsupp"."ps_partkey" = "lineitem"."l_partkey") AND ("part"."p_partkey" = "lineitem"."l_partkey" AND "orders"."o_orderkey" = "lineitem"."l_orderkey" AND ("supplier"."s_nationkey" = "nation"."n_nationkey" AND "part"."p_name" LIKE '%cyan%'))
GROUP BY "nation"."n_name", EXTRACT(YEAR FROM "orders"."o_orderdate")
ORDER BY "nation"."n_name", 2 DESC
FETCH NEXT 1 ROWS ONLY;
