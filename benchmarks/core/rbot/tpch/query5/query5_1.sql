SELECT "nation"."n_name", COALESCE(SUM("lineitem"."l_extendedprice" * (1 - "lineitem"."l_discount")), 0) AS "revenue"
FROM "customer",
    "orders",
    "lineitem",
    "supplier",
    "nation",
    "region"
WHERE "customer"."c_custkey" = "orders"."o_custkey" AND "lineitem"."l_orderkey" = "orders"."o_orderkey" AND ("lineitem"."l_suppkey" = "supplier"."s_suppkey" AND "customer"."c_nationkey" = "supplier"."s_nationkey") AND ("supplier"."s_nationkey" = "nation"."n_nationkey" AND "nation"."n_regionkey" = "region"."r_regionkey" AND ("region"."r_name" = 'EUROPE' AND ("orders"."o_orderdate" >= DATE '1994-01-01' AND "orders"."o_orderdate" < (DATE '1994-01-01' + INTERVAL '1' YEAR))))
GROUP BY "nation"."n_name"
ORDER BY 2 DESC
FETCH NEXT 1 ROWS ONLY;
