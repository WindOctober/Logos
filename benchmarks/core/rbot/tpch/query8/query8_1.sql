SELECT EXTRACT(YEAR FROM "orders"."o_orderdate") AS "o_year", COALESCE(SUM(CASE WHEN "nation0"."n_name0" = 'CANADA' THEN "lineitem"."l_extendedprice" * (1 - "lineitem"."l_discount") ELSE 0 END), 0) / COALESCE(SUM("lineitem"."l_extendedprice" * (1 - "lineitem"."l_discount")), 0) AS "mkt_share"
FROM "part",
    "supplier",
    "lineitem",
    "orders",
    "customer",
    "nation",
    "nation" AS "nation0" ("n_nationkey0", "n_name0", "n_regionkey0", "n_comment0"),
    "region"
WHERE "part"."p_partkey" = "lineitem"."l_partkey" AND "supplier"."s_suppkey" = "lineitem"."l_suppkey" AND ("lineitem"."l_orderkey" = "orders"."o_orderkey" AND ("orders"."o_custkey" = "customer"."c_custkey" AND "customer"."c_nationkey" = "nation"."n_nationkey")) AND ("nation"."n_regionkey" = "region"."r_regionkey" AND ("region"."r_name" = 'AMERICA' AND "supplier"."s_nationkey" = "nation0"."n_nationkey0") AND ("orders"."o_orderdate" >= DATE '1995-01-01' AND ("orders"."o_orderdate" <= DATE '1996-12-31' AND "part"."p_type" = 'SMALL BURNISHED STEEL')))
GROUP BY EXTRACT(YEAR FROM "orders"."o_orderdate")
ORDER BY 1
FETCH NEXT 1 ROWS ONLY;
