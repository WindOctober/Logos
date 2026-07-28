SELECT "customer"."c_custkey", "customer"."c_name", COALESCE(SUM("lineitem"."l_extendedprice" * (1 - "lineitem"."l_discount")), 0) AS "revenue", "customer"."c_acctbal", "nation"."n_name", "customer"."c_address", "customer"."c_phone", "customer"."c_comment"
FROM "customer",
    "orders",
    "lineitem",
    "nation"
WHERE "customer"."c_custkey" = "orders"."o_custkey" AND ("lineitem"."l_orderkey" = "orders"."o_orderkey" AND "orders"."o_orderdate" >= DATE '1993-11-01') AND ("orders"."o_orderdate" < (DATE '1993-11-01' + INTERVAL '3' MONTH) AND ("lineitem"."l_returnflag" = 'R' AND "customer"."c_nationkey" = "nation"."n_nationkey"))
GROUP BY "customer"."c_custkey", "customer"."c_name", "customer"."c_acctbal", "customer"."c_phone", "nation"."n_name", "customer"."c_address", "customer"."c_comment"
ORDER BY 3 DESC
FETCH NEXT 20 ROWS ONLY;
