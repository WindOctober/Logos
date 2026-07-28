SELECT "lineitem"."l_orderkey", COALESCE(SUM("lineitem"."l_extendedprice" * (1 - "lineitem"."l_discount")), 0) AS "revenue", "orders"."o_orderdate", "orders"."o_shippriority"
FROM "customer",
    "orders",
    "lineitem"
WHERE "customer"."c_mktsegment" = 'FURNITURE' AND "customer"."c_custkey" = "orders"."o_custkey" AND "lineitem"."l_orderkey" = "orders"."o_orderkey" AND "orders"."o_orderdate" < DATE '1995-03-28' AND "lineitem"."l_shipdate" > DATE '1995-03-28'
GROUP BY "lineitem"."l_orderkey", "orders"."o_orderdate", "orders"."o_shippriority"
ORDER BY 2 DESC, "orders"."o_orderdate"
FETCH NEXT 10 ROWS ONLY;
