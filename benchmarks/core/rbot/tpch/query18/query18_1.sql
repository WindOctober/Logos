SELECT "customer"."c_name", "customer"."c_custkey", "orders"."o_orderkey", "orders"."o_orderdate", "orders"."o_totalprice", SUM("lineitem"."l_quantity")
FROM "customer",
    "orders",
    "lineitem"
WHERE "orders"."o_orderkey" IN (SELECT "l_orderkey0"
            FROM "lineitem" AS "lineitem0" ("l_orderkey0", "l_partkey0", "l_suppkey0", "l_linenumber0", "l_quantity0", "l_extendedprice0", "l_discount0", "l_tax0", "l_returnflag0", "l_linestatus0", "l_shipdate0", "l_commitdate0", "l_receiptdate0", "l_shipinstruct0", "l_shipmode0", "l_comment0")
            GROUP BY "l_orderkey0"
            HAVING SUM("l_quantity0") > 313) AND "customer"."c_custkey" = "orders"."o_custkey" AND "orders"."o_orderkey" = "lineitem"."l_orderkey"
GROUP BY "customer"."c_custkey", "customer"."c_name", "orders"."o_orderkey", "orders"."o_totalprice", "orders"."o_orderdate"
ORDER BY "orders"."o_totalprice" DESC, "orders"."o_orderdate"
FETCH NEXT 100 ROWS ONLY;
