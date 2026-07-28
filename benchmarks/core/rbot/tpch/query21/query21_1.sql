SELECT "supplier"."s_name", COUNT(*) AS "numwait"
FROM "supplier",
    "lineitem",
    "orders",
    "nation"
WHERE "supplier"."s_suppkey" = "lineitem"."l_suppkey" AND "orders"."o_orderkey" = "lineitem"."l_orderkey" AND ("orders"."o_orderstatus" = 'F' AND "lineitem"."l_receiptdate" > "lineitem"."l_commitdate") AND (EXISTS (SELECT *
                    FROM "lineitem" AS "lineitem0" ("l_orderkey0", "l_partkey0", "l_suppkey0", "l_linenumber0", "l_quantity0", "l_extendedprice0", "l_discount0", "l_tax0", "l_returnflag0", "l_linestatus0", "l_shipdate0", "l_commitdate0", "l_receiptdate0", "l_shipinstruct0", "l_shipmode0", "l_comment0")
                    WHERE "l_orderkey0" = "lineitem"."l_orderkey" AND "l_suppkey0" <> "lineitem"."l_suppkey") AND NOT EXISTS (SELECT *
                    FROM "lineitem" AS "lineitem1" ("l_orderkey1", "l_partkey1", "l_suppkey1", "l_linenumber1", "l_quantity1", "l_extendedprice1", "l_discount1", "l_tax1", "l_returnflag1", "l_linestatus1", "l_shipdate1", "l_commitdate1", "l_receiptdate1", "l_shipinstruct1", "l_shipmode1", "l_comment1")
                    WHERE "l_orderkey1" = "lineitem"."l_orderkey" AND "l_suppkey1" <> "lineitem"."l_suppkey" AND "l_receiptdate1" > "l_commitdate1") AND ("supplier"."s_nationkey" = "nation"."n_nationkey" AND "nation"."n_name" = 'FRANCE'))
GROUP BY "supplier"."s_name"
ORDER BY 2 DESC, "supplier"."s_name"
FETCH NEXT 100 ROWS ONLY;
