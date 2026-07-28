SELECT "supplier"."s_suppkey", "supplier"."s_name", "supplier"."s_address", "supplier"."s_phone", "t1"."EXPR$1" AS "total_revenue"
FROM "supplier",
        (SELECT "l_suppkey", COALESCE(SUM("l_extendedprice" * (1 - "l_discount")), 0) AS "EXPR$1"
        FROM "lineitem"
        WHERE "l_shipdate" >= DATE '1993-05-01' AND "l_shipdate" < (DATE '1993-05-01' + INTERVAL '3' MONTH)
        GROUP BY "l_suppkey") AS "t1"
WHERE "supplier"."s_suppkey" = "t1"."l_suppkey" AND "t1"."EXPR$1" = (((SELECT MAX("EXPR$1")
                    FROM (SELECT SUM("l_extendedprice0" * (1 - "l_discount0")) AS "EXPR$1"
                            FROM "lineitem" AS "lineitem0" ("l_orderkey0", "l_partkey0", "l_suppkey0", "l_linenumber0", "l_quantity0", "l_extendedprice0", "l_discount0", "l_tax0", "l_returnflag0", "l_linestatus0", "l_shipdate0", "l_commitdate0", "l_receiptdate0", "l_shipinstruct0", "l_shipmode0", "l_comment0")
                            WHERE "l_shipdate0" >= DATE '1993-05-01' AND "l_shipdate0" < (DATE '1993-05-01' + INTERVAL '3' MONTH)
                            GROUP BY "l_suppkey0") AS "t5")))
ORDER BY "supplier"."s_suppkey"
FETCH NEXT 1 ROWS ONLY;
