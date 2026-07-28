SELECT SUM("lineitem"."l_extendedprice") / 7.0 AS "avg_yearly"
FROM "lineitem",
    "part"
WHERE "part"."p_partkey" = "lineitem"."l_partkey" AND "part"."p_brand" = 'Brand#23' AND "part"."p_container" = 'WRAP BAG' AND "lineitem"."l_quantity" < (((SELECT 0.2 * AVG("l_quantity0")
                    FROM "lineitem" AS "lineitem0" ("l_orderkey0", "l_partkey0", "l_suppkey0", "l_linenumber0", "l_quantity0", "l_extendedprice0", "l_discount0", "l_tax0", "l_returnflag0", "l_linestatus0", "l_shipdate0", "l_commitdate0", "l_receiptdate0", "l_shipinstruct0", "l_shipmode0", "l_comment0")
                    WHERE "l_partkey0" = "part"."p_partkey")))
FETCH NEXT 1 ROWS ONLY;
