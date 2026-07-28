SELECT "t7"."s_name", "t7"."s_address"
FROM (SELECT *
        FROM "supplier"
        WHERE "s_suppkey" IN (SELECT "ps_suppkey"
                    FROM "partsupp"
                    WHERE "ps_partkey" IN (SELECT "p_partkey"
                                FROM "part"
                                WHERE "p_name" LIKE 'snow%') AND "ps_availqty" > (((SELECT 0.5 * SUM("l_quantity")
                                        FROM "lineitem"
                                        WHERE "l_partkey" = "partsupp"."ps_partkey" AND "l_suppkey" = "partsupp"."ps_suppkey" AND "l_shipdate" >= DATE '1994-01-01' AND "l_shipdate" < (DATE '1994-01-01' + INTERVAL '1' YEAR)))))) AS "t7"
    INNER JOIN (SELECT *
        FROM "nation"
        WHERE "n_name" = 'EGYPT') AS "t8" ON "t7"."s_nationkey" = "t8"."n_nationkey"
ORDER BY "t7"."s_name"
FETCH NEXT 1 ROWS ONLY;
