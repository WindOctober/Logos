SELECT "supplier"."s_acctbal", "supplier"."s_name", "nation"."n_name", "t"."p_partkey", "t"."p_mfgr", "supplier"."s_address", "supplier"."s_phone", "supplier"."s_comment"
FROM (SELECT *
        FROM "part"
        WHERE "p_size" = 7 AND "p_type" LIKE '%COPPER') AS "t"
    CROSS JOIN "supplier"
    INNER JOIN "partsupp" ON "t"."p_partkey" = "partsupp"."ps_partkey" AND "supplier"."s_suppkey" = "partsupp"."ps_suppkey"
    INNER JOIN "nation" ON "supplier"."s_nationkey" = "nation"."n_nationkey"
    INNER JOIN (SELECT *
        FROM "region"
        WHERE "r_name" = 'MIDDLE EAST') AS "t0" ON "nation"."n_regionkey" = "t0"."r_regionkey"
    INNER JOIN (SELECT "partsupp0"."ps_partkey0", MIN("partsupp0"."ps_supplycost0") AS "EXPR$0"
        FROM "partsupp" AS "partsupp0" ("ps_partkey0", "ps_suppkey0", "ps_availqty0", "ps_supplycost0", "ps_comment0")
            INNER JOIN "supplier" AS "supplier0" ("s_suppkey0", "s_name0", "s_address0", "s_nationkey0", "s_phone0", "s_acctbal0", "s_comment0") ON "partsupp0"."ps_suppkey0" = "supplier0"."s_suppkey0"
            INNER JOIN "nation" AS "nation0" ("n_nationkey0", "n_name0", "n_regionkey0", "n_comment0") ON "supplier0"."s_nationkey0" = "nation0"."n_nationkey0"
            INNER JOIN (SELECT *
                FROM "region" AS "region0" ("r_regionkey0", "r_name0", "r_comment0")
                WHERE "r_name0" = 'MIDDLE EAST') AS "t1" ON "nation0"."n_regionkey0" = "t1"."r_regionkey0"
        GROUP BY "partsupp0"."ps_partkey0") AS "t3" ON "t"."p_partkey" = "t3"."ps_partkey0" AND "partsupp"."ps_supplycost" = "t3"."EXPR$0"
ORDER BY "supplier"."s_acctbal" DESC, "nation"."n_name", "supplier"."s_name", "t"."p_partkey"
FETCH NEXT 100 ROWS ONLY;
