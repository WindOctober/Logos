SELECT "partsupp"."ps_partkey", COALESCE(SUM("partsupp"."ps_supplycost" * "partsupp"."ps_availqty"), 0) AS "value"
FROM "partsupp",
    "supplier",
    "nation"
WHERE "partsupp"."ps_suppkey" = "supplier"."s_suppkey" AND "supplier"."s_nationkey" = "nation"."n_nationkey" AND "nation"."n_name" = 'INDIA'
GROUP BY "partsupp"."ps_partkey"
HAVING COALESCE(SUM("partsupp"."ps_supplycost" * "partsupp"."ps_availqty"), 0) > (((SELECT SUM("partsupp0"."ps_supplycost0" * "partsupp0"."ps_availqty0") * 0.0000100000
                FROM "partsupp" AS "partsupp0" ("ps_partkey0", "ps_suppkey0", "ps_availqty0", "ps_supplycost0", "ps_comment0"),
                    "supplier" AS "supplier0" ("s_suppkey0", "s_name0", "s_address0", "s_nationkey0", "s_phone0", "s_acctbal0", "s_comment0"),
                    "nation" AS "nation0" ("n_nationkey0", "n_name0", "n_regionkey0", "n_comment0")
                WHERE "partsupp0"."ps_suppkey0" = "supplier0"."s_suppkey0" AND "supplier0"."s_nationkey0" = "nation0"."n_nationkey0" AND "nation0"."n_name0" = 'INDIA')))
ORDER BY 2 DESC
FETCH NEXT 1 ROWS ONLY;
