SELECT "t3"."p_brand", "t3"."p_type", "t3"."p_size", COUNT("t3"."ps_suppkey") AS "supplier_cnt"
FROM (SELECT "part"."p_brand", "part"."p_type", "part"."p_size", "partsupp"."ps_suppkey"
        FROM "partsupp",
            "part"
        WHERE "part"."p_partkey" = "partsupp"."ps_partkey" AND "part"."p_brand" <> 'Brand#42' AND "part"."p_type" NOT LIKE 'MEDIUM PLATED%' AND ("part"."p_size" = 43 OR "part"."p_size" = 45 OR ("part"."p_size" = 15 OR "part"."p_size" = 11) OR ("part"."p_size" = 40 OR "part"."p_size" = 35 OR ("part"."p_size" = 28 OR "part"."p_size" = 46))) AND "partsupp"."ps_suppkey" NOT IN (SELECT "s_suppkey"
                    FROM "supplier"
                    WHERE "s_comment" LIKE '%Customer%Complaints%')
        GROUP BY "part"."p_brand", "part"."p_type", "part"."p_size", "partsupp"."ps_suppkey") AS "t3"
GROUP BY "t3"."p_brand", "t3"."p_type", "t3"."p_size"
ORDER BY 4 DESC, "t3"."p_brand", "t3"."p_type", "t3"."p_size"
FETCH NEXT 1 ROWS ONLY;
