SELECT "t"."EXPR$1", COUNT(*) AS "custdist"
FROM (SELECT "customer"."c_custkey", COUNT("orders"."o_orderkey") AS "EXPR$1"
        FROM "customer"
            LEFT JOIN "orders" ON "customer"."c_custkey" = "orders"."o_custkey" AND "orders"."o_comment" NOT LIKE '%pending%accounts%'
        GROUP BY "customer"."c_custkey") AS "t"
GROUP BY "t"."EXPR$1"
ORDER BY 2 DESC, "t"."EXPR$1" DESC
FETCH NEXT 1 ROWS ONLY;
