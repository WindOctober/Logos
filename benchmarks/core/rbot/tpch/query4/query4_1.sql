SELECT "o_orderpriority", COUNT(*) AS "order_count"
FROM "orders"
WHERE "o_orderdate" >= DATE '1997-04-01' AND "o_orderdate" < (DATE '1997-04-01' + INTERVAL '3' MONTH) AND EXISTS (SELECT *
        FROM "lineitem"
        WHERE "l_orderkey" = "orders"."o_orderkey" AND "l_commitdate" < "l_receiptdate")
GROUP BY "o_orderpriority"
ORDER BY "o_orderpriority"
FETCH NEXT 1 ROWS ONLY;
