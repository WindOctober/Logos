SELECT "lineitem"."l_shipmode", COALESCE(SUM(CASE WHEN "orders"."o_orderpriority" = '1-URGENT' OR "orders"."o_orderpriority" = '2-HIGH' THEN 1 ELSE 0 END), 0) AS "high_line_count", COALESCE(SUM(CASE WHEN "orders"."o_orderpriority" <> '1-URGENT' AND "orders"."o_orderpriority" <> '2-HIGH' THEN 1 ELSE 0 END), 0) AS "low_line_count"
FROM "orders",
    "lineitem"
WHERE "orders"."o_orderkey" = "lineitem"."l_orderkey" AND (("lineitem"."l_shipmode" = 'SHIP' OR "lineitem"."l_shipmode" = 'RAIL') AND "lineitem"."l_commitdate" < "lineitem"."l_receiptdate") AND ("lineitem"."l_shipdate" < "lineitem"."l_commitdate" AND ("lineitem"."l_receiptdate" >= DATE '1995-01-01' AND "lineitem"."l_receiptdate" < (DATE '1995-01-01' + INTERVAL '1' YEAR)))
GROUP BY "lineitem"."l_shipmode"
ORDER BY "lineitem"."l_shipmode"
FETCH NEXT 1 ROWS ONLY;
