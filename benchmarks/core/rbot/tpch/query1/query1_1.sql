SELECT "l_returnflag", "l_linestatus", COALESCE(SUM("l_quantity"), 0) AS "sum_qty", COALESCE(SUM("l_extendedprice"), 0) AS "sum_base_price", COALESCE(SUM("l_extendedprice" * (1 - "l_discount")), 0) AS "sum_disc_price", COALESCE(SUM("l_extendedprice" * (1 - "l_discount") * (1 + "l_tax")), 0) AS "sum_charge", CAST(CAST(COALESCE(SUM("l_quantity"), 0) AS DECIMAL(15, 2)) / COUNT(*) AS DECIMAL(15, 2)) AS "avg_qty", CAST(CAST(COALESCE(SUM("l_extendedprice"), 0) AS DECIMAL(15, 2)) / COUNT(*) AS DECIMAL(15, 2)) AS "avg_price", CAST(CAST(COALESCE(SUM("l_discount"), 0) AS DECIMAL(15, 2)) / COUNT(*) AS DECIMAL(15, 2)) AS "avg_disc", COUNT(*) AS "count_order"
FROM "lineitem"
WHERE "l_shipdate" <= (DATE '1998-12-01' - INTERVAL '79' DAY)
GROUP BY "l_returnflag", "l_linestatus"
ORDER BY "l_returnflag", "l_linestatus"
FETCH NEXT 1 ROWS ONLY;
