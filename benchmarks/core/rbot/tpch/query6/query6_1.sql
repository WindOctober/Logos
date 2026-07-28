SELECT CASE WHEN COUNT(*) = 0 THEN NULL ELSE COALESCE(SUM("l_extendedprice" * "l_discount"), 0) END AS "revenue"
FROM "lineitem"
WHERE "l_shipdate" >= DATE '1994-01-01' AND "l_shipdate" < (DATE '1994-01-01' + INTERVAL '1' YEAR) AND "l_discount" >= 0.06 - 0.01 AND "l_discount" <= 0.06 + 0.01 AND "l_quantity" < 24
FETCH NEXT 1 ROWS ONLY;
