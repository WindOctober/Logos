SELECT 100.00 * CASE WHEN COUNT(*) = 0 THEN NULL ELSE COALESCE(SUM(CASE WHEN "part"."p_type" LIKE 'PROMO%' THEN "lineitem"."l_extendedprice" * (1 - "lineitem"."l_discount") ELSE 0 END), 0) END / CASE WHEN COUNT(*) = 0 THEN NULL ELSE COALESCE(SUM("lineitem"."l_extendedprice" * (1 - "lineitem"."l_discount")), 0) END AS "promo_revenue"
FROM "lineitem",
    "part"
WHERE "lineitem"."l_partkey" = "part"."p_partkey" AND "lineitem"."l_shipdate" >= DATE '1995-10-01' AND "lineitem"."l_shipdate" < (DATE '1995-10-01' + INTERVAL '1' MONTH)
FETCH NEXT 1 ROWS ONLY;
