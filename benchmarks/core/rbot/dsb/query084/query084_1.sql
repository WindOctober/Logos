SELECT "customer"."c_customer_id" AS "customer_id", CASE WHEN "customer"."c_last_name" IS NOT NULL THEN CAST("customer"."c_last_name" AS CHAR) ELSE '' END || ', ' || CASE WHEN "customer"."c_first_name" IS NOT NULL THEN CAST("customer"."c_first_name" AS CHAR) ELSE '' END AS "customername"
FROM "customer"
    INNER JOIN (SELECT *
        FROM "customer_address"
        WHERE "ca_city" = 'Marion') AS "t" ON "customer"."c_current_addr_sk" = "t"."ca_address_sk"
    INNER JOIN "customer_demographics" ON "customer"."c_current_cdemo_sk" = "customer_demographics"."cd_demo_sk"
    INNER JOIN "household_demographics" ON "customer"."c_current_hdemo_sk" = "household_demographics"."hd_demo_sk"
    INNER JOIN (SELECT *
        FROM "income_band"
        WHERE "ib_lower_bound" >= 26340 AND "ib_upper_bound" <= 26340 + 50000) AS "t0" ON "household_demographics"."hd_income_band_sk" = "t0"."ib_income_band_sk"
    INNER JOIN "store_returns" ON "customer_demographics"."cd_demo_sk" = "store_returns"."sr_cdemo_sk"
ORDER BY "customer"."c_customer_id"
FETCH NEXT 100 ROWS ONLY;
