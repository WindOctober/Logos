SELECT SUBSTRING("warehouse"."w_warehouse_name", 1, 20), "ship_mode"."sm_type", "call_center"."cc_name", COALESCE(SUM(CASE WHEN "catalog_sales"."cs_ship_date_sk" - "catalog_sales"."cs_sold_date_sk" <= 30 THEN 1 ELSE 0 END), 0) AS "30 days", COALESCE(SUM(CASE WHEN "catalog_sales"."cs_ship_date_sk" - "catalog_sales"."cs_sold_date_sk" > 30 AND "catalog_sales"."cs_ship_date_sk" - "catalog_sales"."cs_sold_date_sk" <= 60 THEN 1 ELSE 0 END), 0) AS "31-60 days", COALESCE(SUM(CASE WHEN "catalog_sales"."cs_ship_date_sk" - "catalog_sales"."cs_sold_date_sk" > 60 AND "catalog_sales"."cs_ship_date_sk" - "catalog_sales"."cs_sold_date_sk" <= 90 THEN 1 ELSE 0 END), 0) AS "61-90 days", COALESCE(SUM(CASE WHEN "catalog_sales"."cs_ship_date_sk" - "catalog_sales"."cs_sold_date_sk" > 90 AND "catalog_sales"."cs_ship_date_sk" - "catalog_sales"."cs_sold_date_sk" <= 120 THEN 1 ELSE 0 END), 0) AS "91-120 days", COALESCE(SUM(CASE WHEN "catalog_sales"."cs_ship_date_sk" - "catalog_sales"."cs_sold_date_sk" > 120 THEN 1 ELSE 0 END), 0) AS ">120 days"
FROM "catalog_sales",
    "warehouse",
    "ship_mode",
    "call_center",
    "date_dim"
WHERE "date_dim"."d_month_seq" >= 1201 AND "date_dim"."d_month_seq" <= 1201 + 23 AND ("catalog_sales"."cs_ship_date_sk" = "date_dim"."d_date_sk" AND ("catalog_sales"."cs_warehouse_sk" = "warehouse"."w_warehouse_sk" AND "catalog_sales"."cs_ship_mode_sk" = "ship_mode"."sm_ship_mode_sk")) AND ("catalog_sales"."cs_call_center_sk" = "call_center"."cc_call_center_sk" AND ("catalog_sales"."cs_list_price" >= 248 AND "catalog_sales"."cs_list_price" <= 277) AND ("ship_mode"."sm_type" = 'LIBRARY' AND ("call_center"."cc_class" = 'small' AND CAST("warehouse"."w_gmt_offset" AS DECIMAL(12, 2)) = -5)))
GROUP BY SUBSTRING("warehouse"."w_warehouse_name", 1, 20), "ship_mode"."sm_type", "call_center"."cc_name"
ORDER BY 1, "ship_mode"."sm_type", "call_center"."cc_name"
FETCH NEXT 100 ROWS ONLY;
