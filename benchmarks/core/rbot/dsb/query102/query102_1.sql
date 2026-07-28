SELECT "customer_demographics"."cd_gender", "customer_demographics"."cd_marital_status", "customer_demographics"."cd_education_status", "household_demographics"."hd_vehicle_count", COUNT(*) AS "cnt"
FROM "store_sales",
    "web_sales",
    "date_dim",
    "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0"),
    "customer",
    "inventory",
    "store",
    "warehouse",
    "item",
    "customer_demographics",
    "household_demographics",
    "customer_address"
WHERE "store_sales"."ss_item_sk" = "item"."i_item_sk" AND "web_sales"."ws_item_sk" = "store_sales"."ss_item_sk" AND ("store_sales"."ss_sold_date_sk" = "date_dim"."d_date_sk" AND ("web_sales"."ws_sold_date_sk" = "date_dim0"."d_date_sk0" AND "date_dim0"."d_date0" >= "date_dim"."d_date")) AND ("date_dim0"."d_date0" <= ("date_dim"."d_date" + INTERVAL '30' DAY) AND ("store_sales"."ss_customer_sk" = "customer"."c_customer_sk" AND "web_sales"."ws_bill_customer_sk" = "customer"."c_customer_sk") AND ("web_sales"."ws_warehouse_sk" = "inventory"."inv_warehouse_sk" AND ("web_sales"."ws_warehouse_sk" = "warehouse"."w_warehouse_sk" AND "inventory"."inv_item_sk" = "store_sales"."ss_item_sk"))) AND ("inventory"."inv_date_sk" = "store_sales"."ss_sold_date_sk" AND ("inventory"."inv_quantity_on_hand" >= "store_sales"."ss_quantity" AND "store"."s_state" = "warehouse"."w_state") AND (("item"."i_category" = 'Books' OR "item"."i_category" = 'Jewelry' OR "item"."i_category" = 'Shoes') AND (("item"."i_manager_id" = 2 OR "item"."i_manager_id" = 8 OR ("item"."i_manager_id" = 10 OR ("item"."i_manager_id" = 12 OR "item"."i_manager_id" = 14)) OR ("item"."i_manager_id" = 28 OR "item"."i_manager_id" = 58 OR ("item"."i_manager_id" = 77 OR ("item"."i_manager_id" = 93 OR "item"."i_manager_id" = 96)))) AND "customer"."c_current_cdemo_sk" = "customer_demographics"."cd_demo_sk")) AND ("customer"."c_current_hdemo_sk" = "household_demographics"."hd_demo_sk" AND ("customer"."c_current_addr_sk" = "customer_address"."ca_address_sk" AND ("customer_address"."ca_state" = 'AR' OR "customer_address"."ca_state" = 'GA' OR "customer_address"."ca_state" = 'IA' OR "customer_address"."ca_state" = 'MN' OR "customer_address"."ca_state" = 'NC')) AND ("date_dim"."d_year" = 1999 AND ("web_sales"."ws_wholesale_cost" >= 73 AND "web_sales"."ws_wholesale_cost" <= 93))))
GROUP BY "customer_demographics"."cd_gender", "customer_demographics"."cd_marital_status", "customer_demographics"."cd_education_status", "household_demographics"."hd_vehicle_count"
ORDER BY 5;
