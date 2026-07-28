SELECT "customer"."c_customer_sk", "customer"."c_first_name", "customer"."c_last_name", COUNT(*) AS "cnt"
FROM "store_sales",
    "store_returns",
    "web_sales",
    "date_dim",
    "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0"),
    "item",
    "customer",
    "customer_address",
    "household_demographics"
WHERE "store_sales"."ss_ticket_number" = "store_returns"."sr_ticket_number" AND "store_sales"."ss_customer_sk" = "web_sales"."ws_bill_customer_sk" AND ("store_sales"."ss_customer_sk" = "customer"."c_customer_sk" AND ("customer"."c_current_addr_sk" = "customer_address"."ca_address_sk" AND "customer"."c_current_hdemo_sk" = "household_demographics"."hd_demo_sk")) AND ("store_sales"."ss_item_sk" = "store_returns"."sr_item_sk" AND "store_returns"."sr_item_sk" = "web_sales"."ws_item_sk" AND ("item"."i_item_sk" = "store_sales"."ss_item_sk" AND (("item"."i_category" = 'Electronics' OR "item"."i_category" = 'Shoes' OR "item"."i_category" = 'Sports') AND "store_returns"."sr_returned_date_sk" = "date_dim"."d_date_sk"))) AND ("web_sales"."ws_sold_date_sk" = "date_dim0"."d_date_sk0" AND "date_dim0"."d_date0" >= "date_dim"."d_date" AND ("date_dim0"."d_date0" <= ("date_dim"."d_date" + INTERVAL '90' DAY) AND (("customer_address"."ca_state" = 'GA' OR "customer_address"."ca_state" = 'KS' OR "customer_address"."ca_state" = 'LA' OR "customer_address"."ca_state" = 'ME' OR "customer_address"."ca_state" = 'NC') AND "date_dim"."d_year" = 1999)) AND ("household_demographics"."hd_income_band_sk" >= 2 AND "household_demographics"."hd_income_band_sk" <= 8 AND ("household_demographics"."hd_buy_potential" = '501-1000' AND ("store_sales"."ss_sales_price" / "store_sales"."ss_list_price" >= 73 * 0.01 AND "store_sales"."ss_sales_price" / "store_sales"."ss_list_price" <= 93 * 0.01))))
GROUP BY "customer"."c_customer_sk", "customer"."c_first_name", "customer"."c_last_name"
ORDER BY 4;
