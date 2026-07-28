SELECT "item"."i_item_id", "item"."i_item_desc", "store"."s_store_id", "store"."s_store_name", STDDEV_SAMP("store_sales"."ss_net_profit") AS "store_sales_profit", STDDEV_SAMP("store_returns"."sr_net_loss") AS "store_returns_loss", STDDEV_SAMP("catalog_sales"."cs_net_profit") AS "catalog_sales_profit"
FROM "store_sales",
    "store_returns",
    "catalog_sales",
    "date_dim",
    "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0"),
    "date_dim" AS "date_dim1" ("d_date_sk1", "d_date_id1", "d_date1", "d_month_seq1", "d_week_seq1", "d_quarter_seq1", "d_year1", "d_dow1", "d_moy1", "d_dom1", "d_qoy1", "d_fy_year1", "d_fy_quarter_seq1", "d_fy_week_seq1", "d_day_name1", "d_quarter_name1", "d_holiday1", "d_weekend1", "d_following_holiday1", "d_first_dom1", "d_last_dom1", "d_same_day_ly1", "d_same_day_lq1", "d_current_day1", "d_current_week1", "d_current_month1", "d_current_quarter1", "d_current_year1"),
    "store",
    "item"
WHERE "date_dim"."d_moy" = 7 AND "date_dim"."d_year" = 1998 AND ("date_dim"."d_date_sk" = "store_sales"."ss_sold_date_sk" AND "item"."i_item_sk" = "store_sales"."ss_item_sk") AND ("store"."s_store_sk" = "store_sales"."ss_store_sk" AND "store_sales"."ss_customer_sk" = "store_returns"."sr_customer_sk" AND ("store_sales"."ss_item_sk" = "store_returns"."sr_item_sk" AND ("store_sales"."ss_ticket_number" = "store_returns"."sr_ticket_number" AND "store_returns"."sr_returned_date_sk" = "date_dim0"."d_date_sk0"))) AND ("date_dim0"."d_moy0" >= 7 AND "date_dim0"."d_moy0" <= 7 + 2 AND ("date_dim0"."d_year0" = 1998 AND "store_returns"."sr_customer_sk" = "catalog_sales"."cs_bill_customer_sk") AND ("store_returns"."sr_item_sk" = "catalog_sales"."cs_item_sk" AND "catalog_sales"."cs_sold_date_sk" = "date_dim1"."d_date_sk1" AND ("date_dim1"."d_moy1" >= 7 AND ("date_dim1"."d_moy1" <= 7 + 2 AND "date_dim1"."d_year1" = 1998))))
GROUP BY "store"."s_store_id", "store"."s_store_name", "item"."i_item_id", "item"."i_item_desc"
ORDER BY "item"."i_item_id", "item"."i_item_desc", "store"."s_store_id", "store"."s_store_name"
FETCH NEXT 100 ROWS ONLY;
