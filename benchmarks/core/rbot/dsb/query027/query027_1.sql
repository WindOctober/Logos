SELECT "item"."i_item_id", "store"."s_state", GROUPING("store"."s_state") AS "g_state", AVG("store_sales"."ss_quantity") AS "agg1", AVG("store_sales"."ss_list_price") AS "agg2", AVG("store_sales"."ss_coupon_amt") AS "agg3", AVG("store_sales"."ss_sales_price") AS "agg4"
FROM "store_sales",
    "customer_demographics",
    "date_dim",
    "store",
    "item"
WHERE "store_sales"."ss_sold_date_sk" = "date_dim"."d_date_sk" AND "store_sales"."ss_item_sk" = "item"."i_item_sk" AND ("store_sales"."ss_store_sk" = "store"."s_store_sk" AND ("store_sales"."ss_cdemo_sk" = "customer_demographics"."cd_demo_sk" AND "customer_demographics"."cd_gender" = 'F')) AND ("customer_demographics"."cd_marital_status" = 'S' AND "customer_demographics"."cd_education_status" = 'Unknown' AND ("date_dim"."d_year" = 2001 AND ("store"."s_state" = 'MI' AND "item"."i_category" = 'Books')))
GROUP BY ROLLUP("item"."i_item_id", "store"."s_state")
ORDER BY "item"."i_item_id", "store"."s_state"
FETCH NEXT 100 ROWS ONLY;
