SELECT "item"."i_item_sk", "item0"."i_item_sk0", COUNT(*) AS "cnt"
FROM "item",
    "item" AS "item0" ("i_item_sk0", "i_item_id0", "i_rec_start_date0", "i_rec_end_date0", "i_item_desc0", "i_current_price0", "i_wholesale_cost0", "i_brand_id0", "i_brand0", "i_class_id0", "i_class0", "i_category_id0", "i_category0", "i_manufact_id0", "i_manufact0", "i_size0", "i_formulation0", "i_color0", "i_units0", "i_container0", "i_manager_id0", "i_product_name0"),
    "store_sales",
    "store_sales" AS "store_sales0" ("ss_sold_date_sk0", "ss_sold_time_sk0", "ss_item_sk0", "ss_customer_sk0", "ss_cdemo_sk0", "ss_hdemo_sk0", "ss_addr_sk0", "ss_store_sk0", "ss_promo_sk0", "ss_ticket_number0", "ss_quantity0", "ss_wholesale_cost0", "ss_list_price0", "ss_sales_price0", "ss_ext_discount_amt0", "ss_ext_sales_price0", "ss_ext_wholesale_cost0", "ss_ext_list_price0", "ss_ext_tax0", "ss_coupon_amt0", "ss_net_paid0", "ss_net_paid_inc_tax0", "ss_net_profit0"),
    "date_dim",
    "customer",
    "customer_address",
    "customer_demographics"
WHERE "item"."i_item_sk" < "item0"."i_item_sk0" AND "store_sales"."ss_ticket_number" = "store_sales0"."ss_ticket_number0" AND ("store_sales"."ss_item_sk" = "item"."i_item_sk" AND "store_sales0"."ss_item_sk0" = "item0"."i_item_sk0") AND ("store_sales"."ss_customer_sk" = "customer"."c_customer_sk" AND "customer"."c_current_addr_sk" = "customer_address"."ca_address_sk" AND ("customer"."c_current_cdemo_sk" = "customer_demographics"."cd_demo_sk" AND ("date_dim"."d_year" >= 2000 AND "date_dim"."d_year" <= 2000 + 1))) AND ("date_dim"."d_date_sk" = "store_sales"."ss_sold_date_sk" AND ("item"."i_category" = 'Books' OR "item"."i_category" = 'Shoes') AND ("item0"."i_manager_id0" >= 48 AND ("item0"."i_manager_id0" <= 67 AND "customer_demographics"."cd_marital_status" = 'W')) AND ("customer_demographics"."cd_education_status" = '4 yr Degree' AND "store_sales"."ss_list_price" >= 80 AND ("store_sales"."ss_list_price" <= 94 AND ("store_sales0"."ss_list_price0" >= 80 AND "store_sales0"."ss_list_price0" <= 94))))
GROUP BY "item"."i_item_sk", "item0"."i_item_sk0"
ORDER BY 3;
