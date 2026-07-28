SELECT "store"."s_store_name", "item"."i_item_desc", "t4"."revenue", "item"."i_current_price", "item"."i_wholesale_cost", "item"."i_brand"
FROM "store",
    "item",
        (SELECT "t0"."ss_store_sk", AVG("t0"."revenue") AS "ave"
        FROM (SELECT "store_sales"."ss_item_sk", "store_sales"."ss_store_sk", SUM("store_sales"."ss_sales_price") AS "revenue"
                FROM "store_sales",
                    "date_dim"
                WHERE "store_sales"."ss_sold_date_sk" = "date_dim"."d_date_sk" AND "date_dim"."d_month_seq" >= 1207 AND "date_dim"."d_month_seq" <= 1207 + 11 AND "store_sales"."ss_sales_price" / "store_sales"."ss_list_price" >= 41 * 0.01 AND "store_sales"."ss_sales_price" / "store_sales"."ss_list_price" <= 51 * 0.01
                GROUP BY "store_sales"."ss_item_sk", "store_sales"."ss_store_sk") AS "t0"
        GROUP BY "t0"."ss_store_sk") AS "t1",
        (SELECT "store_sales0"."ss_store_sk0", "store_sales0"."ss_item_sk0", SUM("store_sales0"."ss_sales_price0") AS "revenue"
        FROM "store_sales" AS "store_sales0" ("ss_sold_date_sk0", "ss_sold_time_sk0", "ss_item_sk0", "ss_customer_sk0", "ss_cdemo_sk0", "ss_hdemo_sk0", "ss_addr_sk0", "ss_store_sk0", "ss_promo_sk0", "ss_ticket_number0", "ss_quantity0", "ss_wholesale_cost0", "ss_list_price0", "ss_sales_price0", "ss_ext_discount_amt0", "ss_ext_sales_price0", "ss_ext_wholesale_cost0", "ss_ext_list_price0", "ss_ext_tax0", "ss_coupon_amt0", "ss_net_paid0", "ss_net_paid_inc_tax0", "ss_net_profit0"),
            "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0")
        WHERE "store_sales0"."ss_sold_date_sk0" = "date_dim0"."d_date_sk0" AND "date_dim0"."d_month_seq0" >= 1207 AND "date_dim0"."d_month_seq0" <= 1207 + 11 AND "store_sales0"."ss_sales_price0" / "store_sales0"."ss_list_price0" >= 41 * 0.01 AND "store_sales0"."ss_sales_price0" / "store_sales0"."ss_list_price0" <= 51 * 0.01
        GROUP BY "store_sales0"."ss_item_sk0", "store_sales0"."ss_store_sk0") AS "t4"
WHERE "t1"."ss_store_sk" = "t4"."ss_store_sk0" AND ("t4"."revenue" <= 0.1 * "t1"."ave" AND "store"."s_store_sk" = "t4"."ss_store_sk0") AND ("item"."i_item_sk" = "t4"."ss_item_sk0" AND "item"."i_manager_id" >= 54 AND ("item"."i_manager_id" <= 58 AND ("store"."s_state" = 'IA' OR "store"."s_state" = 'IL' OR "store"."s_state" = 'MI')))
ORDER BY "store"."s_store_name", "item"."i_item_desc"
FETCH NEXT 100 ROWS ONLY;
