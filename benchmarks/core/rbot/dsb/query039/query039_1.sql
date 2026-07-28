SELECT "t3"."w_warehouse_sk", "t3"."i_item_sk", "t3"."d_moy", "t3"."mean", "t3"."cov", "t8"."w_warehouse_sk0", "t8"."i_item_sk0", "t8"."d_moy0", "t8"."mean" AS "mean0", "t8"."cov" AS "cov0"
FROM (SELECT "w_warehouse_name", "w_warehouse_sk", "i_item_sk", "d_moy", "stdev", "mean", CASE WHEN "mean" = 0 THEN NULL ELSE "stdev" / "mean" END AS "cov"
        FROM (SELECT "warehouse"."w_warehouse_name", "warehouse"."w_warehouse_sk", "item"."i_item_sk", "date_dim"."d_moy", STDDEV_SAMP("inventory"."inv_quantity_on_hand") AS "stdev", AVG("inventory"."inv_quantity_on_hand") AS "mean"
                FROM "inventory",
                    "item",
                    "warehouse",
                    "date_dim"
                WHERE "inventory"."inv_item_sk" = "item"."i_item_sk" AND "inventory"."inv_warehouse_sk" = "warehouse"."w_warehouse_sk" AND ("inventory"."inv_date_sk" = "date_dim"."d_date_sk" AND "date_dim"."d_year" = 1999) AND (("item"."i_category" = 'Books' OR "item"."i_category" = 'Shoes') AND "item"."i_manager_id" >= 81 AND ("item"."i_manager_id" <= 100 AND ("inventory"."inv_quantity_on_hand" >= 800 AND "inventory"."inv_quantity_on_hand" <= 1000)))
                GROUP BY "item"."i_item_sk", "warehouse"."w_warehouse_sk", "warehouse"."w_warehouse_name", "date_dim"."d_moy") AS "t1"
        WHERE CASE WHEN "t1"."mean" = 0 THEN 0 ELSE "t1"."stdev" / "t1"."mean" END > 1) AS "t3",
        (SELECT "w_warehouse_name0", "w_warehouse_sk0", "i_item_sk0", "d_moy0", "stdev", "mean", CASE WHEN "mean" = 0 THEN NULL ELSE "stdev" / "mean" END AS "cov"
        FROM (SELECT "warehouse0"."w_warehouse_name0", "warehouse0"."w_warehouse_sk0", "item0"."i_item_sk0", "date_dim0"."d_moy0", STDDEV_SAMP("inventory0"."inv_quantity_on_hand0") AS "stdev", AVG("inventory0"."inv_quantity_on_hand0") AS "mean"
                FROM "inventory" AS "inventory0" ("inv_date_sk0", "inv_item_sk0", "inv_warehouse_sk0", "inv_quantity_on_hand0"),
                    "item" AS "item0" ("i_item_sk0", "i_item_id0", "i_rec_start_date0", "i_rec_end_date0", "i_item_desc0", "i_current_price0", "i_wholesale_cost0", "i_brand_id0", "i_brand0", "i_class_id0", "i_class0", "i_category_id0", "i_category0", "i_manufact_id0", "i_manufact0", "i_size0", "i_formulation0", "i_color0", "i_units0", "i_container0", "i_manager_id0", "i_product_name0"),
                    "warehouse" AS "warehouse0" ("w_warehouse_sk0", "w_warehouse_id0", "w_warehouse_name0", "w_warehouse_sq_ft0", "w_street_number0", "w_street_name0", "w_street_type0", "w_suite_number0", "w_city0", "w_county0", "w_state0", "w_zip0", "w_country0", "w_gmt_offset0"),
                    "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0")
                WHERE "inventory0"."inv_item_sk0" = "item0"."i_item_sk0" AND "inventory0"."inv_warehouse_sk0" = "warehouse0"."w_warehouse_sk0" AND ("inventory0"."inv_date_sk0" = "date_dim0"."d_date_sk0" AND "date_dim0"."d_year0" = 1999) AND (("item0"."i_category0" = 'Books' OR "item0"."i_category0" = 'Shoes') AND "item0"."i_manager_id0" >= 81 AND ("item0"."i_manager_id0" <= 100 AND ("inventory0"."inv_quantity_on_hand0" >= 800 AND "inventory0"."inv_quantity_on_hand0" <= 1000)))
                GROUP BY "item0"."i_item_sk0", "warehouse0"."w_warehouse_sk0", "warehouse0"."w_warehouse_name0", "date_dim0"."d_moy0") AS "t6"
        WHERE CASE WHEN "t6"."mean" = 0 THEN 0 ELSE "t6"."stdev" / "t6"."mean" END > 1) AS "t8"
WHERE "t3"."i_item_sk" = "t8"."i_item_sk0" AND "t3"."w_warehouse_sk" = "t8"."w_warehouse_sk0" AND "t3"."d_moy" = 7 AND "t8"."d_moy0" = 7 + 1
ORDER BY "t3"."w_warehouse_sk", "t3"."i_item_sk", "t3"."d_moy", "t3"."mean", "t3"."cov", "t8"."d_moy0", "t8"."mean", "t8"."cov";
