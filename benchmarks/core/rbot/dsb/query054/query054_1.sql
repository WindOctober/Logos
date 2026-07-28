SELECT "t12"."segment", COUNT(*) AS "num_customers", "t12"."segment" * 50 AS "segment_base"
FROM (SELECT CAST(SUM("store_sales"."ss_ext_sales_price") / 50 AS INTEGER) AS "segment"
        FROM (SELECT "customer"."c_customer_sk", "customer"."c_current_addr_sk"
                FROM (SELECT "cs_sold_date_sk" AS "sold_date_sk", "cs_bill_customer_sk" AS "customer_sk", "cs_item_sk" AS "item_sk", "cs_wholesale_cost" AS "wholesale_cost"
                            FROM "catalog_sales"
                            UNION ALL
                            SELECT "ws_sold_date_sk" AS "sold_date_sk", "ws_bill_customer_sk" AS "customer_sk", "ws_item_sk" AS "item_sk", "ws_wholesale_cost" AS "wholesale_cost"
                            FROM "web_sales") AS "t1",
                    "item",
                    "date_dim",
                    "customer"
                WHERE "t1"."sold_date_sk" = "date_dim"."d_date_sk" AND "t1"."item_sk" = "item"."i_item_sk" AND ("item"."i_category" = 'Home' AND ("item"."i_class" = 'furniture' AND "customer"."c_customer_sk" = "t1"."customer_sk")) AND ("date_dim"."d_moy" = 12 AND ("date_dim"."d_year" = 1999 AND "t1"."wholesale_cost" >= 70) AND ("t1"."wholesale_cost" <= 100 AND ("customer"."c_birth_year" >= 1980 AND "customer"."c_birth_year" <= 1993)))
                GROUP BY "customer"."c_customer_sk", "customer"."c_current_addr_sk") AS "t3",
            "store_sales",
            "customer_address",
            "store",
            "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0")
        WHERE "t3"."c_current_addr_sk" = "customer_address"."ca_address_sk" AND "customer_address"."ca_county" = "store"."s_county" AND ("customer_address"."ca_state" = "store"."s_state" AND ("store_sales"."ss_sold_date_sk" = "date_dim0"."d_date_sk0" AND "t3"."c_customer_sk" = "store_sales"."ss_customer_sk")) AND ("store_sales"."ss_wholesale_cost" >= 70 AND "store_sales"."ss_wholesale_cost" <= 100 AND (("store"."s_state" = 'GA' OR "store"."s_state" = 'IA' OR ("store"."s_state" = 'IL' OR ("store"."s_state" = 'KS' OR "store"."s_state" = 'LA')) OR ("store"."s_state" = 'ME' OR "store"."s_state" = 'MI' OR ("store"."s_state" = 'NC' OR ("store"."s_state" = 'ND' OR "store"."s_state" = 'OK')))) AND ("date_dim0"."d_month_seq0" >= (((SELECT "d_month_seq1" + 1
                                                    FROM "date_dim" AS "date_dim1" ("d_date_sk1", "d_date_id1", "d_date1", "d_month_seq1", "d_week_seq1", "d_quarter_seq1", "d_year1", "d_dow1", "d_moy1", "d_dom1", "d_qoy1", "d_fy_year1", "d_fy_quarter_seq1", "d_fy_week_seq1", "d_day_name1", "d_quarter_name1", "d_holiday1", "d_weekend1", "d_following_holiday1", "d_first_dom1", "d_last_dom1", "d_same_day_ly1", "d_same_day_lq1", "d_current_day1", "d_current_week1", "d_current_month1", "d_current_quarter1", "d_current_year1")
                                                    WHERE "d_year1" = 1999 AND "d_moy1" = 12
                                                    GROUP BY "d_month_seq1" + 1))) AND "date_dim0"."d_month_seq0" <= (((SELECT "d_month_seq2" + 3
                                                    FROM "date_dim" AS "date_dim2" ("d_date_sk2", "d_date_id2", "d_date2", "d_month_seq2", "d_week_seq2", "d_quarter_seq2", "d_year2", "d_dow2", "d_moy2", "d_dom2", "d_qoy2", "d_fy_year2", "d_fy_quarter_seq2", "d_fy_week_seq2", "d_day_name2", "d_quarter_name2", "d_holiday2", "d_weekend2", "d_following_holiday2", "d_first_dom2", "d_last_dom2", "d_same_day_ly2", "d_same_day_lq2", "d_current_day2", "d_current_week2", "d_current_month2", "d_current_quarter2", "d_current_year2")
                                                    WHERE "d_year2" = 1999 AND "d_moy2" = 12
                                                    GROUP BY "d_month_seq2" + 3))))))
        GROUP BY "t3"."c_customer_sk") AS "t12"
GROUP BY "t12"."segment"
ORDER BY "t12"."segment", 2
FETCH NEXT 100 ROWS ONLY;
