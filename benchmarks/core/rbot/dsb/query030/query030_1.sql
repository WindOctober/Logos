SELECT "t6"."c_customer_id", "t6"."c_salutation", "t6"."c_first_name", "t6"."c_last_name", "t6"."c_preferred_cust_flag", "t6"."c_birth_day", "t6"."c_birth_month", "t6"."c_birth_year", "t6"."c_birth_country", "t6"."c_login", "t6"."c_email_address", "t6"."c_last_review_date_sk", "t4"."ctr_total_return"
FROM (SELECT "t"."wr_returning_customer_sk" AS "ctr_customer_sk", "customer_address"."ca_state" AS "ctr_state", "t"."wr_reason_sk" AS "ctr_reason_sk", SUM("t"."wr_return_amt") AS "ctr_total_return"
        FROM (SELECT *
                FROM "web_returns"
                WHERE "wr_return_amt" / "wr_return_quantity" >= 271 AND "wr_return_amt" / "wr_return_quantity" <= 300) AS "t"
            INNER JOIN (SELECT *
                FROM "date_dim"
                WHERE "d_year" = 2000) AS "t0" ON "t"."wr_returned_date_sk" = "t0"."d_date_sk"
            INNER JOIN "customer_address" ON "t"."wr_returning_addr_sk" = "customer_address"."ca_address_sk"
            INNER JOIN (SELECT *
                FROM "item"
                WHERE "i_manager_id" >= 91 AND "i_manager_id" <= 100) AS "t1" ON "t"."wr_item_sk" = "t1"."i_item_sk"
        GROUP BY "t"."wr_returning_customer_sk", "customer_address"."ca_state", "t"."wr_reason_sk"
        HAVING "t"."wr_reason_sk" IN (15, 50)) AS "t4"
    CROSS JOIN (SELECT *
        FROM "customer_address" AS "customer_address0" ("ca_address_sk0", "ca_address_id0", "ca_street_number0", "ca_street_name0", "ca_street_type0", "ca_suite_number0", "ca_city0", "ca_county0", "ca_state0", "ca_zip0", "ca_country0", "ca_gmt_offset0", "ca_location_type0")
        WHERE CAST("ca_state0" AS CHAR(2)) IN ('MO', 'OH', 'OK', 'SD')) AS "t5"
    INNER JOIN (SELECT *
        FROM "customer"
        WHERE "c_birth_year" >= 1987 AND "c_birth_year" <= 1993) AS "t6" ON "t5"."ca_address_sk0" = "t6"."c_current_addr_sk" AND "t4"."ctr_customer_sk" = "t6"."c_customer_sk"
    INNER JOIN (SELECT "t13"."ca_state1", AVG("t13"."ctr_total_return") AS "$f1"
        FROM (SELECT "customer_address1"."ca_state1", SUM("t7"."wr_return_amt0") AS "ctr_total_return"
                FROM (SELECT *
                        FROM "web_returns" AS "web_returns0" ("wr_returned_date_sk0", "wr_returned_time_sk0", "wr_item_sk0", "wr_refunded_customer_sk0", "wr_refunded_cdemo_sk0", "wr_refunded_hdemo_sk0", "wr_refunded_addr_sk0", "wr_returning_customer_sk0", "wr_returning_cdemo_sk0", "wr_returning_hdemo_sk0", "wr_returning_addr_sk0", "wr_web_page_sk0", "wr_reason_sk0", "wr_order_number0", "wr_return_quantity0", "wr_return_amt0", "wr_return_tax0", "wr_return_amt_inc_tax0", "wr_fee0", "wr_return_ship_cost0", "wr_refunded_cash0", "wr_reversed_charge0", "wr_account_credit0", "wr_net_loss0")
                        WHERE "wr_return_amt0" / "wr_return_quantity0" >= 271 AND "wr_return_amt0" / "wr_return_quantity0" <= 300) AS "t7"
                    INNER JOIN (SELECT *
                        FROM "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0")
                        WHERE "d_year0" = 2000) AS "t8" ON "t7"."wr_returned_date_sk0" = "t8"."d_date_sk0"
                    INNER JOIN "customer_address" AS "customer_address1" ("ca_address_sk1", "ca_address_id1", "ca_street_number1", "ca_street_name1", "ca_street_type1", "ca_suite_number1", "ca_city1", "ca_county1", "ca_state1", "ca_zip1", "ca_country1", "ca_gmt_offset1", "ca_location_type1") ON "t7"."wr_returning_addr_sk0" = "customer_address1"."ca_address_sk1"
                    INNER JOIN (SELECT *
                        FROM "item" AS "item0" ("i_item_sk0", "i_item_id0", "i_rec_start_date0", "i_rec_end_date0", "i_item_desc0", "i_current_price0", "i_wholesale_cost0", "i_brand_id0", "i_brand0", "i_class_id0", "i_class0", "i_category_id0", "i_category0", "i_manufact_id0", "i_manufact0", "i_size0", "i_formulation0", "i_color0", "i_units0", "i_container0", "i_manager_id0", "i_product_name0")
                        WHERE "i_manager_id0" >= 91 AND "i_manager_id0" <= 100) AS "t9" ON "t7"."wr_item_sk0" = "t9"."i_item_sk0"
                GROUP BY "t7"."wr_returning_customer_sk0", "customer_address1"."ca_state1", "t7"."wr_reason_sk0"
                HAVING "customer_address1"."ca_state1" IS NOT NULL) AS "t13"
        GROUP BY "t13"."ca_state1") AS "t14" ON "t4"."ctr_state" = "t14"."ca_state1" AND "t4"."ctr_total_return" > "t14"."$f1" * 1.2
ORDER BY "t6"."c_customer_id", "t6"."c_salutation", "t6"."c_first_name", "t6"."c_last_name", "t6"."c_preferred_cust_flag", "t6"."c_birth_day", "t6"."c_birth_month", "t6"."c_birth_year", "t6"."c_birth_country", "t6"."c_login", "t6"."c_email_address", "t6"."c_last_review_date_sk", "t4"."ctr_total_return"
FETCH NEXT 100 ROWS ONLY;
