SELECT "customer"."c_customer_id", "customer"."c_salutation", "customer"."c_first_name", "customer"."c_last_name", "t2"."ca_street_number0", "t2"."ca_street_name0", "t2"."ca_street_type0", "t2"."ca_suite_number0", "t2"."ca_city0", "t2"."ca_county0", "t2"."ca_state0", "t2"."ca_zip0", "t2"."ca_country0", "t2"."ca_gmt_offset0", "t2"."ca_location_type0", "t1"."ctr_total_return"
FROM (SELECT "catalog_returns"."cr_returning_customer_sk" AS "ctr_customer_sk", "customer_address"."ca_state" AS "ctr_state", SUM("catalog_returns"."cr_return_amt_inc_tax") AS "ctr_total_return"
        FROM "catalog_returns"
            INNER JOIN (SELECT *
                FROM "date_dim"
                WHERE "d_year" = 2002) AS "t" ON "catalog_returns"."cr_returned_date_sk" = "t"."d_date_sk"
            INNER JOIN "customer_address" ON "catalog_returns"."cr_returning_addr_sk" = "customer_address"."ca_address_sk"
        GROUP BY "catalog_returns"."cr_returning_customer_sk", "customer_address"."ca_state") AS "t1"
    CROSS JOIN (SELECT *
        FROM "customer_address" AS "customer_address0" ("ca_address_sk0", "ca_address_id0", "ca_street_number0", "ca_street_name0", "ca_street_type0", "ca_suite_number0", "ca_city0", "ca_county0", "ca_state0", "ca_zip0", "ca_country0", "ca_gmt_offset0", "ca_location_type0")
        WHERE "ca_state0" = 'MI') AS "t2"
    INNER JOIN "customer" ON "t2"."ca_address_sk0" = "customer"."c_current_addr_sk" AND "t1"."ctr_customer_sk" = "customer"."c_customer_sk"
    INNER JOIN (SELECT "t7"."ca_state1", AVG("t7"."ctr_total_return") AS "$f1"
        FROM (SELECT "customer_address1"."ca_state1", SUM("catalog_returns0"."cr_return_amt_inc_tax0") AS "ctr_total_return"
                FROM "catalog_returns" AS "catalog_returns0" ("cr_returned_date_sk0", "cr_returned_time_sk0", "cr_item_sk0", "cr_refunded_customer_sk0", "cr_refunded_cdemo_sk0", "cr_refunded_hdemo_sk0", "cr_refunded_addr_sk0", "cr_returning_customer_sk0", "cr_returning_cdemo_sk0", "cr_returning_hdemo_sk0", "cr_returning_addr_sk0", "cr_call_center_sk0", "cr_catalog_page_sk0", "cr_ship_mode_sk0", "cr_warehouse_sk0", "cr_reason_sk0", "cr_order_number0", "cr_return_quantity0", "cr_return_amount0", "cr_return_tax0", "cr_return_amt_inc_tax0", "cr_fee0", "cr_return_ship_cost0", "cr_refunded_cash0", "cr_reversed_charge0", "cr_store_credit0", "cr_net_loss0")
                    INNER JOIN (SELECT *
                        FROM "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0")
                        WHERE "d_year0" = 2002) AS "t3" ON "catalog_returns0"."cr_returned_date_sk0" = "t3"."d_date_sk0"
                    INNER JOIN "customer_address" AS "customer_address1" ("ca_address_sk1", "ca_address_id1", "ca_street_number1", "ca_street_name1", "ca_street_type1", "ca_suite_number1", "ca_city1", "ca_county1", "ca_state1", "ca_zip1", "ca_country1", "ca_gmt_offset1", "ca_location_type1") ON "catalog_returns0"."cr_returning_addr_sk0" = "customer_address1"."ca_address_sk1"
                GROUP BY "catalog_returns0"."cr_returning_customer_sk0", "customer_address1"."ca_state1"
                HAVING "customer_address1"."ca_state1" IS NOT NULL) AS "t7"
        GROUP BY "t7"."ca_state1") AS "t8" ON "t1"."ctr_state" = "t8"."ca_state1" AND "t1"."ctr_total_return" > "t8"."$f1" * 1.2
ORDER BY "customer"."c_customer_id", "customer"."c_salutation", "customer"."c_first_name", "customer"."c_last_name", "t2"."ca_street_number0", "t2"."ca_street_name0", "t2"."ca_street_type0", "t2"."ca_suite_number0", "t2"."ca_city0", "t2"."ca_county0", "t2"."ca_state0", "t2"."ca_zip0", "t2"."ca_country0", "t2"."ca_gmt_offset0", "t2"."ca_location_type0", "t1"."ctr_total_return"
FETCH NEXT 100 ROWS ONLY;
