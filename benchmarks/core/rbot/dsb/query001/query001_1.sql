SELECT "t5"."c_customer_id"
FROM (SELECT "t"."sr_customer_sk" AS "ctr_customer_sk", "t"."sr_store_sk" AS "ctr_store_sk", "t"."sr_reason_sk" AS "ctr_reason_sk", SUM("t"."sr_return_amt_inc_tax") AS "ctr_total_return"
        FROM (SELECT *
                FROM "store_returns"
                WHERE "sr_return_amt" / "sr_return_quantity" >= 80 AND "sr_return_amt" / "sr_return_quantity" <= 139) AS "t"
            INNER JOIN (SELECT *
                FROM "date_dim"
                WHERE "d_year" = 1999) AS "t0" ON "t"."sr_returned_date_sk" = "t0"."d_date_sk"
        GROUP BY "t"."sr_customer_sk", "t"."sr_store_sk", "t"."sr_reason_sk"
        HAVING "t"."sr_reason_sk" >= 72 AND "t"."sr_reason_sk" <= 75) AS "t3"
    INNER JOIN (SELECT *
        FROM "store"
        WHERE CAST("s_state" AS CHAR(2)) IN ('CO', 'GA', 'NE')) AS "t4" ON "t3"."ctr_store_sk" = "t4"."s_store_sk"
    INNER JOIN (SELECT *
        FROM "customer"
        WHERE "c_birth_month" = 8 AND ("c_birth_year" >= 1987 AND "c_birth_year" <= 1993)) AS "t5" ON "t3"."ctr_customer_sk" = "t5"."c_customer_sk"
    INNER JOIN (SELECT *
        FROM "customer_demographics"
        WHERE "cd_marital_status" = 'M' AND "cd_education_status" = '2 yr Degree' AND "cd_gender" = 'F') AS "t6" ON "t5"."c_current_cdemo_sk" = "t6"."cd_demo_sk"
    INNER JOIN (SELECT "t12"."sr_store_sk0", AVG("t12"."ctr_total_return") AS "$f1"
        FROM (SELECT "t7"."sr_store_sk0", SUM("t7"."sr_return_amt_inc_tax0") AS "ctr_total_return"
                FROM (SELECT *
                        FROM "store_returns" AS "store_returns0" ("sr_returned_date_sk0", "sr_return_time_sk0", "sr_item_sk0", "sr_customer_sk0", "sr_cdemo_sk0", "sr_hdemo_sk0", "sr_addr_sk0", "sr_store_sk0", "sr_reason_sk0", "sr_ticket_number0", "sr_return_quantity0", "sr_return_amt0", "sr_return_tax0", "sr_return_amt_inc_tax0", "sr_fee0", "sr_return_ship_cost0", "sr_refunded_cash0", "sr_reversed_charge0", "sr_store_credit0", "sr_net_loss0")
                        WHERE "sr_return_amt0" / "sr_return_quantity0" >= 80 AND "sr_return_amt0" / "sr_return_quantity0" <= 139) AS "t7"
                    INNER JOIN (SELECT *
                        FROM "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0")
                        WHERE "d_year0" = 1999) AS "t8" ON "t7"."sr_returned_date_sk0" = "t8"."d_date_sk0"
                GROUP BY "t7"."sr_customer_sk0", "t7"."sr_store_sk0", "t7"."sr_reason_sk0"
                HAVING "t7"."sr_store_sk0" IS NOT NULL) AS "t12"
        GROUP BY "t12"."sr_store_sk0") AS "t13" ON "t3"."ctr_store_sk" = "t13"."sr_store_sk0" AND "t3"."ctr_total_return" > "t13"."$f1" * 1.2
ORDER BY "t5"."c_customer_id"
FETCH NEXT 100 ROWS ONLY;
