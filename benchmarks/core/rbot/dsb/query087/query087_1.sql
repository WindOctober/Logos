SELECT COUNT(*)
FROM (SELECT *
            FROM (SELECT "customer"."c_last_name", "customer"."c_first_name", "date_dim"."d_date"
                        FROM "store_sales",
                            "date_dim",
                            "customer"
                        WHERE "store_sales"."ss_sold_date_sk" = "date_dim"."d_date_sk" AND "store_sales"."ss_customer_sk" = "customer"."c_customer_sk" AND ("date_dim"."d_month_seq" >= 1206 AND ("date_dim"."d_month_seq" <= 1206 + 11 AND "store_sales"."ss_list_price" >= 271)) AND ("store_sales"."ss_list_price" <= 300 AND "customer"."c_birth_year" >= 1972 AND ("customer"."c_birth_year" <= 1978 AND ("store_sales"."ss_wholesale_cost" >= 73 AND "store_sales"."ss_wholesale_cost" <= 83)))
                        GROUP BY "date_dim"."d_date", "customer"."c_first_name", "customer"."c_last_name"
                        EXCEPT
                        SELECT "customer0"."c_last_name0", "customer0"."c_first_name0", "date_dim0"."d_date0"
                        FROM "catalog_sales",
                            "date_dim" AS "date_dim0" ("d_date_sk0", "d_date_id0", "d_date0", "d_month_seq0", "d_week_seq0", "d_quarter_seq0", "d_year0", "d_dow0", "d_moy0", "d_dom0", "d_qoy0", "d_fy_year0", "d_fy_quarter_seq0", "d_fy_week_seq0", "d_day_name0", "d_quarter_name0", "d_holiday0", "d_weekend0", "d_following_holiday0", "d_first_dom0", "d_last_dom0", "d_same_day_ly0", "d_same_day_lq0", "d_current_day0", "d_current_week0", "d_current_month0", "d_current_quarter0", "d_current_year0"),
                            "customer" AS "customer0" ("c_customer_sk0", "c_customer_id0", "c_current_cdemo_sk0", "c_current_hdemo_sk0", "c_current_addr_sk0", "c_first_shipto_date_sk0", "c_first_sales_date_sk0", "c_salutation0", "c_first_name0", "c_last_name0", "c_preferred_cust_flag0", "c_birth_day0", "c_birth_month0", "c_birth_year0", "c_birth_country0", "c_login0", "c_email_address0", "c_last_review_date_sk0")
                        WHERE "catalog_sales"."cs_sold_date_sk" = "date_dim0"."d_date_sk0" AND "catalog_sales"."cs_bill_customer_sk" = "customer0"."c_customer_sk0" AND ("date_dim0"."d_month_seq0" >= 1206 AND ("date_dim0"."d_month_seq0" <= 1206 + 11 AND "catalog_sales"."cs_list_price" >= 271)) AND ("catalog_sales"."cs_list_price" <= 300 AND "customer0"."c_birth_year0" >= 1972 AND ("customer0"."c_birth_year0" <= 1978 AND ("catalog_sales"."cs_wholesale_cost" >= 73 AND "catalog_sales"."cs_wholesale_cost" <= 83)))
                        GROUP BY "date_dim0"."d_date0", "customer0"."c_first_name0", "customer0"."c_last_name0") AS "t"
            EXCEPT
            SELECT "customer1"."c_last_name1", "customer1"."c_first_name1", "date_dim1"."d_date1"
            FROM "web_sales",
                "date_dim" AS "date_dim1" ("d_date_sk1", "d_date_id1", "d_date1", "d_month_seq1", "d_week_seq1", "d_quarter_seq1", "d_year1", "d_dow1", "d_moy1", "d_dom1", "d_qoy1", "d_fy_year1", "d_fy_quarter_seq1", "d_fy_week_seq1", "d_day_name1", "d_quarter_name1", "d_holiday1", "d_weekend1", "d_following_holiday1", "d_first_dom1", "d_last_dom1", "d_same_day_ly1", "d_same_day_lq1", "d_current_day1", "d_current_week1", "d_current_month1", "d_current_quarter1", "d_current_year1"),
                "customer" AS "customer1" ("c_customer_sk1", "c_customer_id1", "c_current_cdemo_sk1", "c_current_hdemo_sk1", "c_current_addr_sk1", "c_first_shipto_date_sk1", "c_first_sales_date_sk1", "c_salutation1", "c_first_name1", "c_last_name1", "c_preferred_cust_flag1", "c_birth_day1", "c_birth_month1", "c_birth_year1", "c_birth_country1", "c_login1", "c_email_address1", "c_last_review_date_sk1")
            WHERE "web_sales"."ws_sold_date_sk" = "date_dim1"."d_date_sk1" AND "web_sales"."ws_bill_customer_sk" = "customer1"."c_customer_sk1" AND ("date_dim1"."d_month_seq1" >= 1206 AND ("date_dim1"."d_month_seq1" <= 1206 + 11 AND "web_sales"."ws_list_price" >= 271)) AND ("web_sales"."ws_list_price" <= 300 AND "customer1"."c_birth_year1" >= 1972 AND ("customer1"."c_birth_year1" <= 1978 AND ("web_sales"."ws_wholesale_cost" >= 73 AND "web_sales"."ws_wholesale_cost" <= 83)))
            GROUP BY "date_dim1"."d_date1", "customer1"."c_first_name1", "customer1"."c_last_name1") AS "t9";
