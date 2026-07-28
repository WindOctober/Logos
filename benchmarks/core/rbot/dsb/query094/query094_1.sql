SELECT COUNT("t4"."ws_order_number") FILTER (WHERE "t4"."$g_0") AS "order count", MIN("t4"."total shipping cost") FILTER (WHERE "t4"."$g_1") AS "total shipping cost", MIN("t4"."total net profit") FILTER (WHERE "t4"."$g_1") AS "total net profit"
FROM (SELECT "web_sales"."ws_order_number", SUM("web_sales"."ws_ext_ship_cost") AS "total shipping cost", SUM("web_sales"."ws_net_profit") AS "total net profit", GROUPING("web_sales"."ws_order_number") = 0 AS "$g_0", GROUPING("web_sales"."ws_order_number") = 1 AS "$g_1"
        FROM "web_sales",
            "date_dim",
            "customer_address",
            "web_site"
        WHERE "date_dim"."d_date" >= '2002-6-01' AND "date_dim"."d_date" <= (CAST('2002-6-01' AS DATE) + INTERVAL '60' DAY) AND ("web_sales"."ws_ship_date_sk" = "date_dim"."d_date_sk" AND ("web_sales"."ws_ship_addr_sk" = "customer_address"."ca_address_sk" AND ("customer_address"."ca_state" = 'DC' OR ("customer_address"."ca_state" = 'MO' OR "customer_address"."ca_state" = 'OH') OR ("customer_address"."ca_state" = 'OK' OR ("customer_address"."ca_state" = 'PA' OR "customer_address"."ca_state" = 'SD'))))) AND ("web_sales"."ws_web_site_sk" = "web_site"."web_site_sk" AND ("web_site"."web_gmt_offset" >= -5 AND "web_sales"."ws_list_price" >= 226) AND ("web_sales"."ws_list_price" <= 255 AND (EXISTS (SELECT *
                                        FROM "web_sales" AS "web_sales0" ("ws_sold_date_sk0", "ws_sold_time_sk0", "ws_ship_date_sk0", "ws_item_sk0", "ws_bill_customer_sk0", "ws_bill_cdemo_sk0", "ws_bill_hdemo_sk0", "ws_bill_addr_sk0", "ws_ship_customer_sk0", "ws_ship_cdemo_sk0", "ws_ship_hdemo_sk0", "ws_ship_addr_sk0", "ws_web_page_sk0", "ws_web_site_sk0", "ws_ship_mode_sk0", "ws_warehouse_sk0", "ws_promo_sk0", "ws_order_number0", "ws_quantity0", "ws_wholesale_cost0", "ws_list_price0", "ws_sales_price0", "ws_ext_discount_amt0", "ws_ext_sales_price0", "ws_ext_wholesale_cost0", "ws_ext_list_price0", "ws_ext_tax0", "ws_coupon_amt0", "ws_ext_ship_cost0", "ws_net_paid0", "ws_net_paid_inc_tax0", "ws_net_paid_inc_ship0", "ws_net_paid_inc_ship_tax0", "ws_net_profit0")
                                        WHERE "web_sales"."ws_order_number" = "ws_order_number0" AND "web_sales"."ws_warehouse_sk" <> "ws_warehouse_sk0") AND NOT EXISTS (SELECT *
                                        FROM "web_returns"
                                        WHERE "web_sales"."ws_order_number" = "wr_order_number" AND ("wr_reason_sk" = 3 OR "wr_reason_sk" = 6 OR "wr_reason_sk" = 18 OR "wr_reason_sk" = 30 OR "wr_reason_sk" = 40)))))
        GROUP BY ROLLUP("web_sales"."ws_order_number")) AS "t4"
ORDER BY 1
FETCH NEXT 100 ROWS ONLY;
