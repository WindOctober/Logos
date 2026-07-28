SELECT "item"."i_brand_id" AS "brand_id", "item"."i_brand" AS "brand", "item"."i_manufact_id", "item"."i_manufact", SUM("store_sales"."ss_ext_sales_price") AS "ext_price"
FROM "date_dim",
    "store_sales",
    "item",
    "customer",
    "customer_address",
    "store"
WHERE "date_dim"."d_date_sk" = "store_sales"."ss_sold_date_sk" AND ("store_sales"."ss_item_sk" = "item"."i_item_sk" AND "store_sales"."ss_customer_sk" = "customer"."c_customer_sk") AND ("customer"."c_current_addr_sk" = "customer_address"."ca_address_sk" AND ("store_sales"."ss_store_sk" = "store"."s_store_sk" AND "item"."i_category" = 'Books')) AND ("date_dim"."d_year" = 2001 AND ("date_dim"."d_moy" = 2 AND SUBSTRING("customer_address"."ca_zip", 1, 5) <> SUBSTRING("store"."s_zip", 1, 5)) AND ("customer_address"."ca_state" = 'IL' AND "customer"."c_birth_month" = 9 AND ("store_sales"."ss_wholesale_cost" >= 73 AND "store_sales"."ss_wholesale_cost" <= 93)))
GROUP BY "item"."i_brand_id", "item"."i_brand", "item"."i_manufact_id", "item"."i_manufact"
ORDER BY 5 DESC, "item"."i_brand", "item"."i_brand_id", "item"."i_manufact_id", "item"."i_manufact"
FETCH NEXT 100 ROWS ONLY;
