SELECT "call_center"."cc_call_center_id" AS "call_center", "call_center"."cc_name" AS "call_center_name", "call_center"."cc_manager" AS "manager", SUM("catalog_returns"."cr_net_loss") AS "returns_loss"
FROM "call_center",
    "catalog_returns",
    "date_dim",
    "customer",
    "customer_address",
    "customer_demographics",
    "household_demographics"
WHERE "catalog_returns"."cr_call_center_sk" = "call_center"."cc_call_center_sk" AND "catalog_returns"."cr_returned_date_sk" = "date_dim"."d_date_sk" AND ("catalog_returns"."cr_returning_customer_sk" = "customer"."c_customer_sk" AND ("customer_demographics"."cd_demo_sk" = "customer"."c_current_cdemo_sk" AND "household_demographics"."hd_demo_sk" = "customer"."c_current_hdemo_sk")) AND ("customer_address"."ca_address_sk" = "customer"."c_current_addr_sk" AND ("date_dim"."d_year" = 2000 AND "date_dim"."d_moy" = 3) AND (("customer_demographics"."cd_marital_status" = 'M' AND "customer_demographics"."cd_education_status" = 'Unknown' OR "customer_demographics"."cd_marital_status" = 'W' AND "customer_demographics"."cd_education_status" = 'Advanced Degree') AND ("household_demographics"."hd_buy_potential" LIKE '501-1000%' AND CAST("customer_address"."ca_gmt_offset" AS DECIMAL(12, 2)) = -7)))
GROUP BY "call_center"."cc_call_center_id", "call_center"."cc_name", "call_center"."cc_manager", "customer_demographics"."cd_marital_status", "customer_demographics"."cd_education_status"
ORDER BY 4 DESC;
