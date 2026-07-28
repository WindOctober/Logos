SELECT SUBSTRING("c_phone", 1, 2) AS "cntrycode", COUNT(*) AS "numcust", COALESCE(SUM("c_acctbal"), 0) AS "totacctbal"
FROM "customer"
WHERE (SUBSTRING("c_phone", 1, 2) = '14' OR (SUBSTRING("c_phone", 1, 2) = '29' OR SUBSTRING("c_phone", 1, 2) = '27') OR (SUBSTRING("c_phone", 1, 2) = '23' OR SUBSTRING("c_phone", 1, 2) = '32' OR (SUBSTRING("c_phone", 1, 2) = '10' OR SUBSTRING("c_phone", 1, 2) = '12'))) AND "c_acctbal" > (((SELECT AVG("c_acctbal0")
                    FROM "customer" AS "customer0" ("c_custkey0", "c_name0", "c_address0", "c_nationkey0", "c_phone0", "c_acctbal0", "c_mktsegment0", "c_comment0")
                    WHERE "c_acctbal0" > 0.00 AND (SUBSTRING("c_phone0", 1, 2) = '14' OR (SUBSTRING("c_phone0", 1, 2) = '29' OR SUBSTRING("c_phone0", 1, 2) = '27') OR (SUBSTRING("c_phone0", 1, 2) = '23' OR SUBSTRING("c_phone0", 1, 2) = '32' OR (SUBSTRING("c_phone0", 1, 2) = '10' OR SUBSTRING("c_phone0", 1, 2) = '12')))))) AND NOT EXISTS (SELECT *
        FROM "orders"
        WHERE "o_custkey" = "customer"."c_custkey")
GROUP BY SUBSTRING("c_phone", 1, 2)
ORDER BY 1
FETCH NEXT 1 ROWS ONLY;
