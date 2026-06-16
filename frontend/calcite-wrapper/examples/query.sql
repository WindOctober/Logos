SELECT c.c_birth_country, SUM(s.ss_net_paid) AS revenue
FROM store_sales AS s
JOIN customer AS c ON s.ss_customer_sk = c.c_customer_sk
WHERE s.ss_quantity > 0
GROUP BY c.c_birth_country;
