CREATE TABLE store_sales (
  ss_item_sk INTEGER,
  ss_customer_sk INTEGER,
  ss_net_paid DECIMAL,
  ss_quantity INTEGER
);

CREATE TABLE customer (
  c_customer_sk INTEGER,
  c_birth_country VARCHAR
);
