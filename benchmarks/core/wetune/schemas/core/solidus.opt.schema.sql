CREATE TABLE action_mailbox_inbound_emails (
  id BIGINT NOT NULL,
  status INTEGER NOT NULL,
  message_id VARCHAR(255) NOT NULL,
  message_checksum VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (message_id, message_checksum)
);

CREATE TABLE action_text_rich_texts (
  id BIGINT NOT NULL,
  name VARCHAR(255) NOT NULL,
  body VARCHAR(255),
  record_type VARCHAR(255) NOT NULL,
  record_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (record_type, record_id, name)
);

CREATE TABLE active_storage_attachments (
  id BIGINT NOT NULL,
  name VARCHAR(255) NOT NULL,
  record_type VARCHAR(255) NOT NULL,
  record_id BIGINT NOT NULL,
  blob_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (record_type, record_id, name, blob_id)
);

CREATE TABLE active_storage_blobs (
  id BIGINT NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  filename VARCHAR(255) NOT NULL,
  content_type VARCHAR(255),
  metadata VARCHAR(255),
  byte_size BIGINT NOT NULL,
  checksum VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE ("key")
);

CREATE TABLE ar_internal_metadata (
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY ("key")
);

CREATE TABLE friendly_id_slugs (
  id INTEGER NOT NULL,
  slug VARCHAR(255) NOT NULL,
  sluggable_id INTEGER NOT NULL,
  sluggable_type VARCHAR(255),
  "scope" VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (slug, sluggable_type, "scope")
);

CREATE TABLE schema_migrations (
  version VARCHAR(255) NOT NULL,
  PRIMARY KEY (version)
);

CREATE TABLE spree_addresses (
  id INTEGER NOT NULL,
  firstname VARCHAR(255),
  lastname VARCHAR(255),
  address1 VARCHAR(255),
  address2 VARCHAR(255),
  city VARCHAR(255),
  zipcode VARCHAR(255),
  phone VARCHAR(255),
  state_name VARCHAR(255),
  alternative_phone VARCHAR(255),
  company VARCHAR(255),
  state_id INTEGER,
  country_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_adjustment_reasons (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  code VARCHAR(255),
  active INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_adjustments (
  id INTEGER NOT NULL,
  source_type VARCHAR(255),
  source_id INTEGER,
  adjustable_type VARCHAR(255),
  adjustable_id INTEGER NOT NULL,
  amount FLOAT,
  label VARCHAR(255),
  eligible INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  order_id INTEGER NOT NULL,
  included INTEGER,
  promotion_code_id INTEGER,
  adjustment_reason_id INTEGER,
  finalized INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_assets (
  id INTEGER NOT NULL,
  viewable_type VARCHAR(255),
  viewable_id INTEGER,
  attachment_width INTEGER,
  attachment_height INTEGER,
  attachment_file_size INTEGER,
  "position" INTEGER,
  attachment_content_type VARCHAR(255),
  attachment_file_name VARCHAR(255),
  "type" VARCHAR(255),
  attachment_updated_at TIMESTAMP,
  alt VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_calculators (
  id INTEGER NOT NULL,
  "type" VARCHAR(255),
  calculable_type VARCHAR(255),
  calculable_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  preferences VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE spree_cartons (
  id INTEGER NOT NULL,
  number VARCHAR(255),
  external_number VARCHAR(255),
  stock_location_id INTEGER,
  address_id INTEGER,
  shipping_method_id INTEGER,
  tracking VARCHAR(255),
  shipped_at TIMESTAMP,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  imported_from_shipment_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (imported_from_shipment_id),
  UNIQUE (number)
);

CREATE TABLE spree_countries (
  id INTEGER NOT NULL,
  iso_name VARCHAR(255),
  iso VARCHAR(255),
  iso3 VARCHAR(255),
  name VARCHAR(255),
  numcode INTEGER,
  states_required INTEGER,
  updated_at TIMESTAMP,
  created_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_credit_cards (
  id INTEGER NOT NULL,
  month VARCHAR(255),
  year VARCHAR(255),
  cc_type VARCHAR(255),
  last_digits VARCHAR(255),
  gateway_customer_profile_id VARCHAR(255),
  gateway_payment_profile_id VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  name VARCHAR(255),
  user_id INTEGER,
  payment_method_id INTEGER,
  "default" INTEGER NOT NULL,
  address_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_customer_returns (
  id INTEGER NOT NULL,
  number VARCHAR(255),
  stock_location_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_inventory_units (
  id INTEGER NOT NULL,
  state VARCHAR(255),
  variant_id INTEGER,
  shipment_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  pending INTEGER,
  line_item_id INTEGER,
  carton_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_line_item_actions (
  id INTEGER NOT NULL,
  line_item_id INTEGER NOT NULL,
  action_id INTEGER NOT NULL,
  quantity INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_line_items (
  id INTEGER NOT NULL,
  variant_id INTEGER,
  order_id INTEGER,
  quantity INTEGER NOT NULL,
  price FLOAT NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  cost_price FLOAT,
  tax_category_id INTEGER,
  adjustment_total FLOAT,
  additional_tax_total FLOAT,
  promo_total FLOAT,
  included_tax_total FLOAT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_log_entries (
  id INTEGER NOT NULL,
  source_type VARCHAR(255),
  source_id INTEGER,
  details VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_option_type_prototypes (
  id INTEGER NOT NULL,
  prototype_id INTEGER,
  option_type_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_option_types (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  presentation VARCHAR(255),
  "position" INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_option_values (
  id INTEGER NOT NULL,
  "position" INTEGER,
  name VARCHAR(255),
  presentation VARCHAR(255),
  option_type_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_option_values_variants (
  id INTEGER NOT NULL,
  variant_id INTEGER,
  option_value_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_order_mutexes (
  id INTEGER NOT NULL,
  order_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (order_id)
);

CREATE TABLE spree_orders (
  id INTEGER NOT NULL,
  number VARCHAR(255),
  item_total FLOAT NOT NULL,
  total FLOAT NOT NULL,
  state VARCHAR(255),
  adjustment_total FLOAT NOT NULL,
  user_id INTEGER,
  completed_at TIMESTAMP,
  bill_address_id INTEGER,
  ship_address_id INTEGER,
  payment_total FLOAT,
  shipment_state VARCHAR(255),
  payment_state VARCHAR(255),
  email VARCHAR(255),
  special_instructions VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  currency VARCHAR(255),
  last_ip_address VARCHAR(255),
  created_by_id INTEGER,
  shipment_total FLOAT NOT NULL,
  additional_tax_total FLOAT,
  promo_total FLOAT,
  channel VARCHAR(255),
  included_tax_total FLOAT NOT NULL,
  item_count INTEGER,
  approver_id INTEGER,
  approved_at TIMESTAMP,
  confirmation_delivered INTEGER,
  guest_token VARCHAR(255),
  canceled_at TIMESTAMP,
  canceler_id INTEGER,
  store_id INTEGER,
  approver_name VARCHAR(255),
  frontend_viewable INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_orders_promotions (
  id INTEGER NOT NULL,
  order_id INTEGER,
  promotion_id INTEGER,
  promotion_code_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_payment_capture_events (
  id INTEGER NOT NULL,
  amount FLOAT,
  payment_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_payment_methods (
  id INTEGER NOT NULL,
  "type" VARCHAR(255),
  name VARCHAR(255),
  description VARCHAR(255),
  active INTEGER,
  deleted_at TIMESTAMP,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  auto_capture INTEGER,
  preferences VARCHAR(255),
  preference_source VARCHAR(255),
  "position" INTEGER,
  available_to_users INTEGER,
  available_to_admin INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_payments (
  id INTEGER NOT NULL,
  amount FLOAT NOT NULL,
  order_id INTEGER,
  source_type VARCHAR(255),
  source_id INTEGER,
  payment_method_id INTEGER,
  state VARCHAR(255),
  response_code VARCHAR(255),
  avs_response VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  number VARCHAR(255),
  cvv_response_code VARCHAR(255),
  cvv_response_message VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (number)
);

CREATE TABLE spree_preferences (
  id INTEGER NOT NULL,
  "value" VARCHAR(255),
  "key" VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE ("key")
);

CREATE TABLE spree_prices (
  id INTEGER NOT NULL,
  variant_id INTEGER NOT NULL,
  amount FLOAT,
  currency VARCHAR(255),
  deleted_at TIMESTAMP,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  country_iso VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE spree_product_option_types (
  id INTEGER NOT NULL,
  "position" INTEGER,
  product_id INTEGER,
  option_type_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_product_promotion_rules (
  id INTEGER NOT NULL,
  product_id INTEGER,
  promotion_rule_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_product_properties (
  id INTEGER NOT NULL,
  "value" VARCHAR(255),
  product_id INTEGER,
  property_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  "position" INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_products (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  available_on TIMESTAMP,
  deleted_at TIMESTAMP,
  slug VARCHAR(255),
  meta_description VARCHAR(255),
  meta_keywords VARCHAR(255),
  tax_category_id INTEGER,
  shipping_category_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  promotionable INTEGER,
  meta_title VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (slug)
);

CREATE TABLE spree_products_taxons (
  id INTEGER NOT NULL,
  product_id INTEGER,
  taxon_id INTEGER,
  "position" INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_promotion_action_line_items (
  id INTEGER NOT NULL,
  promotion_action_id INTEGER,
  variant_id INTEGER,
  quantity INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_promotion_actions (
  id INTEGER NOT NULL,
  promotion_id INTEGER,
  "position" INTEGER,
  "type" VARCHAR(255),
  deleted_at TIMESTAMP,
  preferences VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_promotion_categories (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  code VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE spree_promotion_code_batches (
  id INTEGER NOT NULL,
  promotion_id INTEGER NOT NULL,
  base_code VARCHAR(255) NOT NULL,
  number_of_codes INTEGER NOT NULL,
  email VARCHAR(255),
  error VARCHAR(255),
  state VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  join_characters VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_promotion_codes (
  id INTEGER NOT NULL,
  promotion_id INTEGER NOT NULL,
  "value" VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  promotion_code_batch_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE ("value")
);

CREATE TABLE spree_promotion_rule_taxons (
  id INTEGER NOT NULL,
  taxon_id INTEGER,
  promotion_rule_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_promotion_rules (
  id INTEGER NOT NULL,
  promotion_id INTEGER,
  product_group_id INTEGER,
  "type" VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  code VARCHAR(255),
  preferences VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE spree_promotion_rules_stores (
  id BIGINT NOT NULL,
  store_id BIGINT NOT NULL,
  promotion_rule_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_promotion_rules_users (
  id INTEGER NOT NULL,
  user_id INTEGER,
  promotion_rule_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_promotions (
  id INTEGER NOT NULL,
  description VARCHAR(255),
  expires_at TIMESTAMP,
  starts_at TIMESTAMP,
  name VARCHAR(255),
  "type" VARCHAR(255),
  usage_limit INTEGER,
  match_policy VARCHAR(255),
  advertise INTEGER,
  path VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  promotion_category_id INTEGER,
  per_code_usage_limit INTEGER,
  apply_automatically INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_properties (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  presentation VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_property_prototypes (
  id INTEGER NOT NULL,
  prototype_id INTEGER,
  property_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_prototype_taxons (
  id INTEGER NOT NULL,
  taxon_id INTEGER,
  prototype_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_prototypes (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_refund_reasons (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  active INTEGER,
  mutable INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  code VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE spree_refunds (
  id INTEGER NOT NULL,
  payment_id INTEGER,
  amount FLOAT NOT NULL,
  transaction_id VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  refund_reason_id INTEGER,
  reimbursement_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_reimbursement_credits (
  id INTEGER NOT NULL,
  amount FLOAT NOT NULL,
  reimbursement_id INTEGER,
  creditable_id INTEGER,
  creditable_type VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_reimbursement_types (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  active INTEGER,
  mutable INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  "type" VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE spree_reimbursements (
  id INTEGER NOT NULL,
  number VARCHAR(255),
  reimbursement_status VARCHAR(255),
  customer_return_id INTEGER,
  order_id INTEGER,
  total FLOAT,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_return_authorizations (
  id INTEGER NOT NULL,
  number VARCHAR(255),
  state VARCHAR(255),
  order_id INTEGER,
  memo VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  stock_location_id INTEGER,
  return_reason_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_return_items (
  id INTEGER NOT NULL,
  return_authorization_id INTEGER,
  inventory_unit_id INTEGER,
  exchange_variant_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  amount FLOAT NOT NULL,
  included_tax_total FLOAT NOT NULL,
  additional_tax_total FLOAT NOT NULL,
  reception_status VARCHAR(255),
  acceptance_status VARCHAR(255),
  customer_return_id INTEGER,
  reimbursement_id INTEGER,
  exchange_inventory_unit_id INTEGER,
  acceptance_status_errors VARCHAR(255),
  preferred_reimbursement_type_id INTEGER,
  override_reimbursement_type_id INTEGER,
  resellable INTEGER NOT NULL,
  return_reason_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_return_reasons (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  active INTEGER,
  mutable INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_roles (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE spree_roles_users (
  id INTEGER NOT NULL,
  role_id INTEGER,
  user_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (user_id, role_id)
);

CREATE TABLE spree_shipments (
  id INTEGER NOT NULL,
  tracking VARCHAR(255),
  number VARCHAR(255),
  cost FLOAT,
  shipped_at TIMESTAMP,
  order_id INTEGER,
  deprecated_address_id INTEGER,
  state VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  stock_location_id INTEGER,
  adjustment_total FLOAT,
  additional_tax_total FLOAT,
  promo_total FLOAT,
  included_tax_total FLOAT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_shipping_categories (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_shipping_method_categories (
  id INTEGER NOT NULL,
  shipping_method_id INTEGER NOT NULL,
  shipping_category_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (shipping_category_id, shipping_method_id)
);

CREATE TABLE spree_shipping_method_stock_locations (
  id INTEGER NOT NULL,
  shipping_method_id INTEGER,
  stock_location_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_shipping_method_zones (
  id INTEGER NOT NULL,
  shipping_method_id INTEGER,
  zone_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_shipping_methods (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  deleted_at TIMESTAMP,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  tracking_url VARCHAR(255),
  admin_name VARCHAR(255),
  tax_category_id INTEGER,
  code VARCHAR(255),
  available_to_all INTEGER,
  carrier VARCHAR(255),
  service_level VARCHAR(255),
  available_to_users INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_shipping_rate_taxes (
  id INTEGER NOT NULL,
  amount FLOAT NOT NULL,
  tax_rate_id INTEGER,
  shipping_rate_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_shipping_rates (
  id INTEGER NOT NULL,
  shipment_id INTEGER,
  shipping_method_id INTEGER,
  selected INTEGER,
  cost FLOAT,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  tax_rate_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (shipment_id, shipping_method_id)
);

CREATE TABLE spree_state_changes (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  previous_state VARCHAR(255),
  stateful_id INTEGER,
  user_id INTEGER,
  stateful_type VARCHAR(255),
  next_state VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_states (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  abbr VARCHAR(255),
  country_id INTEGER,
  updated_at TIMESTAMP,
  created_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_stock_items (
  id INTEGER NOT NULL,
  stock_location_id INTEGER,
  variant_id INTEGER,
  count_on_hand INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  backorderable INTEGER,
  deleted_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_stock_locations (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  "default" INTEGER NOT NULL,
  address1 VARCHAR(255),
  address2 VARCHAR(255),
  city VARCHAR(255),
  state_id INTEGER,
  state_name VARCHAR(255),
  country_id INTEGER,
  zipcode VARCHAR(255),
  phone VARCHAR(255),
  active INTEGER,
  backorderable_default INTEGER,
  propagate_all_variants INTEGER,
  admin_name VARCHAR(255),
  "position" INTEGER,
  restock_inventory INTEGER NOT NULL,
  fulfillable INTEGER NOT NULL,
  code VARCHAR(255),
  check_stock_on_transfer INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_stock_movements (
  id INTEGER NOT NULL,
  stock_item_id INTEGER,
  quantity INTEGER,
  action VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  originator_type VARCHAR(255),
  originator_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_store_credit_categories (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_store_credit_events (
  id INTEGER NOT NULL,
  store_credit_id INTEGER NOT NULL,
  action VARCHAR(255) NOT NULL,
  amount FLOAT,
  user_total_amount FLOAT NOT NULL,
  authorization_code VARCHAR(255) NOT NULL,
  deleted_at TIMESTAMP,
  originator_type VARCHAR(255),
  originator_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  amount_remaining FLOAT,
  store_credit_reason_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_store_credit_reasons (
  id BIGINT NOT NULL,
  name VARCHAR(255),
  active INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_store_credit_types (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  priority INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_store_credits (
  id INTEGER NOT NULL,
  user_id INTEGER,
  category_id INTEGER,
  created_by_id INTEGER,
  amount FLOAT NOT NULL,
  amount_used FLOAT NOT NULL,
  amount_authorized FLOAT NOT NULL,
  currency VARCHAR(255),
  memo VARCHAR(255),
  deleted_at TIMESTAMP,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  type_id INTEGER,
  invalidated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_store_payment_methods (
  id INTEGER NOT NULL,
  store_id INTEGER NOT NULL,
  payment_method_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_store_shipping_methods (
  id BIGINT NOT NULL,
  store_id BIGINT NOT NULL,
  shipping_method_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_stores (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  url VARCHAR(255),
  meta_description VARCHAR(255),
  meta_keywords VARCHAR(255),
  seo_title VARCHAR(255),
  mail_from_address VARCHAR(255),
  default_currency VARCHAR(255),
  code VARCHAR(255),
  "default" INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  cart_tax_country_iso VARCHAR(255),
  available_locales VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE spree_tax_categories (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  description VARCHAR(255),
  is_default INTEGER,
  deleted_at TIMESTAMP,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  tax_code VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE spree_tax_rate_tax_categories (
  id INTEGER NOT NULL,
  tax_category_id INTEGER NOT NULL,
  tax_rate_id INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_tax_rates (
  id INTEGER NOT NULL,
  amount FLOAT,
  zone_id INTEGER,
  included_in_price INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  name VARCHAR(255),
  show_rate_in_label INTEGER,
  deleted_at TIMESTAMP,
  starts_at TIMESTAMP,
  expires_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_taxonomies (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  "position" INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_taxons (
  id INTEGER NOT NULL,
  parent_id INTEGER,
  "position" INTEGER,
  name VARCHAR(255) NOT NULL,
  permalink VARCHAR(255),
  taxonomy_id INTEGER,
  lft INTEGER,
  rgt INTEGER,
  icon_file_name VARCHAR(255),
  icon_content_type VARCHAR(255),
  icon_file_size INTEGER,
  icon_updated_at TIMESTAMP,
  description VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  meta_title VARCHAR(255),
  meta_description VARCHAR(255),
  meta_keywords VARCHAR(255),
  depth INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE spree_unit_cancels (
  id INTEGER NOT NULL,
  inventory_unit_id INTEGER NOT NULL,
  reason VARCHAR(255),
  created_by VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_user_addresses (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  address_id INTEGER NOT NULL,
  "default" INTEGER,
  archived INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, address_id)
);

CREATE TABLE spree_user_stock_locations (
  id INTEGER NOT NULL,
  user_id INTEGER,
  stock_location_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_users (
  id INTEGER NOT NULL,
  crypted_password VARCHAR(255),
  salt VARCHAR(255),
  email VARCHAR(255),
  remember_token VARCHAR(255),
  remember_token_expires_at VARCHAR(255),
  persistence_token VARCHAR(255),
  single_access_token VARCHAR(255),
  perishable_token VARCHAR(255),
  login_count INTEGER NOT NULL,
  failed_login_count INTEGER NOT NULL,
  last_request_at TIMESTAMP,
  current_login_at TIMESTAMP,
  last_login_at TIMESTAMP,
  current_login_ip VARCHAR(255),
  last_login_ip VARCHAR(255),
  login VARCHAR(255),
  ship_address_id INTEGER,
  bill_address_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  openid_identifier VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE spree_variant_property_rule_conditions (
  id INTEGER NOT NULL,
  option_value_id INTEGER,
  variant_property_rule_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_variant_property_rule_values (
  id INTEGER NOT NULL,
  "value" VARCHAR(255),
  "position" INTEGER,
  property_id INTEGER,
  variant_property_rule_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_variant_property_rules (
  id INTEGER NOT NULL,
  product_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE spree_variants (
  id INTEGER NOT NULL,
  sku VARCHAR(255) NOT NULL,
  weight FLOAT,
  height FLOAT,
  width FLOAT,
  depth FLOAT,
  deleted_at TIMESTAMP,
  is_master INTEGER,
  product_id INTEGER,
  cost_price FLOAT,
  "position" INTEGER,
  cost_currency VARCHAR(255),
  track_inventory INTEGER,
  tax_category_id INTEGER,
  updated_at TIMESTAMP,
  created_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_wallet_payment_sources (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  payment_source_type VARCHAR(255) NOT NULL,
  payment_source_id INTEGER NOT NULL,
  "default" INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, payment_source_id, payment_source_type)
);

CREATE TABLE spree_zone_members (
  id INTEGER NOT NULL,
  zoneable_type VARCHAR(255),
  zoneable_id INTEGER,
  zone_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE spree_zones (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  description VARCHAR(255),
  zone_members_count INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);
