CREATE TABLE abuse_reports (
  id INTEGER NOT NULL,
  reporter_id INTEGER,
  user_id INTEGER,
  message VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  message_html VARCHAR(255),
  cached_markdown_version INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE alerts_service_data (
  id BIGINT NOT NULL,
  service_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  encrypted_token VARCHAR(255),
  encrypted_token_iv VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE allowed_email_domains (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  group_id INTEGER NOT NULL,
  domain VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE analytics_cycle_analytics_group_stages (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  relative_position INTEGER,
  start_event_identifier INTEGER NOT NULL,
  end_event_identifier INTEGER NOT NULL,
  group_id BIGINT NOT NULL,
  start_event_label_id BIGINT,
  end_event_label_id BIGINT,
  hidden BOOLEAN NOT NULL,
  custom BOOLEAN NOT NULL,
  name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, name)
);

CREATE TABLE analytics_cycle_analytics_project_stages (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  relative_position INTEGER,
  start_event_identifier INTEGER NOT NULL,
  end_event_identifier INTEGER NOT NULL,
  project_id BIGINT NOT NULL,
  start_event_label_id BIGINT,
  end_event_label_id BIGINT,
  hidden BOOLEAN NOT NULL,
  custom BOOLEAN NOT NULL,
  name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, name)
);

CREATE TABLE analytics_language_trend_repository_languages (
  file_count INTEGER NOT NULL,
  programming_language_id BIGINT NOT NULL,
  project_id BIGINT NOT NULL,
  loc INTEGER NOT NULL,
  bytes INTEGER NOT NULL,
  percentage INTEGER NOT NULL,
  snapshot_date DATE NOT NULL,
  UNIQUE (programming_language_id, project_id, snapshot_date)
);

CREATE TABLE appearances (
  id INTEGER NOT NULL,
  title VARCHAR(255) NOT NULL,
  description VARCHAR(255) NOT NULL,
  logo VARCHAR(255),
  updated_by INTEGER,
  header_logo VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  description_html VARCHAR(255),
  cached_markdown_version INTEGER,
  new_project_guidelines VARCHAR(255),
  new_project_guidelines_html VARCHAR(255),
  header_message VARCHAR(255),
  header_message_html VARCHAR(255),
  footer_message VARCHAR(255),
  footer_message_html VARCHAR(255),
  message_background_color VARCHAR(255),
  message_font_color VARCHAR(255),
  favicon VARCHAR(255),
  email_header_and_footer_enabled BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE application_setting_terms (
  id INTEGER NOT NULL,
  cached_markdown_version INTEGER,
  terms VARCHAR(255) NOT NULL,
  terms_html VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE application_settings (
  id INTEGER NOT NULL,
  default_projects_limit INTEGER,
  signup_enabled BOOLEAN,
  gravatar_enabled BOOLEAN,
  sign_in_text VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  home_page_url VARCHAR(255),
  default_branch_protection INTEGER,
  help_text VARCHAR(255),
  restricted_visibility_levels VARCHAR(255),
  version_check_enabled BOOLEAN,
  max_attachment_size INTEGER NOT NULL,
  default_project_visibility INTEGER NOT NULL,
  default_snippet_visibility INTEGER NOT NULL,
  domain_whitelist VARCHAR(255),
  user_oauth_applications BOOLEAN,
  after_sign_out_path VARCHAR(255),
  session_expire_delay INTEGER NOT NULL,
  import_sources VARCHAR(255),
  help_page_text VARCHAR(255),
  admin_notification_email VARCHAR(255),
  shared_runners_enabled BOOLEAN NOT NULL,
  max_artifacts_size INTEGER NOT NULL,
  runners_registration_token VARCHAR(255),
  max_pages_size INTEGER NOT NULL,
  require_two_factor_authentication BOOLEAN,
  two_factor_grace_period INTEGER,
  metrics_enabled BOOLEAN,
  metrics_host VARCHAR(255),
  metrics_pool_size INTEGER,
  metrics_timeout INTEGER,
  metrics_method_call_threshold INTEGER,
  recaptcha_enabled BOOLEAN,
  metrics_port INTEGER,
  akismet_enabled BOOLEAN,
  metrics_sample_interval INTEGER,
  email_author_in_body BOOLEAN,
  default_group_visibility INTEGER,
  repository_checks_enabled BOOLEAN,
  shared_runners_text VARCHAR(255),
  metrics_packet_size INTEGER,
  disabled_oauth_sign_in_sources VARCHAR(255),
  health_check_access_token VARCHAR(255),
  send_user_confirmation_email BOOLEAN,
  container_registry_token_expire_delay INTEGER,
  after_sign_up_text VARCHAR(255),
  user_default_external BOOLEAN NOT NULL,
  elasticsearch_indexing BOOLEAN NOT NULL,
  elasticsearch_search BOOLEAN NOT NULL,
  repository_storages VARCHAR(255),
  enabled_git_access_protocol VARCHAR(255),
  domain_blacklist_enabled BOOLEAN,
  domain_blacklist VARCHAR(255),
  usage_ping_enabled BOOLEAN NOT NULL,
  sign_in_text_html VARCHAR(255),
  help_page_text_html VARCHAR(255),
  shared_runners_text_html VARCHAR(255),
  after_sign_up_text_html VARCHAR(255),
  rsa_key_restriction INTEGER NOT NULL,
  dsa_key_restriction INTEGER NOT NULL,
  ecdsa_key_restriction INTEGER NOT NULL,
  ed25519_key_restriction INTEGER NOT NULL,
  housekeeping_enabled BOOLEAN NOT NULL,
  housekeeping_bitmaps_enabled BOOLEAN NOT NULL,
  housekeeping_incremental_repack_period INTEGER NOT NULL,
  housekeeping_full_repack_period INTEGER NOT NULL,
  housekeeping_gc_period INTEGER NOT NULL,
  html_emails_enabled BOOLEAN,
  plantuml_url VARCHAR(255),
  plantuml_enabled BOOLEAN,
  shared_runners_minutes INTEGER NOT NULL,
  repository_size_limit BIGINT,
  terminal_max_session_time INTEGER NOT NULL,
  unique_ips_limit_per_user INTEGER,
  unique_ips_limit_time_window INTEGER,
  unique_ips_limit_enabled BOOLEAN NOT NULL,
  default_artifacts_expire_in VARCHAR(255) NOT NULL,
  elasticsearch_url VARCHAR(255),
  elasticsearch_aws BOOLEAN NOT NULL,
  elasticsearch_aws_region VARCHAR(255),
  elasticsearch_aws_access_key VARCHAR(255),
  geo_status_timeout INTEGER,
  uuid VARCHAR(255),
  polling_interval_multiplier FLOAT NOT NULL,
  elasticsearch_experimental_indexer BOOLEAN,
  cached_markdown_version INTEGER,
  check_namespace_plan BOOLEAN NOT NULL,
  mirror_max_delay INTEGER NOT NULL,
  mirror_max_capacity INTEGER NOT NULL,
  mirror_capacity_threshold INTEGER NOT NULL,
  prometheus_metrics_enabled BOOLEAN NOT NULL,
  authorized_keys_enabled BOOLEAN NOT NULL,
  help_page_hide_commercial_content BOOLEAN,
  help_page_support_url VARCHAR(255),
  slack_app_enabled BOOLEAN,
  slack_app_id VARCHAR(255),
  performance_bar_allowed_group_id INTEGER,
  allow_group_owners_to_manage_ldap BOOLEAN NOT NULL,
  hashed_storage_enabled BOOLEAN NOT NULL,
  project_export_enabled BOOLEAN NOT NULL,
  auto_devops_enabled BOOLEAN NOT NULL,
  throttle_unauthenticated_enabled BOOLEAN NOT NULL,
  throttle_unauthenticated_requests_per_period INTEGER NOT NULL,
  throttle_unauthenticated_period_in_seconds INTEGER NOT NULL,
  throttle_authenticated_api_enabled BOOLEAN NOT NULL,
  throttle_authenticated_api_requests_per_period INTEGER NOT NULL,
  throttle_authenticated_api_period_in_seconds INTEGER NOT NULL,
  throttle_authenticated_web_enabled BOOLEAN NOT NULL,
  throttle_authenticated_web_requests_per_period INTEGER NOT NULL,
  throttle_authenticated_web_period_in_seconds INTEGER NOT NULL,
  gitaly_timeout_default INTEGER NOT NULL,
  gitaly_timeout_medium INTEGER NOT NULL,
  gitaly_timeout_fast INTEGER NOT NULL,
  mirror_available BOOLEAN NOT NULL,
  password_authentication_enabled_for_web BOOLEAN,
  password_authentication_enabled_for_git BOOLEAN NOT NULL,
  auto_devops_domain VARCHAR(255),
  external_authorization_service_enabled BOOLEAN NOT NULL,
  external_authorization_service_url VARCHAR(255),
  external_authorization_service_default_label VARCHAR(255),
  pages_domain_verification_enabled BOOLEAN NOT NULL,
  user_default_internal_regex VARCHAR(255),
  external_authorization_service_timeout FLOAT,
  external_auth_client_cert VARCHAR(255),
  encrypted_external_auth_client_key VARCHAR(255),
  encrypted_external_auth_client_key_iv VARCHAR(255),
  encrypted_external_auth_client_key_pass VARCHAR(255),
  encrypted_external_auth_client_key_pass_iv VARCHAR(255),
  email_additional_text VARCHAR(255),
  enforce_terms BOOLEAN,
  file_template_project_id INTEGER,
  pseudonymizer_enabled BOOLEAN NOT NULL,
  hide_third_party_offers BOOLEAN NOT NULL,
  snowplow_enabled BOOLEAN NOT NULL,
  snowplow_collector_hostname VARCHAR(255),
  snowplow_cookie_domain VARCHAR(255),
  instance_statistics_visibility_private BOOLEAN NOT NULL,
  web_ide_clientside_preview_enabled BOOLEAN NOT NULL,
  user_show_add_ssh_key_message BOOLEAN NOT NULL,
  custom_project_templates_group_id INTEGER,
  usage_stats_set_by_user_id INTEGER,
  receive_max_input_size INTEGER,
  diff_max_patch_bytes INTEGER NOT NULL,
  archive_builds_in_seconds INTEGER,
  commit_email_hostname VARCHAR(255),
  protected_ci_variables BOOLEAN NOT NULL,
  runners_registration_token_encrypted VARCHAR(255),
  local_markdown_version INTEGER NOT NULL,
  first_day_of_week INTEGER NOT NULL,
  elasticsearch_limit_indexing BOOLEAN NOT NULL,
  default_project_creation INTEGER NOT NULL,
  lets_encrypt_notification_email VARCHAR(255),
  lets_encrypt_terms_of_service_accepted BOOLEAN NOT NULL,
  geo_node_allowed_ips VARCHAR(255),
  elasticsearch_shards INTEGER NOT NULL,
  elasticsearch_replicas INTEGER NOT NULL,
  encrypted_lets_encrypt_private_key VARCHAR(255),
  encrypted_lets_encrypt_private_key_iv VARCHAR(255),
  required_instance_ci_template VARCHAR(255),
  dns_rebinding_protection_enabled BOOLEAN NOT NULL,
  default_project_deletion_protection BOOLEAN NOT NULL,
  grafana_enabled BOOLEAN NOT NULL,
  lock_memberships_to_ldap BOOLEAN NOT NULL,
  time_tracking_limit_to_hours BOOLEAN NOT NULL,
  grafana_url VARCHAR(255) NOT NULL,
  login_recaptcha_protection_enabled BOOLEAN NOT NULL,
  outbound_local_requests_whitelist VARCHAR(255) NOT NULL,
  raw_blob_request_limit INTEGER NOT NULL,
  allow_local_requests_from_web_hooks_and_services BOOLEAN NOT NULL,
  allow_local_requests_from_system_hooks BOOLEAN NOT NULL,
  instance_administration_project_id BIGINT,
  asset_proxy_enabled BOOLEAN NOT NULL,
  asset_proxy_url VARCHAR(255),
  asset_proxy_whitelist VARCHAR(255),
  encrypted_asset_proxy_secret_key VARCHAR(255),
  encrypted_asset_proxy_secret_key_iv VARCHAR(255),
  static_objects_external_storage_url VARCHAR(255),
  static_objects_external_storage_auth_token VARCHAR(255),
  max_personal_access_token_lifetime INTEGER,
  throttle_protected_paths_enabled BOOLEAN NOT NULL,
  throttle_protected_paths_requests_per_period INTEGER NOT NULL,
  throttle_protected_paths_period_in_seconds INTEGER NOT NULL,
  protected_paths VARCHAR(255),
  throttle_incident_management_notification_enabled BOOLEAN NOT NULL,
  throttle_incident_management_notification_period_in_seconds INTEGER,
  throttle_incident_management_notification_per_period INTEGER,
  snowplow_iglu_registry_url VARCHAR(255),
  push_event_hooks_limit INTEGER NOT NULL,
  push_event_activities_limit INTEGER NOT NULL,
  custom_http_clone_url_root VARCHAR(255),
  deletion_adjourned_period INTEGER NOT NULL,
  license_trial_ends_on DATE,
  eks_integration_enabled BOOLEAN NOT NULL,
  eks_account_id VARCHAR(255),
  eks_access_key_id VARCHAR(255),
  encrypted_eks_secret_access_key_iv VARCHAR(255),
  encrypted_eks_secret_access_key VARCHAR(255),
  snowplow_app_id VARCHAR(255),
  productivity_analytics_start_date TIMESTAMP,
  default_ci_config_path VARCHAR(255),
  sourcegraph_enabled BOOLEAN NOT NULL,
  sourcegraph_url VARCHAR(255),
  sourcegraph_public_only BOOLEAN NOT NULL,
  snippet_size_limit BIGINT NOT NULL,
  minimum_password_length INTEGER NOT NULL,
  encrypted_akismet_api_key VARCHAR(255),
  encrypted_akismet_api_key_iv VARCHAR(255),
  encrypted_elasticsearch_aws_secret_access_key VARCHAR(255),
  encrypted_elasticsearch_aws_secret_access_key_iv VARCHAR(255),
  encrypted_recaptcha_private_key VARCHAR(255),
  encrypted_recaptcha_private_key_iv VARCHAR(255),
  encrypted_recaptcha_site_key VARCHAR(255),
  encrypted_recaptcha_site_key_iv VARCHAR(255),
  encrypted_slack_app_secret VARCHAR(255),
  encrypted_slack_app_secret_iv VARCHAR(255),
  encrypted_slack_app_verification_token VARCHAR(255),
  encrypted_slack_app_verification_token_iv VARCHAR(255),
  force_pages_access_control BOOLEAN NOT NULL,
  updating_name_disabled_for_users BOOLEAN NOT NULL,
  instance_administrators_group_id INTEGER,
  elasticsearch_indexed_field_length_limit INTEGER NOT NULL,
  elasticsearch_max_bulk_size_mb INTEGER NOT NULL,
  elasticsearch_max_bulk_concurrency INTEGER NOT NULL,
  disable_overriding_approvers_per_merge_request BOOLEAN NOT NULL,
  prevent_merge_requests_author_approval BOOLEAN NOT NULL,
  prevent_merge_requests_committers_approval BOOLEAN NOT NULL,
  email_restrictions_enabled BOOLEAN NOT NULL,
  email_restrictions VARCHAR(255),
  npm_package_requests_forwarding BOOLEAN NOT NULL,
  namespace_storage_size_limit BIGINT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE approval_merge_request_rule_sources (
  id BIGINT NOT NULL,
  approval_merge_request_rule_id BIGINT NOT NULL,
  approval_project_rule_id BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (approval_merge_request_rule_id)
);

CREATE TABLE approval_merge_request_rules (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  merge_request_id INTEGER NOT NULL,
  approvals_required INTEGER NOT NULL,
  code_owner BOOLEAN NOT NULL,
  name VARCHAR(255) NOT NULL,
  rule_type INTEGER NOT NULL,
  report_type INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE approval_merge_request_rules_approved_approvers (
  id BIGINT NOT NULL,
  approval_merge_request_rule_id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (approval_merge_request_rule_id, user_id)
);

CREATE TABLE approval_merge_request_rules_groups (
  id BIGINT NOT NULL,
  approval_merge_request_rule_id BIGINT NOT NULL,
  group_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (approval_merge_request_rule_id, group_id)
);

CREATE TABLE approval_merge_request_rules_users (
  id BIGINT NOT NULL,
  approval_merge_request_rule_id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (approval_merge_request_rule_id, user_id)
);

CREATE TABLE approval_project_rules (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id INTEGER NOT NULL,
  approvals_required INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  rule_type INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE approval_project_rules_groups (
  id BIGINT NOT NULL,
  approval_project_rule_id BIGINT NOT NULL,
  group_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (approval_project_rule_id, group_id)
);

CREATE TABLE approval_project_rules_protected_branches (
  approval_project_rule_id BIGINT NOT NULL,
  protected_branch_id BIGINT NOT NULL,
  UNIQUE (approval_project_rule_id, protected_branch_id)
);

CREATE TABLE approval_project_rules_users (
  id BIGINT NOT NULL,
  approval_project_rule_id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (approval_project_rule_id, user_id)
);

CREATE TABLE approvals (
  id INTEGER NOT NULL,
  merge_request_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (user_id, merge_request_id)
);

CREATE TABLE approver_groups (
  id INTEGER NOT NULL,
  target_id INTEGER NOT NULL,
  target_type VARCHAR(255) NOT NULL,
  group_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE approvers (
  id INTEGER NOT NULL,
  target_id INTEGER NOT NULL,
  target_type VARCHAR(255),
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE ar_internal_metadata (
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY ("key")
);

CREATE TABLE audit_events (
  id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  "type" VARCHAR(255) NOT NULL,
  entity_id INTEGER NOT NULL,
  entity_type VARCHAR(255) NOT NULL,
  details VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE award_emoji (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  user_id INTEGER,
  awardable_id INTEGER,
  awardable_type VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE aws_roles (
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  role_arn VARCHAR(255) NOT NULL,
  role_external_id VARCHAR(255) NOT NULL,
  PRIMARY KEY (user_id),
  UNIQUE (role_external_id),
  UNIQUE (user_id)
);

CREATE TABLE badges (
  id INTEGER NOT NULL,
  link_url VARCHAR(255) NOT NULL,
  image_url VARCHAR(255) NOT NULL,
  project_id INTEGER,
  group_id INTEGER,
  "type" VARCHAR(255) NOT NULL,
  name VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE board_assignees (
  id INTEGER NOT NULL,
  board_id INTEGER NOT NULL,
  assignee_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (board_id, assignee_id)
);

CREATE TABLE board_group_recent_visits (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id INTEGER,
  board_id INTEGER,
  group_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (user_id, group_id, board_id)
);

CREATE TABLE board_labels (
  id INTEGER NOT NULL,
  board_id INTEGER NOT NULL,
  label_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (board_id, label_id)
);

CREATE TABLE board_project_recent_visits (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id INTEGER,
  project_id INTEGER,
  board_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (user_id, project_id, board_id)
);

CREATE TABLE boards (
  id INTEGER NOT NULL,
  project_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  name VARCHAR(255) NOT NULL,
  milestone_id INTEGER,
  group_id INTEGER,
  weight INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE broadcast_messages (
  id INTEGER NOT NULL,
  message VARCHAR(255) NOT NULL,
  starts_at TIMESTAMP NOT NULL,
  ends_at TIMESTAMP NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  color VARCHAR(255),
  font VARCHAR(255),
  message_html VARCHAR(255) NOT NULL,
  cached_markdown_version INTEGER,
  target_path VARCHAR(255),
  broadcast_type INTEGER NOT NULL,
  dismissable BOOLEAN,
  PRIMARY KEY (id)
);

CREATE TABLE chat_names (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  service_id INTEGER NOT NULL,
  team_id VARCHAR(255) NOT NULL,
  team_domain VARCHAR(255),
  chat_id VARCHAR(255) NOT NULL,
  chat_name VARCHAR(255),
  last_used_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (service_id, team_id, chat_id),
  UNIQUE (user_id, service_id)
);

CREATE TABLE chat_teams (
  id INTEGER NOT NULL,
  namespace_id INTEGER NOT NULL,
  team_id VARCHAR(255),
  name VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (namespace_id)
);

CREATE TABLE ci_build_needs (
  id INTEGER NOT NULL,
  build_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  artifacts BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (build_id, name)
);

CREATE TABLE ci_build_trace_chunks (
  id BIGINT NOT NULL,
  build_id INTEGER NOT NULL,
  chunk_index INTEGER NOT NULL,
  data_store INTEGER NOT NULL,
  raw_data VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (build_id, chunk_index)
);

CREATE TABLE ci_build_trace_section_names (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, name)
);

CREATE TABLE ci_build_trace_sections (
  project_id INTEGER NOT NULL,
  date_start TIMESTAMP NOT NULL,
  date_end TIMESTAMP NOT NULL,
  byte_start BIGINT NOT NULL,
  byte_end BIGINT NOT NULL,
  build_id INTEGER NOT NULL,
  section_name_id INTEGER NOT NULL,
  UNIQUE (build_id, section_name_id)
);

CREATE TABLE ci_builds (
  id INTEGER NOT NULL,
  status VARCHAR(255),
  finished_at TIMESTAMP,
  trace VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  started_at TIMESTAMP,
  runner_id INTEGER,
  coverage FLOAT,
  commit_id INTEGER,
  commands VARCHAR(255),
  name VARCHAR(255),
  options VARCHAR(255),
  allow_failure BOOLEAN NOT NULL,
  stage VARCHAR(255),
  trigger_request_id INTEGER,
  stage_idx INTEGER,
  tag BOOLEAN,
  "ref" VARCHAR(255),
  user_id INTEGER,
  "type" VARCHAR(255),
  target_url VARCHAR(255),
  description VARCHAR(255),
  artifacts_file VARCHAR(255),
  project_id INTEGER,
  artifacts_metadata VARCHAR(255),
  erased_by_id INTEGER,
  erased_at TIMESTAMP,
  artifacts_expire_at TIMESTAMP,
  environment VARCHAR(255),
  artifacts_size BIGINT,
  "when" VARCHAR(255),
  yaml_variables VARCHAR(255),
  queued_at TIMESTAMP,
  token VARCHAR(255),
  lock_version INTEGER,
  coverage_regex VARCHAR(255),
  auto_canceled_by_id INTEGER,
  retried BOOLEAN,
  stage_id INTEGER,
  artifacts_file_store INTEGER,
  artifacts_metadata_store INTEGER,
  protected BOOLEAN,
  failure_reason INTEGER,
  scheduled_at TIMESTAMP,
  token_encrypted VARCHAR(255),
  upstream_pipeline_id INTEGER,
  resource_group_id BIGINT,
  waiting_for_resource_at TIMESTAMP,
  processed BOOLEAN,
  scheduling_type INTEGER,
  PRIMARY KEY (id),
  UNIQUE (token)
);

CREATE TABLE ci_builds_metadata (
  id INTEGER NOT NULL,
  build_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  timeout INTEGER,
  timeout_source INTEGER NOT NULL,
  interruptible BOOLEAN,
  config_options VARCHAR(255),
  config_variables VARCHAR(255),
  has_exposed_artifacts BOOLEAN,
  environment_auto_stop_in VARCHAR(255),
  expanded_environment_name VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (build_id)
);

CREATE TABLE ci_builds_runner_session (
  id BIGINT NOT NULL,
  build_id INTEGER NOT NULL,
  url VARCHAR(255) NOT NULL,
  certificate VARCHAR(255),
  "authorization" VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (build_id)
);

CREATE TABLE ci_daily_report_results (
  id BIGINT NOT NULL,
  "date" DATE NOT NULL,
  project_id BIGINT NOT NULL,
  last_pipeline_id BIGINT NOT NULL,
  "value" FLOAT NOT NULL,
  param_type BIGINT NOT NULL,
  ref_path VARCHAR(255) NOT NULL,
  title VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, ref_path, param_type, "date", title)
);

CREATE TABLE ci_group_variables (
  id INTEGER NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  encrypted_value VARCHAR(255),
  encrypted_value_salt VARCHAR(255),
  encrypted_value_iv VARCHAR(255),
  group_id INTEGER NOT NULL,
  protected BOOLEAN NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  masked BOOLEAN NOT NULL,
  variable_type INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, "key")
);

CREATE TABLE ci_job_artifacts (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  job_id INTEGER NOT NULL,
  file_type INTEGER NOT NULL,
  size BIGINT,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  expire_at TIMESTAMP,
  file VARCHAR(255),
  file_store INTEGER,
  file_sha256 VARCHAR(255),
  file_format INTEGER,
  file_location INTEGER,
  PRIMARY KEY (id),
  UNIQUE (job_id, file_type)
);

CREATE TABLE ci_job_variables (
  id BIGINT NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  encrypted_value VARCHAR(255),
  encrypted_value_iv VARCHAR(255),
  job_id BIGINT NOT NULL,
  variable_type INTEGER NOT NULL,
  source INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE ("key", job_id)
);

CREATE TABLE ci_pipeline_chat_data (
  id BIGINT NOT NULL,
  pipeline_id INTEGER NOT NULL,
  chat_name_id INTEGER NOT NULL,
  response_url VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (pipeline_id)
);

CREATE TABLE ci_pipeline_schedule_variables (
  id INTEGER NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  encrypted_value VARCHAR(255),
  encrypted_value_salt VARCHAR(255),
  encrypted_value_iv VARCHAR(255),
  pipeline_schedule_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  variable_type INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (pipeline_schedule_id, "key")
);

CREATE TABLE ci_pipeline_schedules (
  id INTEGER NOT NULL,
  description VARCHAR(255),
  "ref" VARCHAR(255),
  cron VARCHAR(255),
  cron_timezone VARCHAR(255),
  next_run_at TIMESTAMP,
  project_id INTEGER,
  owner_id INTEGER,
  active BOOLEAN,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE ci_pipeline_variables (
  id INTEGER NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  encrypted_value VARCHAR(255),
  encrypted_value_salt VARCHAR(255),
  encrypted_value_iv VARCHAR(255),
  pipeline_id INTEGER NOT NULL,
  variable_type INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (pipeline_id, "key")
);

CREATE TABLE ci_pipelines (
  id INTEGER NOT NULL,
  "ref" VARCHAR(255),
  sha VARCHAR(255),
  before_sha VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  tag BOOLEAN,
  yaml_errors VARCHAR(255),
  committed_at TIMESTAMP,
  project_id INTEGER,
  status VARCHAR(255),
  started_at TIMESTAMP,
  finished_at TIMESTAMP,
  duration INTEGER,
  user_id INTEGER,
  lock_version INTEGER,
  auto_canceled_by_id INTEGER,
  pipeline_schedule_id INTEGER,
  source INTEGER,
  config_source INTEGER,
  protected BOOLEAN,
  failure_reason INTEGER,
  iid INTEGER,
  merge_request_id INTEGER,
  source_sha VARCHAR(255),
  target_sha VARCHAR(255),
  external_pull_request_id BIGINT,
  PRIMARY KEY (id)
);

CREATE TABLE ci_pipelines_config (
  pipeline_id BIGINT NOT NULL,
  content VARCHAR(255) NOT NULL,
  PRIMARY KEY (pipeline_id)
);

CREATE TABLE ci_refs (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  lock_version INTEGER,
  last_updated_by_pipeline_id INTEGER,
  tag BOOLEAN NOT NULL,
  "ref" VARCHAR(255) NOT NULL,
  status VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, "ref", tag)
);

CREATE TABLE ci_resource_groups (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id BIGINT NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, "key")
);

CREATE TABLE ci_resources (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  resource_group_id BIGINT NOT NULL,
  build_id BIGINT,
  PRIMARY KEY (id),
  UNIQUE (resource_group_id, build_id)
);

CREATE TABLE ci_runner_namespaces (
  id INTEGER NOT NULL,
  runner_id INTEGER,
  namespace_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (runner_id, namespace_id)
);

CREATE TABLE ci_runner_projects (
  id INTEGER NOT NULL,
  runner_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  project_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE ci_runners (
  id INTEGER NOT NULL,
  token VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  description VARCHAR(255),
  contacted_at TIMESTAMP,
  active BOOLEAN NOT NULL,
  is_shared BOOLEAN,
  name VARCHAR(255),
  version VARCHAR(255),
  revision VARCHAR(255),
  platform VARCHAR(255),
  architecture VARCHAR(255),
  run_untagged BOOLEAN NOT NULL,
  locked BOOLEAN NOT NULL,
  access_level INTEGER NOT NULL,
  ip_address VARCHAR(255),
  maximum_timeout INTEGER,
  runner_type INTEGER NOT NULL,
  token_encrypted VARCHAR(255),
  public_projects_minutes_cost_factor FLOAT NOT NULL,
  private_projects_minutes_cost_factor FLOAT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE ci_sources_pipelines (
  id INTEGER NOT NULL,
  project_id INTEGER,
  pipeline_id INTEGER,
  source_project_id INTEGER,
  source_job_id INTEGER,
  source_pipeline_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE ci_sources_projects (
  id BIGINT NOT NULL,
  pipeline_id BIGINT NOT NULL,
  source_project_id BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (source_project_id, pipeline_id)
);

CREATE TABLE ci_stages (
  id INTEGER NOT NULL,
  project_id INTEGER,
  pipeline_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  name VARCHAR(255),
  status INTEGER,
  lock_version INTEGER,
  "position" INTEGER,
  PRIMARY KEY (id),
  UNIQUE (pipeline_id, name)
);

CREATE TABLE ci_subscriptions_projects (
  id BIGINT NOT NULL,
  downstream_project_id BIGINT NOT NULL,
  upstream_project_id BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (downstream_project_id, upstream_project_id)
);

CREATE TABLE ci_trigger_requests (
  id INTEGER NOT NULL,
  trigger_id INTEGER NOT NULL,
  variables VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  commit_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE ci_triggers (
  id INTEGER NOT NULL,
  token VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  project_id INTEGER,
  owner_id INTEGER NOT NULL,
  description VARCHAR(255),
  "ref" VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE ci_variables (
  id INTEGER NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  encrypted_value VARCHAR(255),
  encrypted_value_salt VARCHAR(255),
  encrypted_value_iv VARCHAR(255),
  project_id INTEGER NOT NULL,
  protected BOOLEAN NOT NULL,
  environment_scope VARCHAR(255) NOT NULL,
  masked BOOLEAN NOT NULL,
  variable_type INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, "key", environment_scope)
);

CREATE TABLE cluster_groups (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (cluster_id, group_id)
);

CREATE TABLE cluster_platforms_kubernetes (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  api_url VARCHAR(255),
  ca_cert VARCHAR(255),
  namespace VARCHAR(255),
  username VARCHAR(255),
  encrypted_password VARCHAR(255),
  encrypted_password_iv VARCHAR(255),
  encrypted_token VARCHAR(255),
  encrypted_token_iv VARCHAR(255),
  authorization_type INTEGER,
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE cluster_projects (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE cluster_providers_aws (
  id BIGINT NOT NULL,
  cluster_id BIGINT NOT NULL,
  created_by_user_id INTEGER,
  num_nodes INTEGER NOT NULL,
  status INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  key_name VARCHAR(255) NOT NULL,
  role_arn VARCHAR(255) NOT NULL,
  region VARCHAR(255) NOT NULL,
  vpc_id VARCHAR(255) NOT NULL,
  subnet_ids VARCHAR(255) NOT NULL,
  security_group_id VARCHAR(255) NOT NULL,
  instance_type VARCHAR(255) NOT NULL,
  access_key_id VARCHAR(255),
  encrypted_secret_access_key_iv VARCHAR(255),
  encrypted_secret_access_key VARCHAR(255),
  session_token VARCHAR(255),
  status_reason VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE cluster_providers_gcp (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  status INTEGER,
  num_nodes INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  status_reason VARCHAR(255),
  gcp_project_id VARCHAR(255) NOT NULL,
  zone VARCHAR(255) NOT NULL,
  machine_type VARCHAR(255),
  operation_id VARCHAR(255),
  endpoint VARCHAR(255),
  encrypted_access_token VARCHAR(255),
  encrypted_access_token_iv VARCHAR(255),
  legacy_abac BOOLEAN NOT NULL,
  cloud_run BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters (
  id INTEGER NOT NULL,
  user_id INTEGER,
  provider_type INTEGER,
  platform_type INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  enabled BOOLEAN,
  name VARCHAR(255) NOT NULL,
  environment_scope VARCHAR(255) NOT NULL,
  cluster_type INTEGER NOT NULL,
  domain VARCHAR(255),
  managed BOOLEAN NOT NULL,
  namespace_per_environment BOOLEAN NOT NULL,
  management_project_id INTEGER,
  cleanup_status INTEGER NOT NULL,
  cleanup_status_reason VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE clusters_applications_cert_managers (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  status INTEGER NOT NULL,
  version VARCHAR(255) NOT NULL,
  email VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  status_reason VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters_applications_crossplane (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  cluster_id BIGINT NOT NULL,
  status INTEGER NOT NULL,
  version VARCHAR(255) NOT NULL,
  stack VARCHAR(255) NOT NULL,
  status_reason VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters_applications_elastic_stacks (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  cluster_id BIGINT NOT NULL,
  status INTEGER NOT NULL,
  version VARCHAR(255) NOT NULL,
  status_reason VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters_applications_helm (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  status INTEGER NOT NULL,
  version VARCHAR(255) NOT NULL,
  status_reason VARCHAR(255),
  encrypted_ca_key VARCHAR(255),
  encrypted_ca_key_iv VARCHAR(255),
  ca_cert VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters_applications_ingress (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  status INTEGER NOT NULL,
  ingress_type INTEGER NOT NULL,
  version VARCHAR(255) NOT NULL,
  cluster_ip VARCHAR(255),
  status_reason VARCHAR(255),
  external_ip VARCHAR(255),
  external_hostname VARCHAR(255),
  modsecurity_enabled BOOLEAN,
  modsecurity_mode INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters_applications_jupyter (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  oauth_application_id INTEGER,
  status INTEGER NOT NULL,
  version VARCHAR(255) NOT NULL,
  hostname VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  status_reason VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters_applications_knative (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  status INTEGER NOT NULL,
  version VARCHAR(255) NOT NULL,
  hostname VARCHAR(255),
  status_reason VARCHAR(255),
  external_ip VARCHAR(255),
  external_hostname VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters_applications_prometheus (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  status INTEGER NOT NULL,
  version VARCHAR(255) NOT NULL,
  status_reason VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  last_update_started_at TIMESTAMP,
  encrypted_alert_manager_token VARCHAR(255),
  encrypted_alert_manager_token_iv VARCHAR(255),
  healthy BOOLEAN,
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters_applications_runners (
  id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  runner_id INTEGER,
  status INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  version VARCHAR(255) NOT NULL,
  status_reason VARCHAR(255),
  privileged BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (cluster_id)
);

CREATE TABLE clusters_kubernetes_namespaces (
  id BIGINT NOT NULL,
  cluster_id INTEGER NOT NULL,
  project_id INTEGER,
  cluster_project_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  encrypted_service_account_token VARCHAR(255),
  encrypted_service_account_token_iv VARCHAR(255),
  namespace VARCHAR(255) NOT NULL,
  service_account_name VARCHAR(255),
  environment_id BIGINT,
  PRIMARY KEY (id),
  UNIQUE (cluster_id, project_id, environment_id),
  UNIQUE (cluster_id, namespace)
);

CREATE TABLE commit_user_mentions (
  id BIGINT NOT NULL,
  note_id INTEGER NOT NULL,
  mentioned_users_ids INTEGER,
  mentioned_projects_ids INTEGER,
  mentioned_groups_ids INTEGER,
  commit_id VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (note_id)
);

CREATE TABLE container_expiration_policies (
  project_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  next_run_at TIMESTAMP,
  name_regex VARCHAR(255),
  cadence VARCHAR(255) NOT NULL,
  older_than VARCHAR(255),
  keep_n INTEGER,
  enabled BOOLEAN NOT NULL,
  PRIMARY KEY (project_id)
);

CREATE TABLE container_repositories (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, name)
);

CREATE TABLE conversational_development_index_metrics (
  id INTEGER NOT NULL,
  leader_issues FLOAT NOT NULL,
  instance_issues FLOAT NOT NULL,
  leader_notes FLOAT NOT NULL,
  instance_notes FLOAT NOT NULL,
  leader_milestones FLOAT NOT NULL,
  instance_milestones FLOAT NOT NULL,
  leader_boards FLOAT NOT NULL,
  instance_boards FLOAT NOT NULL,
  leader_merge_requests FLOAT NOT NULL,
  instance_merge_requests FLOAT NOT NULL,
  leader_ci_pipelines FLOAT NOT NULL,
  instance_ci_pipelines FLOAT NOT NULL,
  leader_environments FLOAT NOT NULL,
  instance_environments FLOAT NOT NULL,
  leader_deployments FLOAT NOT NULL,
  instance_deployments FLOAT NOT NULL,
  leader_projects_prometheus_active FLOAT NOT NULL,
  instance_projects_prometheus_active FLOAT NOT NULL,
  leader_service_desk_issues FLOAT NOT NULL,
  instance_service_desk_issues FLOAT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  percentage_boards FLOAT NOT NULL,
  percentage_ci_pipelines FLOAT NOT NULL,
  percentage_deployments FLOAT NOT NULL,
  percentage_environments FLOAT NOT NULL,
  percentage_issues FLOAT NOT NULL,
  percentage_merge_requests FLOAT NOT NULL,
  percentage_milestones FLOAT NOT NULL,
  percentage_notes FLOAT NOT NULL,
  percentage_projects_prometheus_active FLOAT NOT NULL,
  percentage_service_desk_issues FLOAT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE dependency_proxy_blobs (
  id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  size BIGINT,
  file_store INTEGER,
  file_name VARCHAR(255) NOT NULL,
  file VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE dependency_proxy_group_settings (
  id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  enabled BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE deploy_keys_projects (
  id INTEGER NOT NULL,
  deploy_key_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  can_push BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE deploy_tokens (
  id INTEGER NOT NULL,
  revoked BOOLEAN,
  read_repository BOOLEAN NOT NULL,
  read_registry BOOLEAN NOT NULL,
  expires_at TIMESTAMP NOT NULL,
  created_at TIMESTAMP NOT NULL,
  name VARCHAR(255) NOT NULL,
  token VARCHAR(255),
  username VARCHAR(255),
  token_encrypted VARCHAR(255),
  deploy_token_type INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (token),
  UNIQUE (token_encrypted)
);

CREATE TABLE deployment_clusters (
  deployment_id INTEGER NOT NULL,
  cluster_id INTEGER NOT NULL,
  kubernetes_namespace VARCHAR(255),
  PRIMARY KEY (deployment_id),
  UNIQUE (cluster_id, deployment_id)
);

CREATE TABLE deployment_merge_requests (
  deployment_id INTEGER NOT NULL,
  merge_request_id INTEGER NOT NULL,
  environment_id INTEGER,
  UNIQUE (deployment_id, merge_request_id),
  UNIQUE (environment_id, merge_request_id)
);

CREATE TABLE deployments (
  id INTEGER NOT NULL,
  iid INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  environment_id INTEGER NOT NULL,
  "ref" VARCHAR(255) NOT NULL,
  tag BOOLEAN NOT NULL,
  sha VARCHAR(255) NOT NULL,
  user_id INTEGER,
  deployable_id INTEGER,
  deployable_type VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  on_stop VARCHAR(255),
  status INTEGER NOT NULL,
  finished_at TIMESTAMP,
  cluster_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (project_id, iid)
);

CREATE TABLE description_versions (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  issue_id INTEGER,
  merge_request_id INTEGER,
  epic_id INTEGER,
  description VARCHAR(255),
  deleted_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE design_management_designs (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  issue_id INTEGER,
  filename VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (issue_id, filename)
);

CREATE TABLE design_management_designs_versions (
  id BIGINT NOT NULL,
  design_id BIGINT NOT NULL,
  version_id BIGINT NOT NULL,
  event INTEGER NOT NULL,
  image_v432x230 VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (design_id, version_id)
);

CREATE TABLE design_management_versions (
  id BIGINT NOT NULL,
  sha VARCHAR(255) NOT NULL,
  issue_id BIGINT,
  created_at TIMESTAMP NOT NULL,
  author_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (sha, issue_id)
);

CREATE TABLE design_user_mentions (
  id BIGINT NOT NULL,
  design_id INTEGER NOT NULL,
  note_id INTEGER NOT NULL,
  mentioned_users_ids INTEGER,
  mentioned_projects_ids INTEGER,
  mentioned_groups_ids INTEGER,
  PRIMARY KEY (id),
  UNIQUE (note_id)
);

CREATE TABLE draft_notes (
  id BIGINT NOT NULL,
  merge_request_id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  resolve_discussion BOOLEAN NOT NULL,
  discussion_id VARCHAR(255),
  note VARCHAR(255) NOT NULL,
  "position" VARCHAR(255),
  original_position VARCHAR(255),
  change_position VARCHAR(255),
  commit_id VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE elasticsearch_indexed_namespaces (
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  namespace_id INTEGER,
  UNIQUE (namespace_id)
);

CREATE TABLE elasticsearch_indexed_projects (
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id INTEGER,
  UNIQUE (project_id)
);

CREATE TABLE emails (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  email VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  confirmation_token VARCHAR(255),
  confirmed_at TIMESTAMP,
  confirmation_sent_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (confirmation_token),
  UNIQUE (email)
);

CREATE TABLE environments (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  external_url VARCHAR(255),
  environment_type VARCHAR(255),
  state VARCHAR(255) NOT NULL,
  slug VARCHAR(255) NOT NULL,
  auto_stop_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (project_id, name),
  UNIQUE (project_id, slug)
);

CREATE TABLE epic_issues (
  id INTEGER NOT NULL,
  epic_id INTEGER NOT NULL,
  issue_id INTEGER NOT NULL,
  relative_position INTEGER,
  PRIMARY KEY (id),
  UNIQUE (issue_id)
);

CREATE TABLE epic_metrics (
  id INTEGER NOT NULL,
  epic_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE epic_user_mentions (
  id BIGINT NOT NULL,
  epic_id INTEGER NOT NULL,
  note_id INTEGER,
  mentioned_users_ids INTEGER,
  mentioned_projects_ids INTEGER,
  mentioned_groups_ids INTEGER,
  PRIMARY KEY (id),
  UNIQUE (epic_id, note_id)
);

CREATE TABLE epics (
  id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  assignee_id INTEGER,
  iid INTEGER NOT NULL,
  cached_markdown_version INTEGER,
  updated_by_id INTEGER,
  last_edited_by_id INTEGER,
  lock_version INTEGER,
  start_date DATE,
  end_date DATE,
  last_edited_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  title VARCHAR(255) NOT NULL,
  title_html VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  description_html VARCHAR(255),
  start_date_sourcing_milestone_id INTEGER,
  due_date_sourcing_milestone_id INTEGER,
  start_date_fixed DATE,
  due_date_fixed DATE,
  start_date_is_fixed BOOLEAN,
  due_date_is_fixed BOOLEAN,
  closed_by_id INTEGER,
  closed_at TIMESTAMP,
  parent_id INTEGER,
  relative_position INTEGER,
  state_id INTEGER NOT NULL,
  start_date_sourcing_epic_id INTEGER,
  due_date_sourcing_epic_id INTEGER,
  health_status INTEGER,
  external_key VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE events (
  id INTEGER NOT NULL,
  project_id INTEGER,
  author_id INTEGER NOT NULL,
  target_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  action INTEGER NOT NULL,
  target_type VARCHAR(255),
  group_id BIGINT,
  PRIMARY KEY (id)
);

CREATE TABLE evidences (
  id BIGINT NOT NULL,
  release_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  summary_sha VARCHAR(255),
  summary VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE external_pull_requests (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id BIGINT NOT NULL,
  pull_request_iid INTEGER NOT NULL,
  status INTEGER NOT NULL,
  source_branch VARCHAR(255) NOT NULL,
  target_branch VARCHAR(255) NOT NULL,
  source_repository VARCHAR(255) NOT NULL,
  target_repository VARCHAR(255) NOT NULL,
  source_sha VARCHAR(255) NOT NULL,
  target_sha VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, source_branch, target_branch)
);

CREATE TABLE feature_gates (
  id INTEGER NOT NULL,
  feature_key VARCHAR(255) NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (feature_key, "key", "value")
);

CREATE TABLE features (
  id INTEGER NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE ("key")
);

CREATE TABLE fork_network_members (
  id INTEGER NOT NULL,
  fork_network_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  forked_from_project_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE fork_networks (
  id INTEGER NOT NULL,
  root_project_id INTEGER,
  deleted_root_project_name VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (root_project_id)
);

CREATE TABLE geo_cache_invalidation_events (
  id BIGINT NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_container_repository_updated_events (
  id BIGINT NOT NULL,
  container_repository_id INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_event_log (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  repository_updated_event_id BIGINT,
  repository_deleted_event_id BIGINT,
  repository_renamed_event_id BIGINT,
  repositories_changed_event_id BIGINT,
  repository_created_event_id BIGINT,
  hashed_storage_migrated_event_id BIGINT,
  lfs_object_deleted_event_id BIGINT,
  hashed_storage_attachments_event_id BIGINT,
  upload_deleted_event_id BIGINT,
  job_artifact_deleted_event_id BIGINT,
  reset_checksum_event_id BIGINT,
  cache_invalidation_event_id BIGINT,
  container_repository_updated_event_id BIGINT,
  geo_event_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE geo_events (
  id BIGINT NOT NULL,
  replicable_name VARCHAR(255) NOT NULL,
  event_name VARCHAR(255) NOT NULL,
  payload VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_hashed_storage_attachments_events (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  old_attachments_path VARCHAR(255) NOT NULL,
  new_attachments_path VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_hashed_storage_migrated_events (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  repository_storage_name VARCHAR(255) NOT NULL,
  old_disk_path VARCHAR(255) NOT NULL,
  new_disk_path VARCHAR(255) NOT NULL,
  old_wiki_disk_path VARCHAR(255) NOT NULL,
  new_wiki_disk_path VARCHAR(255) NOT NULL,
  old_storage_version INTEGER,
  new_storage_version INTEGER NOT NULL,
  old_design_disk_path VARCHAR(255),
  new_design_disk_path VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE geo_job_artifact_deleted_events (
  id BIGINT NOT NULL,
  job_artifact_id INTEGER NOT NULL,
  file_path VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_lfs_object_deleted_events (
  id BIGINT NOT NULL,
  lfs_object_id INTEGER NOT NULL,
  oid VARCHAR(255) NOT NULL,
  file_path VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_node_namespace_links (
  id INTEGER NOT NULL,
  geo_node_id INTEGER NOT NULL,
  namespace_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (geo_node_id, namespace_id)
);

CREATE TABLE geo_node_statuses (
  id INTEGER NOT NULL,
  geo_node_id INTEGER NOT NULL,
  db_replication_lag_seconds INTEGER,
  repositories_synced_count INTEGER,
  repositories_failed_count INTEGER,
  lfs_objects_count INTEGER,
  lfs_objects_synced_count INTEGER,
  lfs_objects_failed_count INTEGER,
  attachments_count INTEGER,
  attachments_synced_count INTEGER,
  attachments_failed_count INTEGER,
  last_event_id INTEGER,
  last_event_date TIMESTAMP,
  cursor_last_event_id INTEGER,
  cursor_last_event_date TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  last_successful_status_check_at TIMESTAMP,
  status_message VARCHAR(255),
  replication_slots_count INTEGER,
  replication_slots_used_count INTEGER,
  replication_slots_max_retained_wal_bytes BIGINT,
  wikis_synced_count INTEGER,
  wikis_failed_count INTEGER,
  job_artifacts_count INTEGER,
  job_artifacts_synced_count INTEGER,
  job_artifacts_failed_count INTEGER,
  version VARCHAR(255),
  revision VARCHAR(255),
  repositories_verified_count INTEGER,
  repositories_verification_failed_count INTEGER,
  wikis_verified_count INTEGER,
  wikis_verification_failed_count INTEGER,
  lfs_objects_synced_missing_on_primary_count INTEGER,
  job_artifacts_synced_missing_on_primary_count INTEGER,
  attachments_synced_missing_on_primary_count INTEGER,
  repositories_checksummed_count INTEGER,
  repositories_checksum_failed_count INTEGER,
  repositories_checksum_mismatch_count INTEGER,
  wikis_checksummed_count INTEGER,
  wikis_checksum_failed_count INTEGER,
  wikis_checksum_mismatch_count INTEGER,
  storage_configuration_digest VARCHAR(255),
  repositories_retrying_verification_count INTEGER,
  wikis_retrying_verification_count INTEGER,
  projects_count INTEGER,
  container_repositories_count INTEGER,
  container_repositories_synced_count INTEGER,
  container_repositories_failed_count INTEGER,
  container_repositories_registry_count INTEGER,
  design_repositories_count INTEGER,
  design_repositories_synced_count INTEGER,
  design_repositories_failed_count INTEGER,
  design_repositories_registry_count INTEGER,
  PRIMARY KEY (id),
  UNIQUE (geo_node_id)
);

CREATE TABLE geo_nodes (
  id INTEGER NOT NULL,
  "primary" BOOLEAN NOT NULL,
  oauth_application_id INTEGER,
  enabled BOOLEAN NOT NULL,
  access_key VARCHAR(255),
  encrypted_secret_access_key VARCHAR(255),
  encrypted_secret_access_key_iv VARCHAR(255),
  clone_url_prefix VARCHAR(255),
  files_max_capacity INTEGER NOT NULL,
  repos_max_capacity INTEGER NOT NULL,
  url VARCHAR(255) NOT NULL,
  selective_sync_type VARCHAR(255),
  selective_sync_shards VARCHAR(255),
  verification_max_capacity INTEGER NOT NULL,
  minimum_reverification_interval INTEGER NOT NULL,
  internal_url VARCHAR(255),
  name VARCHAR(255) NOT NULL,
  container_repositories_max_capacity INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  sync_object_storage BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE geo_repositories_changed_events (
  id BIGINT NOT NULL,
  geo_node_id INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_repository_created_events (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  repository_storage_name VARCHAR(255) NOT NULL,
  repo_path VARCHAR(255) NOT NULL,
  wiki_path VARCHAR(255),
  project_name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_repository_deleted_events (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  repository_storage_name VARCHAR(255) NOT NULL,
  deleted_path VARCHAR(255) NOT NULL,
  deleted_wiki_path VARCHAR(255),
  deleted_project_name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_repository_renamed_events (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  repository_storage_name VARCHAR(255) NOT NULL,
  old_path_with_namespace VARCHAR(255) NOT NULL,
  new_path_with_namespace VARCHAR(255) NOT NULL,
  old_wiki_path_with_namespace VARCHAR(255) NOT NULL,
  new_wiki_path_with_namespace VARCHAR(255) NOT NULL,
  old_path VARCHAR(255) NOT NULL,
  new_path VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_repository_updated_events (
  id BIGINT NOT NULL,
  branches_affected INTEGER NOT NULL,
  tags_affected INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  source INTEGER NOT NULL,
  new_branch BOOLEAN NOT NULL,
  remove_branch BOOLEAN NOT NULL,
  "ref" VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE geo_reset_checksum_events (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE geo_upload_deleted_events (
  id BIGINT NOT NULL,
  upload_id INTEGER NOT NULL,
  file_path VARCHAR(255) NOT NULL,
  model_id INTEGER NOT NULL,
  model_type VARCHAR(255) NOT NULL,
  uploader VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE gitlab_subscription_histories (
  id BIGINT NOT NULL,
  gitlab_subscription_created_at TIMESTAMP,
  gitlab_subscription_updated_at TIMESTAMP,
  start_date DATE,
  end_date DATE,
  trial_ends_on DATE,
  namespace_id INTEGER,
  hosted_plan_id INTEGER,
  max_seats_used INTEGER,
  seats INTEGER,
  trial BOOLEAN,
  change_type INTEGER,
  gitlab_subscription_id BIGINT NOT NULL,
  created_at TIMESTAMP,
  trial_starts_on DATE,
  auto_renew BOOLEAN,
  PRIMARY KEY (id)
);

CREATE TABLE gitlab_subscriptions (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  start_date DATE,
  end_date DATE,
  trial_ends_on DATE,
  namespace_id INTEGER,
  hosted_plan_id INTEGER,
  max_seats_used INTEGER,
  seats INTEGER,
  trial BOOLEAN,
  trial_starts_on DATE,
  auto_renew BOOLEAN,
  PRIMARY KEY (id),
  UNIQUE (namespace_id)
);

CREATE TABLE gpg_key_subkeys (
  id INTEGER NOT NULL,
  gpg_key_id INTEGER NOT NULL,
  keyid VARCHAR(255),
  fingerprint VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (fingerprint),
  UNIQUE (keyid)
);

CREATE TABLE gpg_keys (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id INTEGER,
  primary_keyid VARCHAR(255),
  fingerprint VARCHAR(255),
  "key" VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (fingerprint),
  UNIQUE (primary_keyid)
);

CREATE TABLE gpg_signatures (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id INTEGER,
  gpg_key_id INTEGER,
  commit_sha VARCHAR(255),
  gpg_key_primary_keyid VARCHAR(255),
  gpg_key_user_name VARCHAR(255),
  gpg_key_user_email VARCHAR(255),
  verification_status INTEGER NOT NULL,
  gpg_key_subkey_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (commit_sha)
);

CREATE TABLE grafana_integrations (
  id BIGINT NOT NULL,
  project_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  encrypted_token VARCHAR(255) NOT NULL,
  encrypted_token_iv VARCHAR(255) NOT NULL,
  grafana_url VARCHAR(255) NOT NULL,
  enabled BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE group_custom_attributes (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  group_id INTEGER NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, "key")
);

CREATE TABLE group_deletion_schedules (
  group_id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  marked_for_deletion_on DATE NOT NULL,
  PRIMARY KEY (group_id)
);

CREATE TABLE group_deploy_tokens (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  group_id BIGINT NOT NULL,
  deploy_token_id BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, deploy_token_id)
);

CREATE TABLE group_group_links (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  shared_group_id BIGINT NOT NULL,
  shared_with_group_id BIGINT NOT NULL,
  expires_at DATE,
  group_access INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (shared_group_id, shared_with_group_id)
);

CREATE TABLE historical_data (
  id INTEGER NOT NULL,
  "date" DATE NOT NULL,
  active_user_count INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE identities (
  id INTEGER NOT NULL,
  extern_uid VARCHAR(255),
  provider VARCHAR(255),
  user_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  secondary_extern_uid VARCHAR(255),
  saml_provider_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE import_export_uploads (
  id INTEGER NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id INTEGER,
  import_file VARCHAR(255),
  export_file VARCHAR(255),
  group_id BIGINT,
  PRIMARY KEY (id)
);

CREATE TABLE import_failures (
  id BIGINT NOT NULL,
  relation_index INTEGER,
  project_id BIGINT,
  created_at TIMESTAMP NOT NULL,
  relation_key VARCHAR(255),
  exception_class VARCHAR(255),
  correlation_id_value VARCHAR(255),
  exception_message VARCHAR(255),
  retry_count INTEGER,
  group_id INTEGER,
  source VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE index_statuses (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  indexed_at TIMESTAMP,
  note VARCHAR(255),
  last_commit VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  last_wiki_commit VARCHAR(255),
  wiki_indexed_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE insights (
  id INTEGER NOT NULL,
  namespace_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE internal_ids (
  id BIGINT NOT NULL,
  project_id INTEGER,
  usage INTEGER NOT NULL,
  "last_value" INTEGER NOT NULL,
  namespace_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE ip_restrictions (
  id BIGINT NOT NULL,
  group_id INTEGER NOT NULL,
  "range" VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE issue_assignees (
  user_id INTEGER NOT NULL,
  issue_id INTEGER NOT NULL,
  UNIQUE (issue_id, user_id)
);

CREATE TABLE issue_links (
  id INTEGER NOT NULL,
  source_id INTEGER NOT NULL,
  target_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  link_type INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (source_id, target_id)
);

CREATE TABLE issue_metrics (
  id INTEGER NOT NULL,
  issue_id INTEGER NOT NULL,
  first_mentioned_in_commit_at TIMESTAMP,
  first_associated_with_milestone_at TIMESTAMP,
  first_added_to_board_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE issue_tracker_data (
  id BIGINT NOT NULL,
  service_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  encrypted_project_url VARCHAR(255),
  encrypted_project_url_iv VARCHAR(255),
  encrypted_issues_url VARCHAR(255),
  encrypted_issues_url_iv VARCHAR(255),
  encrypted_new_issue_url VARCHAR(255),
  encrypted_new_issue_url_iv VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE issue_user_mentions (
  id BIGINT NOT NULL,
  issue_id INTEGER NOT NULL,
  note_id INTEGER,
  mentioned_users_ids INTEGER,
  mentioned_projects_ids INTEGER,
  mentioned_groups_ids INTEGER,
  PRIMARY KEY (id),
  UNIQUE (issue_id, note_id)
);

CREATE TABLE issues (
  id INTEGER NOT NULL,
  title VARCHAR(255),
  author_id INTEGER,
  project_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  description VARCHAR(255),
  milestone_id INTEGER,
  iid INTEGER,
  updated_by_id INTEGER,
  weight INTEGER,
  confidential BOOLEAN NOT NULL,
  due_date DATE,
  moved_to_id INTEGER,
  lock_version INTEGER,
  title_html VARCHAR(255),
  description_html VARCHAR(255),
  time_estimate INTEGER,
  relative_position INTEGER,
  service_desk_reply_to VARCHAR(255),
  cached_markdown_version INTEGER,
  last_edited_at TIMESTAMP,
  last_edited_by_id INTEGER,
  discussion_locked BOOLEAN,
  closed_at TIMESTAMP,
  closed_by_id INTEGER,
  state_id INTEGER NOT NULL,
  duplicated_to_id INTEGER,
  promoted_to_epic_id INTEGER,
  health_status INTEGER,
  external_key VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (project_id, iid)
);

CREATE TABLE issues_prometheus_alert_events (
  issue_id BIGINT NOT NULL,
  prometheus_alert_event_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  UNIQUE (issue_id, prometheus_alert_event_id)
);

CREATE TABLE issues_self_managed_prometheus_alert_events (
  issue_id BIGINT NOT NULL,
  self_managed_prometheus_alert_event_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  UNIQUE (issue_id, self_managed_prometheus_alert_event_id)
);

CREATE TABLE jira_connect_installations (
  id BIGINT NOT NULL,
  client_key VARCHAR(255),
  encrypted_shared_secret VARCHAR(255),
  encrypted_shared_secret_iv VARCHAR(255),
  base_url VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (client_key)
);

CREATE TABLE jira_connect_subscriptions (
  id BIGINT NOT NULL,
  jira_connect_installation_id BIGINT NOT NULL,
  namespace_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (jira_connect_installation_id, namespace_id)
);

CREATE TABLE jira_tracker_data (
  id BIGINT NOT NULL,
  service_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  encrypted_url VARCHAR(255),
  encrypted_url_iv VARCHAR(255),
  encrypted_api_url VARCHAR(255),
  encrypted_api_url_iv VARCHAR(255),
  encrypted_username VARCHAR(255),
  encrypted_username_iv VARCHAR(255),
  encrypted_password VARCHAR(255),
  encrypted_password_iv VARCHAR(255),
  jira_issue_transition_id VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE keys (
  id INTEGER NOT NULL,
  user_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  "key" VARCHAR(255),
  title VARCHAR(255),
  "type" VARCHAR(255),
  fingerprint VARCHAR(255),
  public BOOLEAN NOT NULL,
  last_used_at TIMESTAMP,
  fingerprint_sha256 VARCHAR(255),
  expires_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (fingerprint)
);

CREATE TABLE label_links (
  id INTEGER NOT NULL,
  label_id INTEGER,
  target_id INTEGER,
  target_type VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE label_priorities (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  label_id INTEGER NOT NULL,
  priority INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, label_id)
);

CREATE TABLE labels (
  id INTEGER NOT NULL,
  title VARCHAR(255),
  color VARCHAR(255),
  project_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  template BOOLEAN,
  description VARCHAR(255),
  description_html VARCHAR(255),
  "type" VARCHAR(255),
  group_id INTEGER,
  cached_markdown_version INTEGER,
  PRIMARY KEY (id),
  UNIQUE (group_id, project_id, title)
);

CREATE TABLE ldap_group_links (
  id INTEGER NOT NULL,
  cn VARCHAR(255),
  group_access INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  provider VARCHAR(255),
  "filter" VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE lfs_file_locks (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  path VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (project_id, path)
);

CREATE TABLE lfs_objects (
  id INTEGER NOT NULL,
  oid VARCHAR(255) NOT NULL,
  size BIGINT NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  file VARCHAR(255),
  file_store INTEGER,
  PRIMARY KEY (id),
  UNIQUE (oid)
);

CREATE TABLE lfs_objects_projects (
  id INTEGER NOT NULL,
  lfs_object_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  repository_type INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE licenses (
  id INTEGER NOT NULL,
  "data" VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE list_user_preferences (
  id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  list_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  collapsed BOOLEAN,
  PRIMARY KEY (id),
  UNIQUE (user_id, list_id)
);

CREATE TABLE lists (
  id INTEGER NOT NULL,
  board_id INTEGER NOT NULL,
  label_id INTEGER,
  list_type INTEGER NOT NULL,
  "position" INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id INTEGER,
  milestone_id INTEGER,
  max_issue_count INTEGER NOT NULL,
  max_issue_weight INTEGER NOT NULL,
  limit_metric VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (board_id, label_id)
);

CREATE TABLE members (
  id INTEGER NOT NULL,
  access_level INTEGER NOT NULL,
  source_id INTEGER NOT NULL,
  source_type VARCHAR(255) NOT NULL,
  user_id INTEGER,
  notification_level INTEGER NOT NULL,
  "type" VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  created_by_id INTEGER,
  invite_email VARCHAR(255),
  invite_token VARCHAR(255),
  invite_accepted_at TIMESTAMP,
  requested_at TIMESTAMP,
  expires_at DATE,
  ldap BOOLEAN NOT NULL,
  override BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (invite_token)
);

CREATE TABLE merge_request_assignees (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  merge_request_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (merge_request_id, user_id)
);

CREATE TABLE merge_request_blocks (
  id BIGINT NOT NULL,
  blocking_merge_request_id INTEGER NOT NULL,
  blocked_merge_request_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (blocking_merge_request_id, blocked_merge_request_id)
);

CREATE TABLE merge_request_context_commit_diff_files (
  sha VARCHAR(255) NOT NULL,
  relative_order INTEGER NOT NULL,
  new_file BOOLEAN NOT NULL,
  renamed_file BOOLEAN NOT NULL,
  deleted_file BOOLEAN NOT NULL,
  too_large BOOLEAN NOT NULL,
  a_mode VARCHAR(255) NOT NULL,
  b_mode VARCHAR(255) NOT NULL,
  new_path VARCHAR(255) NOT NULL,
  old_path VARCHAR(255) NOT NULL,
  diff VARCHAR(255),
  "binary" BOOLEAN,
  merge_request_context_commit_id BIGINT
);

CREATE TABLE merge_request_context_commits (
  id BIGINT NOT NULL,
  authored_date TIMESTAMP,
  committed_date TIMESTAMP,
  relative_order INTEGER NOT NULL,
  sha VARCHAR(255) NOT NULL,
  author_name VARCHAR(255),
  author_email VARCHAR(255),
  committer_name VARCHAR(255),
  committer_email VARCHAR(255),
  message VARCHAR(255),
  merge_request_id BIGINT,
  PRIMARY KEY (id),
  UNIQUE (merge_request_id, sha)
);

CREATE TABLE merge_request_diff_commits (
  authored_date TIMESTAMP,
  committed_date TIMESTAMP,
  merge_request_diff_id INTEGER NOT NULL,
  relative_order INTEGER NOT NULL,
  sha VARCHAR(255) NOT NULL,
  author_name VARCHAR(255),
  author_email VARCHAR(255),
  committer_name VARCHAR(255),
  committer_email VARCHAR(255),
  message VARCHAR(255),
  UNIQUE (merge_request_diff_id, relative_order)
);

CREATE TABLE merge_request_diff_files (
  merge_request_diff_id INTEGER NOT NULL,
  relative_order INTEGER NOT NULL,
  new_file BOOLEAN NOT NULL,
  renamed_file BOOLEAN NOT NULL,
  deleted_file BOOLEAN NOT NULL,
  too_large BOOLEAN NOT NULL,
  a_mode VARCHAR(255) NOT NULL,
  b_mode VARCHAR(255) NOT NULL,
  new_path VARCHAR(255) NOT NULL,
  old_path VARCHAR(255) NOT NULL,
  diff VARCHAR(255),
  "binary" BOOLEAN,
  external_diff_offset INTEGER,
  external_diff_size INTEGER,
  UNIQUE (merge_request_diff_id, relative_order)
);

CREATE TABLE merge_request_diffs (
  id INTEGER NOT NULL,
  state VARCHAR(255),
  merge_request_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  base_commit_sha VARCHAR(255),
  real_size VARCHAR(255),
  head_commit_sha VARCHAR(255),
  start_commit_sha VARCHAR(255),
  commits_count INTEGER,
  external_diff VARCHAR(255),
  external_diff_store INTEGER,
  stored_externally BOOLEAN,
  PRIMARY KEY (id)
);

CREATE TABLE merge_request_metrics (
  id INTEGER NOT NULL,
  merge_request_id INTEGER NOT NULL,
  latest_build_started_at TIMESTAMP,
  latest_build_finished_at TIMESTAMP,
  first_deployed_to_production_at TIMESTAMP,
  merged_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  pipeline_id INTEGER,
  merged_by_id INTEGER,
  latest_closed_by_id INTEGER,
  latest_closed_at TIMESTAMP,
  first_comment_at TIMESTAMP,
  first_commit_at TIMESTAMP,
  last_commit_at TIMESTAMP,
  diff_size INTEGER,
  modified_paths_size INTEGER,
  commits_count INTEGER,
  first_approved_at TIMESTAMP,
  first_reassigned_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE merge_request_user_mentions (
  id BIGINT NOT NULL,
  merge_request_id INTEGER NOT NULL,
  note_id INTEGER,
  mentioned_users_ids INTEGER,
  mentioned_projects_ids INTEGER,
  mentioned_groups_ids INTEGER,
  PRIMARY KEY (id),
  UNIQUE (merge_request_id, note_id)
);

CREATE TABLE merge_requests (
  id INTEGER NOT NULL,
  target_branch VARCHAR(255) NOT NULL,
  source_branch VARCHAR(255) NOT NULL,
  source_project_id INTEGER,
  author_id INTEGER,
  assignee_id INTEGER,
  title VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  milestone_id INTEGER,
  merge_status VARCHAR(255) NOT NULL,
  target_project_id INTEGER NOT NULL,
  iid INTEGER,
  description VARCHAR(255),
  updated_by_id INTEGER,
  merge_error VARCHAR(255),
  merge_params VARCHAR(255),
  merge_when_pipeline_succeeds BOOLEAN NOT NULL,
  merge_user_id INTEGER,
  merge_commit_sha VARCHAR(255),
  approvals_before_merge INTEGER,
  rebase_commit_sha VARCHAR(255),
  in_progress_merge_commit_sha VARCHAR(255),
  lock_version INTEGER,
  title_html VARCHAR(255),
  description_html VARCHAR(255),
  time_estimate INTEGER,
  squash BOOLEAN NOT NULL,
  cached_markdown_version INTEGER,
  last_edited_at TIMESTAMP,
  last_edited_by_id INTEGER,
  head_pipeline_id INTEGER,
  merge_jid VARCHAR(255),
  discussion_locked BOOLEAN,
  latest_merge_request_diff_id INTEGER,
  allow_maintainer_to_push BOOLEAN,
  state_id INTEGER NOT NULL,
  rebase_jid VARCHAR(255),
  squash_commit_sha VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (target_project_id, iid)
);

CREATE TABLE merge_requests_closing_issues (
  id INTEGER NOT NULL,
  merge_request_id INTEGER NOT NULL,
  issue_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE merge_trains (
  id BIGINT NOT NULL,
  merge_request_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  pipeline_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  target_project_id INTEGER NOT NULL,
  target_branch VARCHAR(255) NOT NULL,
  status INTEGER NOT NULL,
  merged_at TIMESTAMP,
  duration INTEGER,
  PRIMARY KEY (id),
  UNIQUE (merge_request_id)
);

CREATE TABLE milestone_releases (
  milestone_id BIGINT NOT NULL,
  release_id BIGINT NOT NULL,
  UNIQUE (milestone_id, release_id)
);

CREATE TABLE milestones (
  id INTEGER NOT NULL,
  title VARCHAR(255) NOT NULL,
  project_id INTEGER,
  description VARCHAR(255),
  due_date DATE,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  state VARCHAR(255),
  iid INTEGER,
  title_html VARCHAR(255),
  description_html VARCHAR(255),
  start_date DATE,
  cached_markdown_version INTEGER,
  group_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (project_id, iid)
);

CREATE TABLE namespace_aggregation_schedules (
  namespace_id INTEGER NOT NULL,
  PRIMARY KEY (namespace_id),
  UNIQUE (namespace_id)
);

CREATE TABLE namespace_root_storage_statistics (
  namespace_id INTEGER NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  repository_size BIGINT NOT NULL,
  lfs_objects_size BIGINT NOT NULL,
  wiki_size BIGINT NOT NULL,
  build_artifacts_size BIGINT NOT NULL,
  storage_size BIGINT NOT NULL,
  packages_size BIGINT NOT NULL,
  PRIMARY KEY (namespace_id),
  UNIQUE (namespace_id)
);

CREATE TABLE namespace_statistics (
  id INTEGER NOT NULL,
  namespace_id INTEGER NOT NULL,
  shared_runners_seconds INTEGER NOT NULL,
  shared_runners_seconds_last_reset TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (namespace_id)
);

CREATE TABLE namespaces (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  path VARCHAR(255) NOT NULL,
  owner_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  "type" VARCHAR(255),
  description VARCHAR(255) NOT NULL,
  avatar VARCHAR(255),
  membership_lock BOOLEAN,
  share_with_group_lock BOOLEAN,
  visibility_level INTEGER NOT NULL,
  request_access_enabled BOOLEAN NOT NULL,
  ldap_sync_status VARCHAR(255) NOT NULL,
  ldap_sync_error VARCHAR(255),
  ldap_sync_last_update_at TIMESTAMP,
  ldap_sync_last_successful_update_at TIMESTAMP,
  ldap_sync_last_sync_at TIMESTAMP,
  description_html VARCHAR(255),
  lfs_enabled BOOLEAN,
  parent_id INTEGER,
  shared_runners_minutes_limit INTEGER,
  repository_size_limit BIGINT,
  require_two_factor_authentication BOOLEAN NOT NULL,
  two_factor_grace_period INTEGER NOT NULL,
  cached_markdown_version INTEGER,
  plan_id INTEGER,
  project_creation_level INTEGER,
  runners_token VARCHAR(255),
  trial_ends_on TIMESTAMP,
  file_template_project_id INTEGER,
  saml_discovery_token VARCHAR(255),
  runners_token_encrypted VARCHAR(255),
  custom_project_templates_group_id INTEGER,
  auto_devops_enabled BOOLEAN,
  extra_shared_runners_minutes_limit INTEGER,
  last_ci_minutes_notification_at TIMESTAMP,
  last_ci_minutes_usage_notification_level INTEGER,
  subgroup_creation_level INTEGER,
  emails_disabled BOOLEAN,
  max_pages_size INTEGER,
  max_artifacts_size INTEGER,
  mentions_disabled BOOLEAN,
  default_branch_protection INTEGER,
  unlock_membership_to_ldap BOOLEAN,
  max_personal_access_token_lifetime INTEGER,
  PRIMARY KEY (id),
  UNIQUE (name, parent_id),
  UNIQUE (parent_id, id),
  UNIQUE (runners_token),
  UNIQUE (runners_token_encrypted)
);

CREATE TABLE note_diff_files (
  id INTEGER NOT NULL,
  diff_note_id INTEGER NOT NULL,
  diff VARCHAR(255) NOT NULL,
  new_file BOOLEAN NOT NULL,
  renamed_file BOOLEAN NOT NULL,
  deleted_file BOOLEAN NOT NULL,
  a_mode VARCHAR(255) NOT NULL,
  b_mode VARCHAR(255) NOT NULL,
  new_path VARCHAR(255) NOT NULL,
  old_path VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (diff_note_id)
);

CREATE TABLE notes (
  id INTEGER NOT NULL,
  note VARCHAR(255),
  noteable_type VARCHAR(255),
  author_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  project_id INTEGER,
  attachment VARCHAR(255),
  line_code VARCHAR(255),
  commit_id VARCHAR(255),
  noteable_id INTEGER,
  "system" BOOLEAN NOT NULL,
  st_diff VARCHAR(255),
  updated_by_id INTEGER,
  "type" VARCHAR(255),
  "position" VARCHAR(255),
  original_position VARCHAR(255),
  resolved_at TIMESTAMP,
  resolved_by_id INTEGER,
  discussion_id VARCHAR(255),
  note_html VARCHAR(255),
  cached_markdown_version INTEGER,
  change_position VARCHAR(255),
  resolved_by_push BOOLEAN,
  review_id BIGINT,
  confidential BOOLEAN,
  PRIMARY KEY (id)
);

CREATE TABLE notification_settings (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  source_id INTEGER,
  source_type VARCHAR(255),
  level INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  new_note BOOLEAN,
  new_issue BOOLEAN,
  reopen_issue BOOLEAN,
  close_issue BOOLEAN,
  reassign_issue BOOLEAN,
  new_merge_request BOOLEAN,
  reopen_merge_request BOOLEAN,
  close_merge_request BOOLEAN,
  reassign_merge_request BOOLEAN,
  merge_merge_request BOOLEAN,
  failed_pipeline BOOLEAN,
  success_pipeline BOOLEAN,
  push_to_merge_request BOOLEAN,
  issue_due BOOLEAN,
  new_epic BOOLEAN,
  notification_email VARCHAR(255),
  fixed_pipeline BOOLEAN,
  new_release BOOLEAN,
  PRIMARY KEY (id),
  UNIQUE (user_id, source_id, source_type)
);

CREATE TABLE oauth_access_grants (
  id INTEGER NOT NULL,
  resource_owner_id INTEGER NOT NULL,
  application_id INTEGER NOT NULL,
  token VARCHAR(255) NOT NULL,
  expires_in INTEGER NOT NULL,
  redirect_uri VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  revoked_at TIMESTAMP,
  scopes VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (token)
);

CREATE TABLE oauth_access_tokens (
  id INTEGER NOT NULL,
  resource_owner_id INTEGER,
  application_id INTEGER,
  token VARCHAR(255) NOT NULL,
  refresh_token VARCHAR(255),
  expires_in INTEGER,
  revoked_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  scopes VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (refresh_token),
  UNIQUE (token)
);

CREATE TABLE oauth_applications (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  uid VARCHAR(255) NOT NULL,
  secret VARCHAR(255) NOT NULL,
  redirect_uri VARCHAR(255) NOT NULL,
  scopes VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  owner_id INTEGER,
  owner_type VARCHAR(255),
  trusted BOOLEAN NOT NULL,
  confidential BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (uid)
);

CREATE TABLE oauth_openid_requests (
  id INTEGER NOT NULL,
  access_grant_id INTEGER NOT NULL,
  nonce VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE open_project_tracker_data (
  id BIGINT NOT NULL,
  service_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  encrypted_url VARCHAR(255),
  encrypted_url_iv VARCHAR(255),
  encrypted_api_url VARCHAR(255),
  encrypted_api_url_iv VARCHAR(255),
  encrypted_token VARCHAR(255),
  encrypted_token_iv VARCHAR(255),
  closed_status_id VARCHAR(255),
  project_identifier_code VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE operations_feature_flag_scopes (
  id BIGINT NOT NULL,
  feature_flag_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  active BOOLEAN NOT NULL,
  environment_scope VARCHAR(255) NOT NULL,
  strategies VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (feature_flag_id, environment_scope)
);

CREATE TABLE operations_feature_flags (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  active BOOLEAN NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  name VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  iid INTEGER NOT NULL,
  version INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, iid),
  UNIQUE (project_id, name)
);

CREATE TABLE operations_feature_flags_clients (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  token_encrypted VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (project_id, token_encrypted)
);

CREATE TABLE operations_scopes (
  id BIGINT NOT NULL,
  strategy_id BIGINT NOT NULL,
  environment_scope VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (strategy_id, environment_scope)
);

CREATE TABLE operations_strategies (
  id BIGINT NOT NULL,
  feature_flag_id BIGINT NOT NULL,
  name VARCHAR(255) NOT NULL,
  parameters VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE packages_build_infos (
  id BIGINT NOT NULL,
  package_id INTEGER NOT NULL,
  pipeline_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (package_id)
);

CREATE TABLE packages_conan_file_metadata (
  id BIGINT NOT NULL,
  package_file_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  recipe_revision VARCHAR(255) NOT NULL,
  package_revision VARCHAR(255),
  conan_package_reference VARCHAR(255),
  conan_file_type INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (package_file_id)
);

CREATE TABLE packages_conan_metadata (
  id BIGINT NOT NULL,
  package_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  package_username VARCHAR(255) NOT NULL,
  package_channel VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (package_id, package_username, package_channel)
);

CREATE TABLE packages_dependencies (
  id BIGINT NOT NULL,
  name VARCHAR(255) NOT NULL,
  version_pattern VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (name, version_pattern)
);

CREATE TABLE packages_dependency_links (
  id BIGINT NOT NULL,
  package_id BIGINT NOT NULL,
  dependency_id BIGINT NOT NULL,
  dependency_type INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (package_id, dependency_id, dependency_type)
);

CREATE TABLE packages_maven_metadata (
  id BIGINT NOT NULL,
  package_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  app_group VARCHAR(255) NOT NULL,
  app_name VARCHAR(255) NOT NULL,
  app_version VARCHAR(255),
  path VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE packages_package_files (
  id BIGINT NOT NULL,
  package_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  size BIGINT,
  file_store INTEGER,
  file_md5 VARCHAR(255),
  file_sha1 VARCHAR(255),
  file_name VARCHAR(255) NOT NULL,
  file VARCHAR(255) NOT NULL,
  file_sha256 VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE packages_packages (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  name VARCHAR(255) NOT NULL,
  version VARCHAR(255),
  package_type INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE packages_tags (
  id BIGINT NOT NULL,
  package_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE pages_domain_acme_orders (
  id BIGINT NOT NULL,
  pages_domain_id INTEGER NOT NULL,
  expires_at TIMESTAMP NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  url VARCHAR(255) NOT NULL,
  challenge_token VARCHAR(255) NOT NULL,
  challenge_file_content VARCHAR(255) NOT NULL,
  encrypted_private_key VARCHAR(255) NOT NULL,
  encrypted_private_key_iv VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE pages_domains (
  id INTEGER NOT NULL,
  project_id INTEGER,
  certificate VARCHAR(255),
  encrypted_key VARCHAR(255),
  encrypted_key_iv VARCHAR(255),
  encrypted_key_salt VARCHAR(255),
  domain VARCHAR(255),
  verified_at TIMESTAMP,
  verification_code VARCHAR(255) NOT NULL,
  enabled_until TIMESTAMP,
  remove_at TIMESTAMP,
  auto_ssl_enabled BOOLEAN NOT NULL,
  certificate_valid_not_before TIMESTAMP,
  certificate_valid_not_after TIMESTAMP,
  certificate_source INTEGER NOT NULL,
  wildcard BOOLEAN NOT NULL,
  usage INTEGER NOT NULL,
  "scope" INTEGER NOT NULL,
  auto_ssl_failed BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (domain, wildcard)
);

CREATE TABLE path_locks (
  id INTEGER NOT NULL,
  path VARCHAR(255) NOT NULL,
  project_id INTEGER,
  user_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE personal_access_tokens (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  revoked BOOLEAN,
  expires_at DATE,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  scopes VARCHAR(255) NOT NULL,
  impersonation BOOLEAN NOT NULL,
  token_digest VARCHAR(255),
  expire_notification_delivered BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (token_digest)
);

CREATE TABLE plan_limits (
  id BIGINT NOT NULL,
  plan_id BIGINT NOT NULL,
  ci_active_pipelines INTEGER NOT NULL,
  ci_pipeline_size INTEGER NOT NULL,
  ci_active_jobs INTEGER NOT NULL,
  project_hooks INTEGER NOT NULL,
  group_hooks INTEGER NOT NULL,
  ci_project_subscriptions INTEGER NOT NULL,
  ci_pipeline_schedules INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (plan_id)
);

CREATE TABLE plans (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  name VARCHAR(255),
  title VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE pool_repositories (
  id BIGINT NOT NULL,
  shard_id INTEGER NOT NULL,
  disk_path VARCHAR(255),
  state VARCHAR(255),
  source_project_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (disk_path),
  UNIQUE (source_project_id, shard_id)
);

CREATE TABLE programming_languages (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  color VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE project_alerting_settings (
  project_id INTEGER NOT NULL,
  encrypted_token VARCHAR(255) NOT NULL,
  encrypted_token_iv VARCHAR(255) NOT NULL,
  PRIMARY KEY (project_id)
);

CREATE TABLE project_aliases (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE project_authorizations (
  user_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  access_level INTEGER NOT NULL,
  UNIQUE (user_id, project_id, access_level)
);

CREATE TABLE project_auto_devops (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  enabled BOOLEAN,
  deploy_strategy INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE project_ci_cd_settings (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  group_runners_enabled BOOLEAN NOT NULL,
  merge_pipelines_enabled BOOLEAN,
  default_git_depth INTEGER,
  forward_deployment_enabled BOOLEAN,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE project_custom_attributes (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id INTEGER NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, "key")
);

CREATE TABLE project_daily_statistics (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  fetch_count INTEGER NOT NULL,
  "date" DATE,
  PRIMARY KEY (id),
  UNIQUE (project_id, "date")
);

CREATE TABLE project_deploy_tokens (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  deploy_token_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, deploy_token_id)
);

CREATE TABLE project_error_tracking_settings (
  project_id INTEGER NOT NULL,
  enabled BOOLEAN NOT NULL,
  api_url VARCHAR(255),
  encrypted_token VARCHAR(255),
  encrypted_token_iv VARCHAR(255),
  project_name VARCHAR(255),
  organization_name VARCHAR(255),
  PRIMARY KEY (project_id)
);

CREATE TABLE project_export_jobs (
  id BIGINT NOT NULL,
  project_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  status INTEGER NOT NULL,
  jid VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (jid)
);

CREATE TABLE project_feature_usages (
  project_id INTEGER NOT NULL,
  jira_dvcs_cloud_last_sync_at TIMESTAMP,
  jira_dvcs_server_last_sync_at TIMESTAMP,
  PRIMARY KEY (project_id)
);

CREATE TABLE project_features (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  merge_requests_access_level INTEGER,
  issues_access_level INTEGER,
  wiki_access_level INTEGER,
  snippets_access_level INTEGER NOT NULL,
  builds_access_level INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  repository_access_level INTEGER NOT NULL,
  pages_access_level INTEGER NOT NULL,
  forking_access_level INTEGER,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE project_group_links (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  group_access INTEGER NOT NULL,
  expires_at DATE,
  PRIMARY KEY (id)
);

CREATE TABLE project_import_data (
  id INTEGER NOT NULL,
  project_id INTEGER,
  "data" VARCHAR(255),
  encrypted_credentials VARCHAR(255),
  encrypted_credentials_iv VARCHAR(255),
  encrypted_credentials_salt VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE project_incident_management_settings (
  project_id INTEGER NOT NULL,
  create_issue BOOLEAN NOT NULL,
  send_email BOOLEAN NOT NULL,
  issue_template_key VARCHAR(255),
  PRIMARY KEY (project_id)
);

CREATE TABLE project_metrics_settings (
  project_id INTEGER NOT NULL,
  external_dashboard_url VARCHAR(255) NOT NULL,
  PRIMARY KEY (project_id)
);

CREATE TABLE project_mirror_data (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  retry_count INTEGER NOT NULL,
  last_update_started_at TIMESTAMP,
  last_update_scheduled_at TIMESTAMP,
  next_execution_timestamp TIMESTAMP,
  status VARCHAR(255),
  jid VARCHAR(255),
  last_error VARCHAR(255),
  last_update_at TIMESTAMP,
  last_successful_update_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE project_pages_metadata (
  project_id BIGINT NOT NULL,
  deployed BOOLEAN NOT NULL,
  UNIQUE (project_id)
);

CREATE TABLE project_repositories (
  id BIGINT NOT NULL,
  shard_id INTEGER NOT NULL,
  disk_path VARCHAR(255) NOT NULL,
  project_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (disk_path),
  UNIQUE (project_id)
);

CREATE TABLE project_repository_states (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  repository_verification_checksum VARCHAR(255),
  wiki_verification_checksum VARCHAR(255),
  last_repository_verification_failure VARCHAR(255),
  last_wiki_verification_failure VARCHAR(255),
  repository_retry_at TIMESTAMP,
  wiki_retry_at TIMESTAMP,
  repository_retry_count INTEGER,
  wiki_retry_count INTEGER,
  last_repository_verification_ran_at TIMESTAMP,
  last_wiki_verification_ran_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE project_settings (
  project_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (project_id)
);

CREATE TABLE project_statistics (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  namespace_id INTEGER NOT NULL,
  commit_count BIGINT NOT NULL,
  storage_size BIGINT NOT NULL,
  repository_size BIGINT NOT NULL,
  lfs_objects_size BIGINT NOT NULL,
  build_artifacts_size BIGINT NOT NULL,
  shared_runners_seconds BIGINT NOT NULL,
  shared_runners_seconds_last_reset TIMESTAMP,
  packages_size BIGINT NOT NULL,
  wiki_size BIGINT,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE project_tracing_settings (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id INTEGER NOT NULL,
  external_url VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE projects (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  path VARCHAR(255),
  description VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  creator_id INTEGER,
  namespace_id INTEGER NOT NULL,
  last_activity_at TIMESTAMP,
  import_url VARCHAR(255),
  visibility_level INTEGER NOT NULL,
  archived BOOLEAN NOT NULL,
  avatar VARCHAR(255),
  merge_requests_template VARCHAR(255),
  star_count INTEGER NOT NULL,
  merge_requests_rebase_enabled BOOLEAN,
  import_type VARCHAR(255),
  import_source VARCHAR(255),
  approvals_before_merge INTEGER NOT NULL,
  reset_approvals_on_push BOOLEAN,
  merge_requests_ff_only_enabled BOOLEAN,
  issues_template VARCHAR(255),
  mirror BOOLEAN NOT NULL,
  mirror_last_update_at TIMESTAMP,
  mirror_last_successful_update_at TIMESTAMP,
  mirror_user_id INTEGER,
  shared_runners_enabled BOOLEAN NOT NULL,
  runners_token VARCHAR(255),
  build_coverage_regex VARCHAR(255),
  build_allow_git_fetch BOOLEAN NOT NULL,
  build_timeout INTEGER NOT NULL,
  mirror_trigger_builds BOOLEAN NOT NULL,
  pending_delete BOOLEAN,
  public_builds BOOLEAN NOT NULL,
  last_repository_check_failed BOOLEAN,
  last_repository_check_at TIMESTAMP,
  container_registry_enabled BOOLEAN,
  only_allow_merge_if_pipeline_succeeds BOOLEAN NOT NULL,
  has_external_issue_tracker BOOLEAN,
  repository_storage VARCHAR(255) NOT NULL,
  repository_read_only BOOLEAN,
  request_access_enabled BOOLEAN NOT NULL,
  has_external_wiki BOOLEAN,
  ci_config_path VARCHAR(255),
  lfs_enabled BOOLEAN,
  description_html VARCHAR(255),
  only_allow_merge_if_all_discussions_are_resolved BOOLEAN,
  repository_size_limit BIGINT,
  printing_merge_request_link_enabled BOOLEAN NOT NULL,
  auto_cancel_pending_pipelines INTEGER NOT NULL,
  service_desk_enabled BOOLEAN,
  cached_markdown_version INTEGER,
  delete_error VARCHAR(255),
  last_repository_updated_at TIMESTAMP,
  disable_overriding_approvers_per_merge_request BOOLEAN,
  storage_version INTEGER,
  resolve_outdated_diff_discussions BOOLEAN,
  remote_mirror_available_overridden BOOLEAN,
  only_mirror_protected_branches BOOLEAN,
  pull_mirror_available_overridden BOOLEAN,
  jobs_cache_index INTEGER,
  external_authorization_classification_label VARCHAR(255),
  mirror_overwrites_diverged_branches BOOLEAN,
  pages_https_only BOOLEAN,
  external_webhook_token VARCHAR(255),
  packages_enabled BOOLEAN,
  merge_requests_author_approval BOOLEAN,
  pool_repository_id BIGINT,
  runners_token_encrypted VARCHAR(255),
  bfg_object_map VARCHAR(255),
  detected_repository_languages BOOLEAN,
  merge_requests_disable_committers_approval BOOLEAN,
  require_password_to_approve BOOLEAN,
  emails_disabled BOOLEAN,
  max_pages_size INTEGER,
  max_artifacts_size INTEGER,
  pull_mirror_branch_prefix VARCHAR(255),
  remove_source_branch_after_merge BOOLEAN,
  marked_for_deletion_at DATE,
  marked_for_deletion_by_user_id INTEGER,
  autoclose_referenced_issues BOOLEAN,
  suggestion_commit_message VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE prometheus_alert_events (
  id BIGINT NOT NULL,
  project_id INTEGER NOT NULL,
  prometheus_alert_id INTEGER NOT NULL,
  started_at TIMESTAMP NOT NULL,
  ended_at TIMESTAMP,
  status INTEGER,
  payload_key VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (prometheus_alert_id, payload_key)
);

CREATE TABLE prometheus_alerts (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  threshold FLOAT NOT NULL,
  operator INTEGER NOT NULL,
  environment_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  prometheus_metric_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, prometheus_metric_id, environment_id)
);

CREATE TABLE prometheus_metrics (
  id INTEGER NOT NULL,
  project_id INTEGER,
  title VARCHAR(255) NOT NULL,
  query VARCHAR(255) NOT NULL,
  y_label VARCHAR(255) NOT NULL,
  unit VARCHAR(255) NOT NULL,
  legend VARCHAR(255),
  congruentClass INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  common BOOLEAN NOT NULL,
  identifier VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (identifier)
);

CREATE TABLE protected_branch_merge_access_levels (
  id INTEGER NOT NULL,
  protected_branch_id INTEGER NOT NULL,
  access_level INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id INTEGER,
  group_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE protected_branch_push_access_levels (
  id INTEGER NOT NULL,
  protected_branch_id INTEGER NOT NULL,
  access_level INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id INTEGER,
  group_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE protected_branch_unprotect_access_levels (
  id INTEGER NOT NULL,
  protected_branch_id INTEGER NOT NULL,
  access_level INTEGER,
  user_id INTEGER,
  group_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE protected_branches (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  code_owner_approval_required BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE protected_environment_deploy_access_levels (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  access_level INTEGER,
  protected_environment_id INTEGER NOT NULL,
  user_id INTEGER,
  group_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE protected_environments (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, name)
);

CREATE TABLE protected_tag_create_access_levels (
  id INTEGER NOT NULL,
  protected_tag_id INTEGER NOT NULL,
  access_level INTEGER,
  user_id INTEGER,
  group_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE protected_tags (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, name)
);

CREATE TABLE push_event_payloads (
  commit_count BIGINT NOT NULL,
  event_id INTEGER NOT NULL,
  action INTEGER NOT NULL,
  ref_type INTEGER NOT NULL,
  commit_from VARCHAR(255),
  commit_to VARCHAR(255),
  "ref" VARCHAR(255),
  commit_title VARCHAR(255),
  ref_count INTEGER,
  UNIQUE (event_id)
);

CREATE TABLE push_rules (
  id INTEGER NOT NULL,
  force_push_regex VARCHAR(255),
  delete_branch_regex VARCHAR(255),
  commit_message_regex VARCHAR(255),
  deny_delete_tag BOOLEAN,
  project_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  author_email_regex VARCHAR(255),
  member_check BOOLEAN NOT NULL,
  file_name_regex VARCHAR(255),
  is_sample BOOLEAN,
  max_file_size INTEGER NOT NULL,
  prevent_secrets BOOLEAN NOT NULL,
  branch_name_regex VARCHAR(255),
  reject_unsigned_commits BOOLEAN,
  commit_committer_check BOOLEAN,
  regexp_uses_re2 BOOLEAN,
  commit_message_negative_regex VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE redirect_routes (
  id INTEGER NOT NULL,
  source_id INTEGER NOT NULL,
  source_type VARCHAR(255) NOT NULL,
  path VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (path)
);

CREATE TABLE release_links (
  id BIGINT NOT NULL,
  release_id INTEGER NOT NULL,
  url VARCHAR(255) NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  filepath VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (release_id, name),
  UNIQUE (release_id, url)
);

CREATE TABLE releases (
  id INTEGER NOT NULL,
  tag VARCHAR(255),
  description VARCHAR(255),
  project_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  description_html VARCHAR(255),
  cached_markdown_version INTEGER,
  author_id INTEGER,
  name VARCHAR(255),
  sha VARCHAR(255),
  released_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE remote_mirrors (
  id INTEGER NOT NULL,
  project_id INTEGER,
  url VARCHAR(255),
  enabled BOOLEAN,
  update_status VARCHAR(255),
  last_update_at TIMESTAMP,
  last_successful_update_at TIMESTAMP,
  last_error VARCHAR(255),
  encrypted_credentials VARCHAR(255),
  encrypted_credentials_iv VARCHAR(255),
  encrypted_credentials_salt VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  last_update_started_at TIMESTAMP,
  only_protected_branches BOOLEAN NOT NULL,
  remote_name VARCHAR(255),
  error_notification_sent BOOLEAN,
  keep_divergent_refs BOOLEAN,
  PRIMARY KEY (id)
);

CREATE TABLE repository_languages (
  project_id INTEGER NOT NULL,
  programming_language_id INTEGER NOT NULL,
  share FLOAT NOT NULL,
  UNIQUE (project_id, programming_language_id)
);

CREATE TABLE requirements (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id INTEGER NOT NULL,
  author_id INTEGER,
  iid INTEGER NOT NULL,
  cached_markdown_version INTEGER,
  state INTEGER NOT NULL,
  title VARCHAR(255) NOT NULL,
  title_html VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE resource_label_events (
  id BIGINT NOT NULL,
  action INTEGER NOT NULL,
  issue_id INTEGER,
  merge_request_id INTEGER,
  epic_id INTEGER,
  label_id INTEGER,
  user_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  cached_markdown_version INTEGER,
  reference VARCHAR(255),
  reference_html VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE resource_milestone_events (
  id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  issue_id BIGINT,
  merge_request_id BIGINT,
  milestone_id BIGINT,
  action INTEGER NOT NULL,
  state INTEGER NOT NULL,
  cached_markdown_version INTEGER,
  reference VARCHAR(255),
  reference_html VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE resource_weight_events (
  id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  issue_id BIGINT NOT NULL,
  weight INTEGER,
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE reviews (
  id BIGINT NOT NULL,
  author_id INTEGER,
  merge_request_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE routes (
  id INTEGER NOT NULL,
  source_id INTEGER NOT NULL,
  source_type VARCHAR(255) NOT NULL,
  path VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  name VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (path),
  UNIQUE (source_type, source_id)
);

CREATE TABLE saml_providers (
  id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  enabled BOOLEAN NOT NULL,
  certificate_fingerprint VARCHAR(255) NOT NULL,
  sso_url VARCHAR(255) NOT NULL,
  enforced_sso BOOLEAN NOT NULL,
  enforced_group_managed_accounts BOOLEAN NOT NULL,
  prohibited_outer_forks BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE schema_migrations (
  version VARCHAR(255) NOT NULL,
  PRIMARY KEY (version)
);

CREATE TABLE scim_identities (
  id BIGINT NOT NULL,
  group_id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  active BOOLEAN,
  extern_uid VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, group_id)
);

CREATE TABLE scim_oauth_access_tokens (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  group_id INTEGER NOT NULL,
  token_encrypted VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, token_encrypted)
);

CREATE TABLE security_scans (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  build_id BIGINT NOT NULL,
  scan_type INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (build_id, scan_type)
);

CREATE TABLE self_managed_prometheus_alert_events (
  id BIGINT NOT NULL,
  project_id BIGINT NOT NULL,
  environment_id BIGINT,
  started_at TIMESTAMP NOT NULL,
  ended_at TIMESTAMP,
  status INTEGER NOT NULL,
  title VARCHAR(255) NOT NULL,
  query_expression VARCHAR(255),
  payload_key VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, payload_key)
);

CREATE TABLE sent_notifications (
  id INTEGER NOT NULL,
  project_id INTEGER,
  noteable_id INTEGER,
  noteable_type VARCHAR(255),
  recipient_id INTEGER,
  commit_id VARCHAR(255),
  reply_key VARCHAR(255) NOT NULL,
  line_code VARCHAR(255),
  note_type VARCHAR(255),
  "position" VARCHAR(255),
  in_reply_to_discussion_id VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (reply_key)
);

CREATE TABLE sentry_issues (
  id BIGINT NOT NULL,
  issue_id BIGINT NOT NULL,
  sentry_issue_identifier BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (issue_id)
);

CREATE TABLE serverless_domain_cluster (
  uuid VARCHAR(255) NOT NULL,
  pages_domain_id BIGINT NOT NULL,
  clusters_applications_knative_id BIGINT NOT NULL,
  creator_id BIGINT,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  encrypted_key VARCHAR(255),
  encrypted_key_iv VARCHAR(255),
  certificate VARCHAR(255),
  PRIMARY KEY (uuid),
  UNIQUE (clusters_applications_knative_id)
);

CREATE TABLE service_desk_settings (
  project_id BIGINT NOT NULL,
  issue_template_key VARCHAR(255),
  outgoing_name VARCHAR(255),
  project_key VARCHAR(255),
  PRIMARY KEY (project_id)
);

CREATE TABLE services (
  id INTEGER NOT NULL,
  "type" VARCHAR(255),
  title VARCHAR(255),
  project_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  active BOOLEAN NOT NULL,
  properties VARCHAR(255),
  push_events BOOLEAN,
  issues_events BOOLEAN,
  merge_requests_events BOOLEAN,
  tag_push_events BOOLEAN,
  note_events BOOLEAN NOT NULL,
  category VARCHAR(255) NOT NULL,
  "default" BOOLEAN,
  wiki_page_events BOOLEAN,
  pipeline_events BOOLEAN NOT NULL,
  confidential_issues_events BOOLEAN NOT NULL,
  commit_events BOOLEAN NOT NULL,
  job_events BOOLEAN NOT NULL,
  confidential_note_events BOOLEAN,
  deployment_events BOOLEAN NOT NULL,
  description VARCHAR(255),
  comment_on_event_enabled BOOLEAN NOT NULL,
  template BOOLEAN,
  instance BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE shards (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE slack_integrations (
  id INTEGER NOT NULL,
  service_id INTEGER NOT NULL,
  team_id VARCHAR(255) NOT NULL,
  team_name VARCHAR(255) NOT NULL,
  alias VARCHAR(255) NOT NULL,
  user_id VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (team_id, alias)
);

CREATE TABLE smartcard_identities (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  subject VARCHAR(255) NOT NULL,
  issuer VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (subject, issuer)
);

CREATE TABLE snippet_repositories (
  snippet_id BIGINT NOT NULL,
  shard_id BIGINT NOT NULL,
  disk_path VARCHAR(255) NOT NULL,
  PRIMARY KEY (snippet_id),
  UNIQUE (disk_path)
);

CREATE TABLE snippet_user_mentions (
  id BIGINT NOT NULL,
  snippet_id INTEGER NOT NULL,
  note_id INTEGER,
  mentioned_users_ids INTEGER,
  mentioned_projects_ids INTEGER,
  mentioned_groups_ids INTEGER,
  PRIMARY KEY (id),
  UNIQUE (snippet_id, note_id)
);

CREATE TABLE snippets (
  id INTEGER NOT NULL,
  title VARCHAR(255),
  content VARCHAR(255),
  author_id INTEGER NOT NULL,
  project_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  file_name VARCHAR(255),
  "type" VARCHAR(255),
  visibility_level INTEGER NOT NULL,
  title_html VARCHAR(255),
  content_html VARCHAR(255),
  cached_markdown_version INTEGER,
  description VARCHAR(255),
  description_html VARCHAR(255),
  encrypted_secret_token VARCHAR(255),
  encrypted_secret_token_iv VARCHAR(255),
  secret BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE software_license_policies (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  software_license_id INTEGER NOT NULL,
  classification INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, software_license_id)
);

CREATE TABLE software_licenses (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  spdx_identifier VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE spam_logs (
  id INTEGER NOT NULL,
  user_id INTEGER,
  source_ip VARCHAR(255),
  user_agent VARCHAR(255),
  via_api BOOLEAN,
  noteable_type VARCHAR(255),
  title VARCHAR(255),
  description VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  submitted_as_ham BOOLEAN NOT NULL,
  recaptcha_verified BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE status_page_settings (
  project_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  enabled BOOLEAN NOT NULL,
  aws_s3_bucket_name VARCHAR(255) NOT NULL,
  aws_region VARCHAR(255) NOT NULL,
  aws_access_key VARCHAR(255) NOT NULL,
  encrypted_aws_secret_key VARCHAR(255) NOT NULL,
  encrypted_aws_secret_key_iv VARCHAR(255) NOT NULL,
  PRIMARY KEY (project_id)
);

CREATE TABLE subscriptions (
  id INTEGER NOT NULL,
  user_id INTEGER,
  subscribable_id INTEGER,
  subscribable_type VARCHAR(255),
  subscribed BOOLEAN,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  project_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (subscribable_id, subscribable_type, user_id, project_id)
);

CREATE TABLE suggestions (
  id BIGINT NOT NULL,
  note_id INTEGER NOT NULL,
  relative_order INTEGER NOT NULL,
  applied BOOLEAN NOT NULL,
  commit_id VARCHAR(255),
  from_content VARCHAR(255) NOT NULL,
  to_content VARCHAR(255) NOT NULL,
  lines_above INTEGER NOT NULL,
  lines_below INTEGER NOT NULL,
  outdated BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (note_id, relative_order)
);

CREATE TABLE system_note_metadata (
  id INTEGER NOT NULL,
  note_id INTEGER NOT NULL,
  commit_count INTEGER,
  action VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  description_version_id BIGINT,
  PRIMARY KEY (id),
  UNIQUE (note_id)
);

CREATE TABLE taggings (
  id INTEGER NOT NULL,
  tag_id INTEGER,
  taggable_id INTEGER,
  taggable_type VARCHAR(255),
  tagger_id INTEGER,
  tagger_type VARCHAR(255),
  context VARCHAR(255),
  created_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (tag_id, taggable_id, taggable_type, context, tagger_id, tagger_type)
);

CREATE TABLE tags (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  taggings_count INTEGER,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE term_agreements (
  id INTEGER NOT NULL,
  term_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  accepted BOOLEAN NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, term_id)
);

CREATE TABLE timelogs (
  id INTEGER NOT NULL,
  time_spent INTEGER NOT NULL,
  user_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  issue_id INTEGER,
  merge_request_id INTEGER,
  spent_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE todos (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  project_id INTEGER,
  target_id INTEGER,
  target_type VARCHAR(255) NOT NULL,
  author_id INTEGER NOT NULL,
  action INTEGER NOT NULL,
  state VARCHAR(255) NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  note_id INTEGER,
  commit_id VARCHAR(255),
  group_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE trending_projects (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id)
);

CREATE TABLE u2f_registrations (
  id INTEGER NOT NULL,
  certificate VARCHAR(255),
  key_handle VARCHAR(255),
  public_key VARCHAR(255),
  counter INTEGER,
  user_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  name VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE uploads (
  id INTEGER NOT NULL,
  size BIGINT NOT NULL,
  path VARCHAR(255) NOT NULL,
  checksum VARCHAR(255),
  model_id INTEGER,
  model_type VARCHAR(255),
  uploader VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  store INTEGER,
  mount_point VARCHAR(255),
  secret VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE user_agent_details (
  id INTEGER NOT NULL,
  user_agent VARCHAR(255) NOT NULL,
  ip_address VARCHAR(255) NOT NULL,
  subject_id INTEGER NOT NULL,
  subject_type VARCHAR(255) NOT NULL,
  submitted BOOLEAN NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE user_callouts (
  id INTEGER NOT NULL,
  feature_name INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  dismissed_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (user_id, feature_name)
);

CREATE TABLE user_canonical_emails (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id BIGINT NOT NULL,
  canonical_email VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id),
  UNIQUE (user_id, canonical_email)
);

CREATE TABLE user_custom_attributes (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id INTEGER NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, "key")
);

CREATE TABLE user_details (
  user_id BIGINT NOT NULL,
  job_title VARCHAR(255) NOT NULL,
  PRIMARY KEY (user_id),
  UNIQUE (user_id)
);

CREATE TABLE user_highest_roles (
  user_id BIGINT NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  highest_access_level INTEGER,
  PRIMARY KEY (user_id)
);

CREATE TABLE user_interacted_projects (
  user_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  UNIQUE (project_id, user_id)
);

CREATE TABLE user_preferences (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  issue_notes_filter INTEGER NOT NULL,
  merge_request_notes_filter INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  epics_sort VARCHAR(255),
  roadmap_epics_state INTEGER,
  epic_notes_filter INTEGER NOT NULL,
  issues_sort VARCHAR(255),
  merge_requests_sort VARCHAR(255),
  roadmaps_sort VARCHAR(255),
  first_day_of_week INTEGER,
  timezone VARCHAR(255),
  time_display_relative BOOLEAN,
  time_format_in_24h BOOLEAN,
  projects_sort VARCHAR(255),
  show_whitespace_in_diffs BOOLEAN NOT NULL,
  sourcegraph_enabled BOOLEAN,
  setup_for_company BOOLEAN,
  render_whitespace_in_code BOOLEAN,
  tab_width INTEGER,
  feature_filter_type BIGINT,
  PRIMARY KEY (id),
  UNIQUE (user_id)
);

CREATE TABLE user_statuses (
  user_id INTEGER NOT NULL,
  cached_markdown_version INTEGER,
  emoji VARCHAR(255) NOT NULL,
  message VARCHAR(255),
  message_html VARCHAR(255),
  PRIMARY KEY (user_id)
);

CREATE TABLE user_synced_attributes_metadata (
  id INTEGER NOT NULL,
  name_synced BOOLEAN,
  email_synced BOOLEAN,
  location_synced BOOLEAN,
  user_id INTEGER NOT NULL,
  provider VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (user_id)
);

CREATE TABLE users (
  id INTEGER NOT NULL,
  email VARCHAR(255) NOT NULL,
  encrypted_password VARCHAR(255) NOT NULL,
  reset_password_token VARCHAR(255),
  reset_password_sent_at TIMESTAMP,
  remember_created_at TIMESTAMP,
  sign_in_count INTEGER,
  current_sign_in_at TIMESTAMP,
  last_sign_in_at TIMESTAMP,
  current_sign_in_ip VARCHAR(255),
  last_sign_in_ip VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  name VARCHAR(255),
  admin BOOLEAN NOT NULL,
  projects_limit INTEGER NOT NULL,
  skype VARCHAR(255) NOT NULL,
  linkedin VARCHAR(255) NOT NULL,
  twitter VARCHAR(255) NOT NULL,
  bio VARCHAR(255),
  failed_attempts INTEGER,
  locked_at TIMESTAMP,
  username VARCHAR(255),
  can_create_group BOOLEAN NOT NULL,
  can_create_team BOOLEAN NOT NULL,
  state VARCHAR(255),
  color_scheme_id INTEGER NOT NULL,
  password_expires_at TIMESTAMP,
  created_by_id INTEGER,
  last_credential_check_at TIMESTAMP,
  avatar VARCHAR(255),
  confirmation_token VARCHAR(255),
  confirmed_at TIMESTAMP,
  confirmation_sent_at TIMESTAMP,
  unconfirmed_email VARCHAR(255),
  hide_no_ssh_key BOOLEAN,
  website_url VARCHAR(255) NOT NULL,
  admin_email_unsubscribed_at TIMESTAMP,
  notification_email VARCHAR(255),
  hide_no_password BOOLEAN,
  password_automatically_set BOOLEAN,
  location VARCHAR(255),
  encrypted_otp_secret VARCHAR(255),
  encrypted_otp_secret_iv VARCHAR(255),
  encrypted_otp_secret_salt VARCHAR(255),
  otp_required_for_login BOOLEAN NOT NULL,
  otp_backup_codes VARCHAR(255),
  public_email VARCHAR(255) NOT NULL,
  dashboard INTEGER,
  project_view INTEGER,
  consumed_timestep INTEGER,
  layout INTEGER,
  hide_project_limit BOOLEAN,
  note VARCHAR(255),
  unlock_token VARCHAR(255),
  otp_grace_period_started_at TIMESTAMP,
  "external" BOOLEAN,
  incoming_email_token VARCHAR(255),
  organization VARCHAR(255),
  auditor BOOLEAN NOT NULL,
  require_two_factor_authentication_from_group BOOLEAN NOT NULL,
  two_factor_grace_period INTEGER NOT NULL,
  ghost BOOLEAN,
  last_activity_on DATE,
  notified_of_own_activity BOOLEAN,
  preferred_language VARCHAR(255),
  email_opted_in BOOLEAN,
  email_opted_in_ip VARCHAR(255),
  email_opted_in_source_id INTEGER,
  email_opted_in_at TIMESTAMP,
  theme_id INTEGER,
  accepted_term_id INTEGER,
  feed_token VARCHAR(255),
  private_profile BOOLEAN NOT NULL,
  roadmap_layout INTEGER,
  include_private_contributions BOOLEAN,
  commit_email VARCHAR(255),
  group_view INTEGER,
  managing_group_id INTEGER,
  bot_type INTEGER,
  first_name VARCHAR(255),
  last_name VARCHAR(255),
  static_object_token VARCHAR(255),
  role INTEGER,
  user_type INTEGER,
  PRIMARY KEY (id),
  UNIQUE (confirmation_token),
  UNIQUE (email),
  UNIQUE (reset_password_token),
  UNIQUE (static_object_token),
  UNIQUE (unlock_token)
);

CREATE TABLE users_ops_dashboard_projects (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, project_id)
);

CREATE TABLE users_security_dashboard_projects (
  user_id BIGINT NOT NULL,
  project_id BIGINT NOT NULL,
  UNIQUE (project_id, user_id)
);

CREATE TABLE users_star_projects (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (user_id, project_id)
);

CREATE TABLE users_statistics (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  without_groups_and_projects INTEGER NOT NULL,
  with_highest_role_guest INTEGER NOT NULL,
  with_highest_role_reporter INTEGER NOT NULL,
  with_highest_role_developer INTEGER NOT NULL,
  with_highest_role_maintainer INTEGER NOT NULL,
  with_highest_role_owner INTEGER NOT NULL,
  bots INTEGER NOT NULL,
  blocked INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE vulnerabilities (
  id BIGINT NOT NULL,
  milestone_id BIGINT,
  epic_id BIGINT,
  project_id BIGINT NOT NULL,
  author_id BIGINT NOT NULL,
  updated_by_id BIGINT,
  last_edited_by_id BIGINT,
  start_date DATE,
  due_date DATE,
  last_edited_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  title VARCHAR(255) NOT NULL,
  title_html VARCHAR(255),
  description VARCHAR(255),
  description_html VARCHAR(255),
  start_date_sourcing_milestone_id BIGINT,
  due_date_sourcing_milestone_id BIGINT,
  state INTEGER NOT NULL,
  severity INTEGER NOT NULL,
  severity_overridden BOOLEAN,
  confidence INTEGER NOT NULL,
  confidence_overridden BOOLEAN,
  resolved_by_id BIGINT,
  resolved_at TIMESTAMP,
  report_type INTEGER NOT NULL,
  cached_markdown_version INTEGER,
  confirmed_by_id BIGINT,
  confirmed_at TIMESTAMP,
  dismissed_at TIMESTAMP,
  dismissed_by_id BIGINT,
  PRIMARY KEY (id)
);

CREATE TABLE vulnerability_exports (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  started_at TIMESTAMP,
  finished_at TIMESTAMP,
  status VARCHAR(255) NOT NULL,
  file VARCHAR(255),
  project_id BIGINT NOT NULL,
  author_id BIGINT NOT NULL,
  file_store INTEGER,
  format INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, id)
);

CREATE TABLE vulnerability_feedback (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  feedback_type INTEGER NOT NULL,
  category INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  pipeline_id INTEGER,
  issue_id INTEGER,
  project_fingerprint VARCHAR(255) NOT NULL,
  merge_request_id INTEGER,
  comment_author_id INTEGER,
  comment VARCHAR(255),
  comment_timestamp TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (project_id, category, feedback_type, project_fingerprint)
);

CREATE TABLE vulnerability_identifiers (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id INTEGER NOT NULL,
  fingerprint VARCHAR(255) NOT NULL,
  external_type VARCHAR(255) NOT NULL,
  external_id VARCHAR(255) NOT NULL,
  name VARCHAR(255) NOT NULL,
  url VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (project_id, fingerprint)
);

CREATE TABLE vulnerability_issue_links (
  id BIGINT NOT NULL,
  vulnerability_id BIGINT NOT NULL,
  issue_id BIGINT NOT NULL,
  link_type INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (vulnerability_id, issue_id)
);

CREATE TABLE vulnerability_occurrence_identifiers (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  occurrence_id BIGINT NOT NULL,
  identifier_id BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (occurrence_id, identifier_id)
);

CREATE TABLE vulnerability_occurrence_pipelines (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  occurrence_id BIGINT NOT NULL,
  pipeline_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (occurrence_id, pipeline_id)
);

CREATE TABLE vulnerability_occurrences (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  severity INTEGER NOT NULL,
  confidence INTEGER NOT NULL,
  report_type INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  scanner_id BIGINT NOT NULL,
  primary_identifier_id BIGINT NOT NULL,
  project_fingerprint VARCHAR(255) NOT NULL,
  location_fingerprint VARCHAR(255) NOT NULL,
  uuid VARCHAR(255) NOT NULL,
  name VARCHAR(255) NOT NULL,
  metadata_version VARCHAR(255) NOT NULL,
  raw_metadata VARCHAR(255) NOT NULL,
  vulnerability_id BIGINT,
  PRIMARY KEY (id),
  UNIQUE (project_id, primary_identifier_id, location_fingerprint, scanner_id),
  UNIQUE (uuid)
);

CREATE TABLE vulnerability_scanners (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id INTEGER NOT NULL,
  external_id VARCHAR(255) NOT NULL,
  name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (project_id, external_id)
);

CREATE TABLE vulnerability_user_mentions (
  id BIGINT NOT NULL,
  vulnerability_id BIGINT NOT NULL,
  note_id INTEGER,
  mentioned_users_ids INTEGER,
  mentioned_projects_ids INTEGER,
  mentioned_groups_ids INTEGER,
  PRIMARY KEY (id),
  UNIQUE (vulnerability_id, note_id)
);

CREATE TABLE web_hook_logs (
  id INTEGER NOT NULL,
  web_hook_id INTEGER NOT NULL,
  "trigger" VARCHAR(255),
  url VARCHAR(255),
  request_headers VARCHAR(255),
  request_data VARCHAR(255),
  response_headers VARCHAR(255),
  response_body VARCHAR(255),
  response_status VARCHAR(255),
  execution_duration FLOAT,
  internal_error_message VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE web_hooks (
  id INTEGER NOT NULL,
  project_id INTEGER,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  "type" VARCHAR(255),
  service_id INTEGER,
  push_events BOOLEAN NOT NULL,
  issues_events BOOLEAN NOT NULL,
  merge_requests_events BOOLEAN NOT NULL,
  tag_push_events BOOLEAN,
  group_id INTEGER,
  note_events BOOLEAN NOT NULL,
  enable_ssl_verification BOOLEAN,
  wiki_page_events BOOLEAN NOT NULL,
  pipeline_events BOOLEAN NOT NULL,
  confidential_issues_events BOOLEAN NOT NULL,
  repository_update_events BOOLEAN NOT NULL,
  job_events BOOLEAN NOT NULL,
  confidential_note_events BOOLEAN,
  push_events_branch_filter VARCHAR(255),
  encrypted_token VARCHAR(255),
  encrypted_token_iv VARCHAR(255),
  encrypted_url VARCHAR(255),
  encrypted_url_iv VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE wiki_page_meta (
  id INTEGER NOT NULL,
  project_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  title VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE wiki_page_slugs (
  id INTEGER NOT NULL,
  canonical BOOLEAN NOT NULL,
  wiki_page_meta_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  slug VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (slug, wiki_page_meta_id)
);

CREATE TABLE x509_certificates (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  subject_key_identifier VARCHAR(255) NOT NULL,
  subject VARCHAR(255) NOT NULL,
  email VARCHAR(255) NOT NULL,
  serial_number VARCHAR(255) NOT NULL,
  certificate_status INTEGER NOT NULL,
  x509_issuer_id BIGINT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE x509_commit_signatures (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  project_id BIGINT NOT NULL,
  x509_certificate_id BIGINT NOT NULL,
  commit_sha VARCHAR(255) NOT NULL,
  verification_status INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE x509_issuers (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  subject_key_identifier VARCHAR(255) NOT NULL,
  subject VARCHAR(255) NOT NULL,
  crl_url VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE zoom_meetings (
  id BIGINT NOT NULL,
  project_id BIGINT NOT NULL,
  issue_id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  issue_status INTEGER NOT NULL,
  url VARCHAR(255),
  PRIMARY KEY (id)
);
