CREATE TABLE anonymous_users (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  master_user_id INTEGER NOT NULL,
  active BOOLEAN NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id)
);

CREATE TABLE api_keys (
  id INTEGER NOT NULL,
  user_id INTEGER,
  created_by_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  allowed_ips VARCHAR(255),
  hidden BOOLEAN NOT NULL,
  last_used_at TIMESTAMP,
  revoked_at TIMESTAMP,
  description VARCHAR(255),
  key_hash VARCHAR(255) NOT NULL,
  truncated_key VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE application_requests (
  id INTEGER NOT NULL,
  "date" DATE NOT NULL,
  req_type INTEGER NOT NULL,
  "count" INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE ("date", req_type)
);

CREATE TABLE ar_internal_metadata (
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY ("key")
);

CREATE TABLE backup_draft_posts (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  post_id INTEGER NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (post_id),
  UNIQUE (user_id, "key")
);

CREATE TABLE backup_draft_topics (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (topic_id),
  UNIQUE (user_id)
);

CREATE TABLE backup_metadata (
  id BIGINT NOT NULL,
  name VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE badge_groupings (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  "position" INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE categories (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  color VARCHAR(255) NOT NULL,
  topic_id INTEGER,
  topic_count INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id INTEGER NOT NULL,
  topics_year INTEGER,
  topics_month INTEGER,
  topics_week INTEGER,
  slug VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  text_color VARCHAR(255) NOT NULL,
  read_restricted BOOLEAN NOT NULL,
  auto_close_hours FLOAT,
  post_count INTEGER NOT NULL,
  latest_post_id INTEGER,
  latest_topic_id INTEGER,
  "position" INTEGER,
  parent_category_id INTEGER,
  posts_year INTEGER,
  posts_month INTEGER,
  posts_week INTEGER,
  email_in VARCHAR(255),
  email_in_allow_strangers BOOLEAN,
  topics_day INTEGER,
  posts_day INTEGER,
  allow_badges BOOLEAN NOT NULL,
  name_lower VARCHAR(255) NOT NULL,
  auto_close_based_on_last_post BOOLEAN,
  topic_template VARCHAR(255),
  contains_messages BOOLEAN,
  sort_order VARCHAR(255),
  sort_ascending BOOLEAN,
  uploaded_logo_id INTEGER,
  uploaded_background_id INTEGER,
  topic_featured_link_allowed BOOLEAN,
  all_topics_wiki BOOLEAN NOT NULL,
  show_subcategory_list BOOLEAN,
  num_featured_topics INTEGER,
  default_view VARCHAR(255),
  subcategory_list_style VARCHAR(255),
  default_top_period VARCHAR(255),
  mailinglist_mirror BOOLEAN NOT NULL,
  minimum_required_tags INTEGER NOT NULL,
  navigate_to_first_post_after_read BOOLEAN NOT NULL,
  search_priority INTEGER,
  allow_global_tags BOOLEAN NOT NULL,
  reviewable_by_group_id INTEGER,
  required_tag_group_id INTEGER,
  min_tags_from_required_group INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (email_in)
);

CREATE TABLE posts (
  id INTEGER NOT NULL,
  user_id INTEGER,
  topic_id INTEGER NOT NULL,
  post_number INTEGER NOT NULL,
  raw VARCHAR(255) NOT NULL,
  cooked VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  reply_to_post_number INTEGER,
  reply_count INTEGER NOT NULL,
  quote_count INTEGER NOT NULL,
  deleted_at TIMESTAMP,
  off_topic_count INTEGER NOT NULL,
  like_count INTEGER NOT NULL,
  incoming_link_count INTEGER NOT NULL,
  bookmark_count INTEGER NOT NULL,
  avg_time INTEGER,
  score FLOAT,
  "reads" INTEGER NOT NULL,
  post_type INTEGER NOT NULL,
  sort_order INTEGER,
  last_editor_id INTEGER,
  hidden BOOLEAN NOT NULL,
  hidden_reason_id INTEGER,
  notify_moderators_count INTEGER NOT NULL,
  spam_count INTEGER NOT NULL,
  illegal_count INTEGER NOT NULL,
  inappropriate_count INTEGER NOT NULL,
  last_version_at TIMESTAMP NOT NULL,
  user_deleted BOOLEAN NOT NULL,
  reply_to_user_id INTEGER,
  "percent_rank" FLOAT,
  notify_user_count INTEGER NOT NULL,
  like_score INTEGER NOT NULL,
  deleted_by_id INTEGER,
  edit_reason VARCHAR(255),
  word_count INTEGER,
  version INTEGER NOT NULL,
  cook_method INTEGER NOT NULL,
  wiki BOOLEAN NOT NULL,
  baked_at TIMESTAMP,
  baked_version INTEGER,
  hidden_at TIMESTAMP,
  self_edits INTEGER NOT NULL,
  reply_quoted BOOLEAN NOT NULL,
  via_email BOOLEAN NOT NULL,
  raw_email VARCHAR(255),
  public_version INTEGER NOT NULL,
  action_code VARCHAR(255),
  image_url VARCHAR(255),
  locked_by_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (topic_id, post_number)
);

CREATE TABLE topics (
  id INTEGER NOT NULL,
  title VARCHAR(255) NOT NULL,
  last_posted_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  views INTEGER NOT NULL,
  posts_count INTEGER NOT NULL,
  user_id INTEGER,
  last_post_user_id INTEGER NOT NULL,
  reply_count INTEGER NOT NULL,
  featured_user1_id INTEGER,
  featured_user2_id INTEGER,
  featured_user3_id INTEGER,
  avg_time INTEGER,
  deleted_at TIMESTAMP,
  highest_post_number INTEGER NOT NULL,
  image_url VARCHAR(255),
  like_count INTEGER NOT NULL,
  incoming_link_count INTEGER NOT NULL,
  category_id INTEGER,
  visible BOOLEAN NOT NULL,
  moderator_posts_count INTEGER NOT NULL,
  closed BOOLEAN NOT NULL,
  archived BOOLEAN NOT NULL,
  bumped_at TIMESTAMP NOT NULL,
  has_summary BOOLEAN NOT NULL,
  archetype VARCHAR(255) NOT NULL,
  featured_user4_id INTEGER,
  notify_moderators_count INTEGER NOT NULL,
  spam_count INTEGER NOT NULL,
  pinned_at TIMESTAMP,
  score FLOAT,
  "percent_rank" FLOAT NOT NULL,
  subtype VARCHAR(255),
  slug VARCHAR(255),
  deleted_by_id INTEGER,
  participant_count INTEGER,
  word_count INTEGER,
  excerpt VARCHAR(255),
  pinned_globally BOOLEAN NOT NULL,
  pinned_until TIMESTAMP,
  fancy_title VARCHAR(255),
  highest_staff_post_number INTEGER NOT NULL,
  featured_link VARCHAR(255),
  reviewable_score FLOAT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE badge_types (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE badges (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  badge_type_id INTEGER NOT NULL,
  grant_count INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  allow_title BOOLEAN NOT NULL,
  multiple_grant BOOLEAN NOT NULL,
  icon VARCHAR(255),
  listable BOOLEAN,
  target_posts BOOLEAN,
  query VARCHAR(255),
  enabled BOOLEAN NOT NULL,
  auto_revoke BOOLEAN NOT NULL,
  badge_grouping_id INTEGER NOT NULL,
  "trigger" INTEGER,
  show_posts BOOLEAN NOT NULL,
  "system" BOOLEAN NOT NULL,
  image VARCHAR(255),
  long_description VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE bookmarks (
  id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  topic_id BIGINT NOT NULL,
  post_id BIGINT NOT NULL,
  name VARCHAR(255),
  reminder_type INTEGER,
  reminder_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  reminder_last_sent_at TIMESTAMP,
  reminder_set_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (user_id, post_id)
);

CREATE TABLE categories_web_hooks (
  web_hook_id INTEGER NOT NULL,
  category_id INTEGER NOT NULL,
  UNIQUE (web_hook_id, category_id)
);

CREATE TABLE category_custom_fields (
  id INTEGER NOT NULL,
  category_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE category_featured_topics (
  category_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  "rank" INTEGER NOT NULL,
  id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (category_id, topic_id)
);

CREATE TABLE category_groups (
  id INTEGER NOT NULL,
  category_id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  permission_type INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE category_search_data (
  category_id INTEGER NOT NULL,
  search_data VARCHAR(255),
  raw_data VARCHAR(255),
  locale VARCHAR(255),
  version INTEGER,
  PRIMARY KEY (category_id)
);

CREATE TABLE category_tag_groups (
  id INTEGER NOT NULL,
  category_id INTEGER NOT NULL,
  tag_group_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (category_id, tag_group_id)
);

CREATE TABLE category_tag_stats (
  id BIGINT NOT NULL,
  category_id BIGINT NOT NULL,
  tag_id BIGINT NOT NULL,
  topic_count INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (category_id, tag_id)
);

CREATE TABLE category_tags (
  id INTEGER NOT NULL,
  category_id INTEGER NOT NULL,
  tag_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (category_id, tag_id),
  UNIQUE (tag_id, category_id)
);

CREATE TABLE category_users (
  id INTEGER NOT NULL,
  category_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  notification_level INTEGER,
  last_seen_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (category_id, user_id),
  UNIQUE (user_id, category_id)
);

CREATE TABLE child_themes (
  id INTEGER NOT NULL,
  parent_theme_id INTEGER,
  child_theme_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (child_theme_id, parent_theme_id),
  UNIQUE (parent_theme_id, child_theme_id)
);

CREATE TABLE color_scheme_colors (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  hex VARCHAR(255) NOT NULL,
  color_scheme_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE color_schemes (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  version INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  via_wizard BOOLEAN NOT NULL,
  base_scheme_id VARCHAR(255),
  theme_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE custom_emojis (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  upload_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE developers (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id)
);

CREATE TABLE directory_items (
  id INTEGER NOT NULL,
  period_type INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  likes_received INTEGER NOT NULL,
  likes_given INTEGER NOT NULL,
  topics_entered INTEGER NOT NULL,
  topic_count INTEGER NOT NULL,
  post_count INTEGER NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  days_visited INTEGER NOT NULL,
  posts_read INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (period_type, user_id)
);

CREATE TABLE draft_sequences (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  draft_key VARCHAR(255) NOT NULL,
  sequence INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, draft_key)
);

CREATE TABLE drafts (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  draft_key VARCHAR(255) NOT NULL,
  "data" VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  sequence INTEGER NOT NULL,
  revisions INTEGER NOT NULL,
  owner VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (user_id, draft_key)
);

CREATE TABLE email_change_requests (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  old_email VARCHAR(255) NOT NULL,
  new_email VARCHAR(255) NOT NULL,
  old_email_token_id INTEGER,
  new_email_token_id INTEGER,
  change_state INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE email_logs (
  id INTEGER NOT NULL,
  to_address VARCHAR(255) NOT NULL,
  email_type VARCHAR(255) NOT NULL,
  user_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  post_id INTEGER,
  bounce_key VARCHAR(255),
  bounced BOOLEAN NOT NULL,
  message_id VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE email_tokens (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  email VARCHAR(255) NOT NULL,
  token VARCHAR(255) NOT NULL,
  confirmed BOOLEAN NOT NULL,
  expired BOOLEAN NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (token)
);

CREATE TABLE embeddable_hosts (
  id INTEGER NOT NULL,
  host VARCHAR(255) NOT NULL,
  category_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  path_whitelist VARCHAR(255),
  class_name VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE github_user_infos (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  screen_name VARCHAR(255) NOT NULL,
  github_user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (github_user_id),
  UNIQUE (user_id)
);

CREATE TABLE given_daily_likes (
  user_id INTEGER NOT NULL,
  likes_given INTEGER NOT NULL,
  given_date DATE NOT NULL,
  limit_reached BOOLEAN NOT NULL,
  UNIQUE (user_id, given_date)
);

CREATE TABLE group_archived_messages (
  id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, topic_id)
);

CREATE TABLE group_custom_fields (
  id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE group_histories (
  id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  acting_user_id INTEGER NOT NULL,
  target_user_id INTEGER,
  action INTEGER NOT NULL,
  subject VARCHAR(255),
  prev_value VARCHAR(255),
  new_value VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE group_mentions (
  id INTEGER NOT NULL,
  post_id INTEGER,
  group_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, post_id),
  UNIQUE (post_id, group_id)
);

CREATE TABLE group_requests (
  id BIGINT NOT NULL,
  group_id INTEGER,
  user_id INTEGER,
  reason VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, user_id)
);

CREATE TABLE group_users (
  id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  owner BOOLEAN NOT NULL,
  notification_level INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, user_id),
  UNIQUE (user_id, group_id)
);

CREATE TABLE "groups" (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  automatic BOOLEAN NOT NULL,
  user_count INTEGER NOT NULL,
  automatic_membership_email_domains VARCHAR(255),
  automatic_membership_retroactive BOOLEAN,
  primary_group BOOLEAN NOT NULL,
  title VARCHAR(255),
  grant_trust_level INTEGER,
  incoming_email VARCHAR(255),
  has_messages BOOLEAN NOT NULL,
  flair_url VARCHAR(255),
  flair_bg_color VARCHAR(255),
  flair_color VARCHAR(255),
  bio_raw VARCHAR(255),
  bio_cooked VARCHAR(255),
  allow_membership_requests BOOLEAN NOT NULL,
  full_name VARCHAR(255),
  default_notification_level INTEGER NOT NULL,
  visibility_level INTEGER NOT NULL,
  public_exit BOOLEAN NOT NULL,
  public_admission BOOLEAN NOT NULL,
  membership_request_template VARCHAR(255),
  messageable_level INTEGER,
  mentionable_level INTEGER,
  publish_read_state BOOLEAN NOT NULL,
  members_visibility_level INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (incoming_email),
  UNIQUE (name)
);

CREATE TABLE groups_web_hooks (
  web_hook_id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  UNIQUE (web_hook_id, group_id)
);

CREATE TABLE ignored_users (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  ignored_user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  summarized_at TIMESTAMP,
  expiring_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (ignored_user_id, user_id),
  UNIQUE (user_id, ignored_user_id)
);

CREATE TABLE incoming_domains (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  https BOOLEAN NOT NULL,
  port INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (name, https, port)
);

CREATE TABLE incoming_emails (
  id INTEGER NOT NULL,
  user_id INTEGER,
  topic_id INTEGER,
  post_id INTEGER,
  raw VARCHAR(255),
  error VARCHAR(255),
  message_id VARCHAR(255),
  from_address VARCHAR(255),
  to_addresses VARCHAR(255),
  cc_addresses VARCHAR(255),
  subject VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  rejection_message VARCHAR(255),
  is_auto_generated BOOLEAN,
  is_bounce BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE incoming_links (
  id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  user_id INTEGER,
  ip_address VARCHAR(255),
  current_user_id INTEGER,
  post_id INTEGER NOT NULL,
  incoming_referer_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE incoming_referers (
  id INTEGER NOT NULL,
  path VARCHAR(255) NOT NULL,
  incoming_domain_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (path, incoming_domain_id)
);

CREATE TABLE invited_groups (
  id INTEGER NOT NULL,
  group_id INTEGER,
  invite_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE invites (
  id INTEGER NOT NULL,
  invite_key VARCHAR(255) NOT NULL,
  email VARCHAR(255),
  invited_by_id INTEGER NOT NULL,
  user_id INTEGER,
  redeemed_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  deleted_at TIMESTAMP,
  deleted_by_id INTEGER,
  invalidated_at TIMESTAMP,
  moderator BOOLEAN NOT NULL,
  custom_message VARCHAR(255),
  emailed_status INTEGER,
  PRIMARY KEY (id),
  UNIQUE (invite_key)
);

CREATE TABLE javascript_caches (
  id BIGINT NOT NULL,
  theme_field_id BIGINT,
  digest VARCHAR(255),
  content VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  theme_id BIGINT,
  PRIMARY KEY (id)
);

CREATE TABLE message_bus (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  context VARCHAR(255),
  "data" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE muted_users (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  muted_user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (muted_user_id, user_id),
  UNIQUE (user_id, muted_user_id)
);

CREATE TABLE notifications (
  id INTEGER NOT NULL,
  notification_type INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  "data" VARCHAR(255) NOT NULL,
  read BOOLEAN NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  topic_id INTEGER,
  post_number INTEGER,
  post_action_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE oauth2_user_infos (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  uid VARCHAR(255) NOT NULL,
  provider VARCHAR(255) NOT NULL,
  email VARCHAR(255),
  name VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (uid, provider)
);

CREATE TABLE onceoff_logs (
  id INTEGER NOT NULL,
  job_name VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE optimized_images (
  id INTEGER NOT NULL,
  sha1 VARCHAR(255) NOT NULL,
  extension VARCHAR(255) NOT NULL,
  width INTEGER NOT NULL,
  height INTEGER NOT NULL,
  upload_id INTEGER NOT NULL,
  url VARCHAR(255) NOT NULL,
  filesize INTEGER,
  etag VARCHAR(255),
  version INTEGER,
  PRIMARY KEY (id),
  UNIQUE (upload_id, width, height)
);

CREATE TABLE permalinks (
  id INTEGER NOT NULL,
  url VARCHAR(255) NOT NULL,
  topic_id INTEGER,
  post_id INTEGER,
  category_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  external_url VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (url)
);

CREATE TABLE plugin_store_rows (
  id INTEGER NOT NULL,
  plugin_name VARCHAR(255) NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  type_name VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (plugin_name, "key")
);

CREATE TABLE poll_options (
  id BIGINT NOT NULL,
  poll_id BIGINT,
  digest VARCHAR(255) NOT NULL,
  html VARCHAR(255) NOT NULL,
  anonymous_votes INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (poll_id, digest)
);

CREATE TABLE poll_votes (
  poll_id BIGINT,
  poll_option_id BIGINT,
  user_id BIGINT,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  UNIQUE (poll_id, poll_option_id, user_id)
);

CREATE TABLE polls (
  id BIGINT NOT NULL,
  post_id BIGINT,
  name VARCHAR(255) NOT NULL,
  close_at TIMESTAMP,
  "type" INTEGER NOT NULL,
  status INTEGER NOT NULL,
  results INTEGER NOT NULL,
  visibility INTEGER NOT NULL,
  "min" INTEGER,
  "max" INTEGER,
  step INTEGER,
  anonymous_voters INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  chart_type INTEGER NOT NULL,
  "groups" VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (post_id, name)
);

CREATE TABLE post_action_types (
  name_key VARCHAR(255) NOT NULL,
  is_flag BOOLEAN NOT NULL,
  icon VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  id INTEGER NOT NULL,
  "position" INTEGER NOT NULL,
  score_bonus FLOAT NOT NULL,
  reviewable_priority INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE post_actions (
  id INTEGER NOT NULL,
  post_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  post_action_type_id INTEGER NOT NULL,
  deleted_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  deleted_by_id INTEGER,
  related_post_id INTEGER,
  staff_took_action BOOLEAN NOT NULL,
  deferred_by_id INTEGER,
  targets_topic BOOLEAN NOT NULL,
  agreed_at TIMESTAMP,
  agreed_by_id INTEGER,
  deferred_at TIMESTAMP,
  disagreed_at TIMESTAMP,
  disagreed_by_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE post_custom_fields (
  id INTEGER NOT NULL,
  post_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE post_details (
  id INTEGER NOT NULL,
  post_id INTEGER,
  "key" VARCHAR(255),
  "value" VARCHAR(255),
  extra VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (post_id, "key")
);

CREATE TABLE post_replies (
  post_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  reply_post_id INTEGER,
  UNIQUE (post_id, reply_post_id)
);

CREATE TABLE post_reply_keys (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  post_id INTEGER NOT NULL,
  reply_key VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (reply_key),
  UNIQUE (user_id, post_id)
);

CREATE TABLE post_revisions (
  id INTEGER NOT NULL,
  user_id INTEGER,
  post_id INTEGER,
  modifications VARCHAR(255),
  number INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  hidden BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE post_search_data (
  post_id INTEGER NOT NULL,
  search_data VARCHAR(255),
  raw_data VARCHAR(255),
  locale VARCHAR(255),
  version INTEGER,
  PRIMARY KEY (post_id)
);

CREATE TABLE post_stats (
  id INTEGER NOT NULL,
  post_id INTEGER,
  drafts_saved INTEGER,
  typing_duration_msecs INTEGER,
  composer_open_duration_msecs INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE post_timings (
  topic_id INTEGER NOT NULL,
  post_number INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  msecs INTEGER NOT NULL,
  UNIQUE (topic_id, post_number, user_id)
);

CREATE TABLE post_uploads (
  id INTEGER NOT NULL,
  post_id INTEGER NOT NULL,
  upload_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (post_id, upload_id)
);

CREATE TABLE push_subscriptions (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  "data" VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE quoted_posts (
  id INTEGER NOT NULL,
  post_id INTEGER NOT NULL,
  quoted_post_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (post_id, quoted_post_id),
  UNIQUE (quoted_post_id, post_id)
);

CREATE TABLE remote_themes (
  id INTEGER NOT NULL,
  remote_url VARCHAR(255) NOT NULL,
  remote_version VARCHAR(255),
  local_version VARCHAR(255),
  about_url VARCHAR(255),
  license_url VARCHAR(255),
  commits_behind INTEGER,
  remote_updated_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  private_key VARCHAR(255),
  branch VARCHAR(255),
  last_error_text VARCHAR(255),
  authors VARCHAR(255),
  theme_version VARCHAR(255),
  minimum_discourse_version VARCHAR(255),
  maximum_discourse_version VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE reviewable_claimed_topics (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (topic_id)
);

CREATE TABLE reviewable_histories (
  id BIGINT NOT NULL,
  reviewable_id INTEGER NOT NULL,
  reviewable_history_type INTEGER NOT NULL,
  status INTEGER NOT NULL,
  created_by_id INTEGER NOT NULL,
  edited VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE reviewable_scores (
  id BIGINT NOT NULL,
  reviewable_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  reviewable_score_type INTEGER NOT NULL,
  status INTEGER NOT NULL,
  score FLOAT NOT NULL,
  take_action_bonus FLOAT NOT NULL,
  reviewed_by_id INTEGER,
  reviewed_at TIMESTAMP,
  meta_topic_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  reason VARCHAR(255),
  user_accuracy_bonus FLOAT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE reviewables (
  id BIGINT NOT NULL,
  "type" VARCHAR(255) NOT NULL,
  status INTEGER NOT NULL,
  created_by_id INTEGER NOT NULL,
  reviewable_by_moderator BOOLEAN NOT NULL,
  reviewable_by_group_id INTEGER,
  category_id INTEGER,
  topic_id INTEGER,
  score FLOAT NOT NULL,
  potential_spam BOOLEAN NOT NULL,
  target_id INTEGER,
  target_type VARCHAR(255),
  target_created_by_id INTEGER,
  payload VARCHAR(255),
  version INTEGER NOT NULL,
  latest_score TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE ("type", target_id)
);

CREATE TABLE scheduler_stats (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  hostname VARCHAR(255) NOT NULL,
  pid INTEGER NOT NULL,
  duration_ms INTEGER,
  live_slots_start INTEGER,
  live_slots_finish INTEGER,
  started_at TIMESTAMP NOT NULL,
  success BOOLEAN,
  error VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE schema_migration_details (
  id INTEGER NOT NULL,
  version VARCHAR(255) NOT NULL,
  name VARCHAR(255),
  hostname VARCHAR(255),
  git_version VARCHAR(255),
  rails_version VARCHAR(255),
  duration INTEGER,
  direction VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE schema_migrations (
  version VARCHAR(255) NOT NULL,
  PRIMARY KEY (version)
);

CREATE TABLE screened_emails (
  id INTEGER NOT NULL,
  email VARCHAR(255) NOT NULL,
  action_type INTEGER NOT NULL,
  match_count INTEGER NOT NULL,
  last_match_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  ip_address VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (email)
);

CREATE TABLE screened_ip_addresses (
  id INTEGER NOT NULL,
  ip_address VARCHAR(255) NOT NULL,
  action_type INTEGER NOT NULL,
  match_count INTEGER NOT NULL,
  last_match_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (ip_address)
);

CREATE TABLE screened_urls (
  id INTEGER NOT NULL,
  url VARCHAR(255) NOT NULL,
  domain VARCHAR(255) NOT NULL,
  action_type INTEGER NOT NULL,
  match_count INTEGER NOT NULL,
  last_match_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  ip_address VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (url)
);

CREATE TABLE search_logs (
  id INTEGER NOT NULL,
  term VARCHAR(255) NOT NULL,
  user_id INTEGER,
  ip_address VARCHAR(255),
  search_result_id INTEGER,
  search_type INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  search_result_type INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE shared_drafts (
  topic_id INTEGER NOT NULL,
  category_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  id BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (topic_id)
);

CREATE TABLE single_sign_on_records (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  external_id VARCHAR(255) NOT NULL,
  last_payload VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  external_username VARCHAR(255),
  external_email VARCHAR(255),
  external_name VARCHAR(255),
  external_avatar_url VARCHAR(255),
  external_profile_background_url VARCHAR(255),
  external_card_background_url VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (external_id)
);

CREATE TABLE site_settings (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  data_type INTEGER NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE skipped_email_logs (
  id BIGINT NOT NULL,
  email_type VARCHAR(255) NOT NULL,
  to_address VARCHAR(255) NOT NULL,
  user_id INTEGER,
  post_id INTEGER,
  reason_type INTEGER NOT NULL,
  custom_reason VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE stylesheet_cache (
  id INTEGER NOT NULL,
  target VARCHAR(255) NOT NULL,
  digest VARCHAR(255) NOT NULL,
  content VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  theme_id INTEGER NOT NULL,
  source_map VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (target, digest)
);

CREATE TABLE tag_group_memberships (
  id INTEGER NOT NULL,
  tag_id INTEGER NOT NULL,
  tag_group_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (tag_group_id, tag_id)
);

CREATE TABLE tag_group_permissions (
  id BIGINT NOT NULL,
  tag_group_id BIGINT NOT NULL,
  group_id BIGINT NOT NULL,
  permission_type INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE tag_groups (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  parent_tag_id INTEGER,
  one_per_topic BOOLEAN,
  PRIMARY KEY (id)
);

CREATE TABLE tag_search_data (
  tag_id INTEGER NOT NULL,
  search_data VARCHAR(255),
  raw_data VARCHAR(255),
  locale VARCHAR(255),
  version INTEGER,
  PRIMARY KEY (tag_id)
);

CREATE TABLE tag_users (
  id INTEGER NOT NULL,
  tag_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  notification_level INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, tag_id, notification_level),
  UNIQUE (tag_id, user_id, notification_level)
);

CREATE TABLE tags (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  topic_count INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  pm_topic_count INTEGER NOT NULL,
  target_tag_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE tags_web_hooks (
  web_hook_id BIGINT NOT NULL,
  tag_id BIGINT NOT NULL,
  UNIQUE (web_hook_id, tag_id)
);

CREATE TABLE theme_fields (
  id INTEGER NOT NULL,
  theme_id INTEGER NOT NULL,
  target_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  "value" VARCHAR(255) NOT NULL,
  value_baked VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  compiler_version VARCHAR(255) NOT NULL,
  error VARCHAR(255),
  upload_id INTEGER,
  type_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (theme_id, target_id, type_id, name)
);

CREATE TABLE theme_modifier_sets (
  id BIGINT NOT NULL,
  theme_id BIGINT NOT NULL,
  serialize_topic_excerpts BOOLEAN,
  csp_extensions VARCHAR(255),
  svg_icons VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (theme_id)
);

CREATE TABLE theme_settings (
  id BIGINT NOT NULL,
  name VARCHAR(255) NOT NULL,
  data_type INTEGER NOT NULL,
  "value" VARCHAR(255),
  theme_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE theme_translation_overrides (
  id BIGINT NOT NULL,
  theme_id INTEGER NOT NULL,
  locale VARCHAR(255) NOT NULL,
  translation_key VARCHAR(255) NOT NULL,
  "value" VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (theme_id, locale, translation_key)
);

CREATE TABLE themes (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  compiler_version INTEGER NOT NULL,
  user_selectable BOOLEAN NOT NULL,
  hidden BOOLEAN NOT NULL,
  color_scheme_id INTEGER,
  remote_theme_id INTEGER,
  component BOOLEAN NOT NULL,
  enabled BOOLEAN NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (remote_theme_id)
);

CREATE TABLE top_topics (
  id INTEGER NOT NULL,
  topic_id INTEGER,
  yearly_posts_count INTEGER NOT NULL,
  yearly_views_count INTEGER NOT NULL,
  yearly_likes_count INTEGER NOT NULL,
  monthly_posts_count INTEGER NOT NULL,
  monthly_views_count INTEGER NOT NULL,
  monthly_likes_count INTEGER NOT NULL,
  weekly_posts_count INTEGER NOT NULL,
  weekly_views_count INTEGER NOT NULL,
  weekly_likes_count INTEGER NOT NULL,
  daily_posts_count INTEGER NOT NULL,
  daily_views_count INTEGER NOT NULL,
  daily_likes_count INTEGER NOT NULL,
  daily_score FLOAT,
  weekly_score FLOAT,
  monthly_score FLOAT,
  yearly_score FLOAT,
  all_score FLOAT,
  daily_op_likes_count INTEGER NOT NULL,
  weekly_op_likes_count INTEGER NOT NULL,
  monthly_op_likes_count INTEGER NOT NULL,
  yearly_op_likes_count INTEGER NOT NULL,
  quarterly_posts_count INTEGER NOT NULL,
  quarterly_views_count INTEGER NOT NULL,
  quarterly_likes_count INTEGER NOT NULL,
  quarterly_score FLOAT,
  quarterly_op_likes_count INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (topic_id)
);

CREATE TABLE topic_allowed_groups (
  id INTEGER NOT NULL,
  group_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, topic_id),
  UNIQUE (topic_id, group_id)
);

CREATE TABLE topic_allowed_users (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (topic_id, user_id),
  UNIQUE (user_id, topic_id)
);

CREATE TABLE topic_custom_fields (
  id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE topic_embeds (
  id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  post_id INTEGER NOT NULL,
  embed_url VARCHAR(255) NOT NULL,
  content_sha1 VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  deleted_at TIMESTAMP,
  deleted_by_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (embed_url)
);

CREATE TABLE topic_groups (
  id BIGINT NOT NULL,
  group_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  last_read_post_number INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (group_id, topic_id)
);

CREATE TABLE topic_invites (
  id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  invite_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (topic_id, invite_id)
);

CREATE TABLE topic_link_clicks (
  id INTEGER NOT NULL,
  topic_link_id INTEGER NOT NULL,
  user_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  ip_address VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE topic_links (
  id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  post_id INTEGER,
  user_id INTEGER NOT NULL,
  url VARCHAR(255) NOT NULL,
  domain VARCHAR(255) NOT NULL,
  internal BOOLEAN NOT NULL,
  link_topic_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  reflection BOOLEAN,
  clicks INTEGER NOT NULL,
  link_post_id INTEGER,
  title VARCHAR(255),
  crawled_at TIMESTAMP,
  quote BOOLEAN NOT NULL,
  extension VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (topic_id, post_id, url)
);

CREATE TABLE topic_search_data (
  topic_id INTEGER NOT NULL,
  raw_data VARCHAR(255),
  locale VARCHAR(255) NOT NULL,
  search_data VARCHAR(255),
  version INTEGER,
  PRIMARY KEY (topic_id)
);

CREATE TABLE topic_tags (
  id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  tag_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (topic_id, tag_id)
);

CREATE TABLE topic_timers (
  id INTEGER NOT NULL,
  execute_at TIMESTAMP NOT NULL,
  status_type INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  based_on_last_post BOOLEAN NOT NULL,
  deleted_at TIMESTAMP,
  deleted_by_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  category_id INTEGER,
  public_type BOOLEAN,
  duration INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE topic_users (
  user_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  posted BOOLEAN NOT NULL,
  last_read_post_number INTEGER,
  highest_seen_post_number INTEGER,
  last_visited_at TIMESTAMP,
  first_visited_at TIMESTAMP,
  notification_level INTEGER NOT NULL,
  notifications_changed_at TIMESTAMP,
  notifications_reason_id INTEGER,
  total_msecs_viewed INTEGER NOT NULL,
  cleared_pinned_at TIMESTAMP,
  id INTEGER NOT NULL,
  last_emailed_post_number INTEGER,
  liked BOOLEAN,
  bookmarked BOOLEAN,
  PRIMARY KEY (id),
  UNIQUE (topic_id, user_id),
  UNIQUE (user_id, topic_id)
);

CREATE TABLE topic_views (
  topic_id INTEGER NOT NULL,
  viewed_at DATE NOT NULL,
  user_id INTEGER,
  ip_address VARCHAR(255),
  UNIQUE (user_id, ip_address, topic_id)
);

CREATE TABLE translation_overrides (
  id INTEGER NOT NULL,
  locale VARCHAR(255) NOT NULL,
  translation_key VARCHAR(255) NOT NULL,
  "value" VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  compiled_js VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (locale, translation_key)
);

CREATE TABLE unsubscribe_keys (
  "key" VARCHAR(255) NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  unsubscribe_key_type VARCHAR(255),
  topic_id INTEGER,
  post_id INTEGER,
  PRIMARY KEY ("key")
);

CREATE TABLE uploads (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  original_filename VARCHAR(255) NOT NULL,
  filesize INTEGER NOT NULL,
  width INTEGER,
  height INTEGER,
  url VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  sha1 VARCHAR(255),
  origin VARCHAR(255),
  retain_hours INTEGER,
  extension VARCHAR(255),
  thumbnail_width INTEGER,
  thumbnail_height INTEGER,
  etag VARCHAR(255),
  secure BOOLEAN NOT NULL,
  access_control_post_id BIGINT,
  original_sha1 VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (sha1)
);

CREATE TABLE user_actions (
  id INTEGER NOT NULL,
  action_type INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  target_topic_id INTEGER,
  target_post_id INTEGER,
  target_user_id INTEGER,
  acting_user_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (action_type, user_id, target_topic_id, target_post_id, acting_user_id)
);

CREATE TABLE user_api_keys (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  client_id VARCHAR(255) NOT NULL,
  "key" VARCHAR(255) NOT NULL,
  application_name VARCHAR(255) NOT NULL,
  push_url VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  revoked_at TIMESTAMP,
  scopes VARCHAR(255) NOT NULL,
  last_used_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (client_id),
  UNIQUE ("key")
);

CREATE TABLE user_archived_messages (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, topic_id)
);

CREATE TABLE user_associated_accounts (
  id BIGINT NOT NULL,
  provider_name VARCHAR(255) NOT NULL,
  provider_uid VARCHAR(255) NOT NULL,
  user_id INTEGER,
  last_used TIMESTAMP NOT NULL,
  info VARCHAR(255) NOT NULL,
  credentials VARCHAR(255) NOT NULL,
  extra VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (provider_name, provider_uid),
  UNIQUE (provider_name, user_id)
);

CREATE TABLE user_auth_token_logs (
  id INTEGER NOT NULL,
  action VARCHAR(255) NOT NULL,
  user_auth_token_id INTEGER,
  user_id INTEGER,
  client_ip VARCHAR(255),
  user_agent VARCHAR(255),
  auth_token VARCHAR(255),
  created_at TIMESTAMP,
  path VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE user_auth_tokens (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  auth_token VARCHAR(255) NOT NULL,
  prev_auth_token VARCHAR(255) NOT NULL,
  user_agent VARCHAR(255),
  auth_token_seen BOOLEAN NOT NULL,
  client_ip VARCHAR(255),
  rotated_at TIMESTAMP NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  seen_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (auth_token),
  UNIQUE (prev_auth_token)
);

CREATE TABLE user_avatars (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  custom_upload_id INTEGER,
  gravatar_upload_id INTEGER,
  last_gravatar_download_attempt TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE user_badges (
  id INTEGER NOT NULL,
  badge_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  granted_at TIMESTAMP NOT NULL,
  granted_by_id INTEGER NOT NULL,
  post_id INTEGER,
  notification_id INTEGER,
  seq INTEGER NOT NULL,
  featured_rank INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE user_custom_fields (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE user_emails (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  email VARCHAR(255) NOT NULL,
  "primary" BOOLEAN NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE user_exports (
  id INTEGER NOT NULL,
  file_name VARCHAR(255) NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  upload_id INTEGER,
  topic_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE user_field_options (
  id INTEGER NOT NULL,
  user_field_id INTEGER NOT NULL,
  "value" VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE user_fields (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  field_type VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  editable BOOLEAN NOT NULL,
  description VARCHAR(255) NOT NULL,
  required BOOLEAN NOT NULL,
  show_on_profile BOOLEAN NOT NULL,
  "position" INTEGER,
  show_on_user_card BOOLEAN NOT NULL,
  external_name VARCHAR(255),
  external_type VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE user_histories (
  id INTEGER NOT NULL,
  action INTEGER NOT NULL,
  acting_user_id INTEGER,
  target_user_id INTEGER,
  details VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  context VARCHAR(255),
  ip_address VARCHAR(255),
  email VARCHAR(255),
  subject VARCHAR(255),
  previous_value VARCHAR(255),
  new_value VARCHAR(255),
  topic_id INTEGER,
  admin_only BOOLEAN,
  post_id INTEGER,
  custom_type VARCHAR(255),
  category_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE user_open_ids (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  email VARCHAR(255) NOT NULL,
  url VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  active BOOLEAN NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE user_options (
  user_id INTEGER NOT NULL,
  mailing_list_mode BOOLEAN NOT NULL,
  email_digests BOOLEAN,
  external_links_in_new_tab BOOLEAN NOT NULL,
  enable_quoting BOOLEAN NOT NULL,
  dynamic_favicon BOOLEAN NOT NULL,
  disable_jump_reply BOOLEAN NOT NULL,
  automatically_unpin_topics BOOLEAN NOT NULL,
  digest_after_minutes INTEGER,
  auto_track_topics_after_msecs INTEGER,
  new_topic_duration_minutes INTEGER,
  last_redirected_to_top_at TIMESTAMP,
  email_previous_replies INTEGER NOT NULL,
  email_in_reply_to BOOLEAN NOT NULL,
  like_notification_frequency INTEGER NOT NULL,
  mailing_list_mode_frequency INTEGER NOT NULL,
  include_tl0_in_digests BOOLEAN,
  notification_level_when_replying INTEGER,
  theme_key_seq INTEGER NOT NULL,
  allow_private_messages BOOLEAN NOT NULL,
  homepage_id INTEGER,
  theme_ids INTEGER NOT NULL,
  hide_profile_and_presence BOOLEAN NOT NULL,
  text_size_key INTEGER NOT NULL,
  text_size_seq INTEGER NOT NULL,
  email_level INTEGER NOT NULL,
  email_messages_level INTEGER NOT NULL,
  title_count_mode_key INTEGER NOT NULL,
  enable_defer BOOLEAN NOT NULL,
  timezone VARCHAR(255),
  UNIQUE (user_id)
);

CREATE TABLE user_profile_views (
  id INTEGER NOT NULL,
  user_profile_id INTEGER NOT NULL,
  viewed_at TIMESTAMP NOT NULL,
  ip_address VARCHAR(255),
  user_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (viewed_at, user_id, ip_address, user_profile_id)
);

CREATE TABLE user_profiles (
  user_id INTEGER NOT NULL,
  location VARCHAR(255),
  website VARCHAR(255),
  bio_raw VARCHAR(255),
  bio_cooked VARCHAR(255),
  dismissed_banner_key INTEGER,
  bio_cooked_version INTEGER,
  badge_granted_title BOOLEAN,
  views INTEGER NOT NULL,
  profile_background_upload_id INTEGER,
  card_background_upload_id INTEGER,
  granted_title_badge_id BIGINT,
  featured_topic_id INTEGER,
  PRIMARY KEY (user_id)
);

CREATE TABLE user_search_data (
  user_id INTEGER NOT NULL,
  search_data VARCHAR(255),
  raw_data VARCHAR(255),
  locale VARCHAR(255),
  version INTEGER,
  PRIMARY KEY (user_id)
);

CREATE TABLE user_second_factors (
  id BIGINT NOT NULL,
  user_id INTEGER NOT NULL,
  "method" INTEGER NOT NULL,
  "data" VARCHAR(255) NOT NULL,
  enabled BOOLEAN NOT NULL,
  last_used TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  name VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE user_security_keys (
  id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  credential_id VARCHAR(255) NOT NULL,
  public_key VARCHAR(255) NOT NULL,
  factor_type INTEGER NOT NULL,
  enabled BOOLEAN NOT NULL,
  name VARCHAR(255) NOT NULL,
  last_used TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (credential_id)
);

CREATE TABLE user_stats (
  user_id INTEGER NOT NULL,
  topics_entered INTEGER NOT NULL,
  time_read INTEGER NOT NULL,
  days_visited INTEGER NOT NULL,
  posts_read_count INTEGER NOT NULL,
  likes_given INTEGER NOT NULL,
  likes_received INTEGER NOT NULL,
  topic_reply_count INTEGER NOT NULL,
  new_since TIMESTAMP NOT NULL,
  read_faq TIMESTAMP,
  first_post_created_at TIMESTAMP,
  post_count INTEGER NOT NULL,
  topic_count INTEGER NOT NULL,
  bounce_score FLOAT NOT NULL,
  reset_bounce_score_after TIMESTAMP,
  flags_agreed INTEGER NOT NULL,
  flags_disagreed INTEGER NOT NULL,
  flags_ignored INTEGER NOT NULL,
  first_unread_at TIMESTAMP NOT NULL,
  distinct_badge_count INTEGER NOT NULL,
  PRIMARY KEY (user_id)
);

CREATE TABLE user_uploads (
  id BIGINT NOT NULL,
  upload_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (upload_id, user_id)
);

CREATE TABLE user_visits (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  visited_at DATE NOT NULL,
  posts_read INTEGER,
  mobile BOOLEAN,
  time_read INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, visited_at)
);

CREATE TABLE user_warnings (
  id INTEGER NOT NULL,
  topic_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  created_by_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (topic_id)
);

CREATE TABLE users (
  id INTEGER NOT NULL,
  username VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  name VARCHAR(255),
  seen_notification_id INTEGER NOT NULL,
  last_posted_at TIMESTAMP,
  password_hash VARCHAR(255),
  salt VARCHAR(255),
  active BOOLEAN NOT NULL,
  username_lower VARCHAR(255) NOT NULL,
  last_seen_at TIMESTAMP,
  admin BOOLEAN NOT NULL,
  last_emailed_at TIMESTAMP,
  trust_level INTEGER NOT NULL,
  approved BOOLEAN NOT NULL,
  approved_by_id INTEGER,
  approved_at TIMESTAMP,
  previous_visit_at TIMESTAMP,
  suspended_at TIMESTAMP,
  suspended_till TIMESTAMP,
  date_of_birth DATE,
  views INTEGER NOT NULL,
  flag_level INTEGER NOT NULL,
  ip_address VARCHAR(255),
  moderator BOOLEAN,
  title VARCHAR(255),
  uploaded_avatar_id INTEGER,
  locale VARCHAR(255),
  primary_group_id INTEGER,
  registration_ip_address VARCHAR(255),
  staged BOOLEAN NOT NULL,
  first_seen_at TIMESTAMP,
  silenced_till TIMESTAMP,
  group_locked_trust_level INTEGER,
  manual_locked_trust_level INTEGER,
  secure_identifier VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (secure_identifier),
  UNIQUE (username),
  UNIQUE (username_lower)
);

CREATE TABLE watched_words (
  id INTEGER NOT NULL,
  word VARCHAR(255) NOT NULL,
  action INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (action, word)
);

CREATE TABLE web_crawler_requests (
  id BIGINT NOT NULL,
  "date" DATE NOT NULL,
  user_agent VARCHAR(255) NOT NULL,
  "count" INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE ("date", user_agent)
);

CREATE TABLE web_hook_event_types (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE web_hook_event_types_hooks (
  web_hook_id INTEGER NOT NULL,
  web_hook_event_type_id INTEGER NOT NULL,
  UNIQUE (web_hook_event_type_id, web_hook_id)
);

CREATE TABLE web_hook_events (
  id INTEGER NOT NULL,
  web_hook_id INTEGER NOT NULL,
  headers VARCHAR(255),
  payload VARCHAR(255),
  status INTEGER,
  response_headers VARCHAR(255),
  response_body VARCHAR(255),
  duration INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE web_hooks (
  id INTEGER NOT NULL,
  payload_url VARCHAR(255) NOT NULL,
  content_type INTEGER NOT NULL,
  last_delivery_status INTEGER NOT NULL,
  status INTEGER NOT NULL,
  secret VARCHAR(255),
  wildcard_web_hook BOOLEAN NOT NULL,
  verify_certificate BOOLEAN NOT NULL,
  active BOOLEAN NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);
