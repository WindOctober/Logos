CREATE TABLE account_deletions (
  id INTEGER NOT NULL,
  person_id INTEGER,
  completed_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (person_id)
);

CREATE TABLE account_migrations (
  id BIGINT NOT NULL,
  old_person_id INTEGER NOT NULL,
  new_person_id INTEGER NOT NULL,
  completed_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (old_person_id, new_person_id),
  UNIQUE (old_person_id)
);

CREATE TABLE ar_internal_metadata (
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY ("key")
);

CREATE TABLE aspect_memberships (
  id INTEGER NOT NULL,
  aspect_id INTEGER NOT NULL,
  contact_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (aspect_id, contact_id)
);

CREATE TABLE aspect_visibilities (
  id INTEGER NOT NULL,
  shareable_id INTEGER NOT NULL,
  aspect_id INTEGER NOT NULL,
  shareable_type VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (shareable_id, shareable_type, aspect_id)
);

CREATE TABLE aspects (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  order_id INTEGER,
  post_default INTEGER,
  PRIMARY KEY (id),
  UNIQUE (user_id, name)
);

CREATE TABLE authorizations (
  id INTEGER NOT NULL,
  user_id INTEGER,
  o_auth_application_id INTEGER,
  refresh_token VARCHAR(255),
  code VARCHAR(255),
  redirect_uri VARCHAR(255),
  nonce VARCHAR(255),
  scopes VARCHAR(255),
  code_used INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE blocks (
  id INTEGER NOT NULL,
  user_id INTEGER,
  person_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (user_id, person_id)
);

CREATE TABLE comment_signatures (
  comment_id INTEGER NOT NULL,
  author_signature VARCHAR(255) NOT NULL,
  signature_order_id INTEGER NOT NULL,
  additional_data VARCHAR(255),
  UNIQUE (comment_id)
);

CREATE TABLE comments (
  id INTEGER NOT NULL,
  text VARCHAR(255) NOT NULL,
  commentable_id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  guid VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  likes_count INTEGER NOT NULL,
  commentable_type VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (guid)
);

CREATE TABLE contacts (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  person_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  sharing INTEGER NOT NULL,
  receiving INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, person_id)
);

CREATE TABLE conversation_visibilities (
  id INTEGER NOT NULL,
  conversation_id INTEGER NOT NULL,
  person_id INTEGER NOT NULL,
  unread INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (conversation_id, person_id)
);

CREATE TABLE conversations (
  id INTEGER NOT NULL,
  subject VARCHAR(255),
  guid VARCHAR(255) NOT NULL,
  author_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (guid)
);

CREATE TABLE invitation_codes (
  id INTEGER NOT NULL,
  token VARCHAR(255),
  user_id INTEGER,
  "count" INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE like_signatures (
  like_id INTEGER NOT NULL,
  author_signature VARCHAR(255) NOT NULL,
  signature_order_id INTEGER NOT NULL,
  additional_data VARCHAR(255),
  UNIQUE (like_id)
);

CREATE TABLE likes (
  id INTEGER NOT NULL,
  positive INTEGER,
  target_id INTEGER,
  author_id INTEGER,
  guid VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  target_type VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (target_id, author_id, target_type),
  UNIQUE (guid)
);

CREATE TABLE locations (
  id INTEGER NOT NULL,
  address VARCHAR(255),
  lat VARCHAR(255),
  lng VARCHAR(255),
  status_message_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE mentions (
  id INTEGER NOT NULL,
  mentions_container_id INTEGER NOT NULL,
  person_id INTEGER NOT NULL,
  mentions_container_type VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (person_id, mentions_container_id, mentions_container_type)
);

CREATE TABLE messages (
  id INTEGER NOT NULL,
  conversation_id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  guid VARCHAR(255) NOT NULL,
  text VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (guid)
);

CREATE TABLE notification_actors (
  id INTEGER NOT NULL,
  notification_id INTEGER,
  person_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (notification_id, person_id)
);

CREATE TABLE notifications (
  id INTEGER NOT NULL,
  target_type VARCHAR(255),
  target_id INTEGER,
  recipient_id INTEGER NOT NULL,
  unread INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  "type" VARCHAR(255),
  guid VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (guid)
);

CREATE TABLE o_auth_access_tokens (
  id INTEGER NOT NULL,
  authorization_id INTEGER,
  token VARCHAR(255),
  expires_at TIMESTAMP,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (token)
);

CREATE TABLE o_auth_applications (
  id INTEGER NOT NULL,
  user_id INTEGER,
  client_id VARCHAR(255),
  client_secret VARCHAR(255),
  client_name VARCHAR(255),
  redirect_uris VARCHAR(255),
  response_types VARCHAR(255),
  grant_types VARCHAR(255),
  application_type VARCHAR(255),
  contacts VARCHAR(255),
  logo_uri VARCHAR(255),
  client_uri VARCHAR(255),
  policy_uri VARCHAR(255),
  tos_uri VARCHAR(255),
  sector_identifier_uri VARCHAR(255),
  token_endpoint_auth_method VARCHAR(255),
  jwks VARCHAR(255),
  jwks_uri VARCHAR(255),
  ppid INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (client_id)
);

CREATE TABLE o_embed_caches (
  id INTEGER NOT NULL,
  url VARCHAR(255) NOT NULL,
  "data" VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE open_graph_caches (
  id INTEGER NOT NULL,
  title VARCHAR(255),
  ob_type VARCHAR(255),
  image VARCHAR(255),
  url VARCHAR(255),
  description VARCHAR(255),
  video_url VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE participations (
  id INTEGER NOT NULL,
  guid VARCHAR(255),
  target_id INTEGER,
  target_type VARCHAR(255) NOT NULL,
  author_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  "count" INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (target_id, target_type, author_id)
);

CREATE TABLE people (
  id INTEGER NOT NULL,
  guid VARCHAR(255) NOT NULL,
  diaspora_handle VARCHAR(255) NOT NULL,
  serialized_public_key VARCHAR(255) NOT NULL,
  owner_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  closed_account INTEGER,
  fetch_status INTEGER,
  pod_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (diaspora_handle),
  UNIQUE (guid),
  UNIQUE (owner_id)
);

CREATE TABLE photos (
  id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  public INTEGER NOT NULL,
  guid VARCHAR(255) NOT NULL,
  pending INTEGER NOT NULL,
  text VARCHAR(255),
  remote_photo_path VARCHAR(255),
  remote_photo_name VARCHAR(255),
  random_string VARCHAR(255),
  processed_image VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  unprocessed_image VARCHAR(255),
  status_message_guid VARCHAR(255),
  height INTEGER,
  width INTEGER,
  PRIMARY KEY (id),
  UNIQUE (guid)
);

CREATE TABLE pods (
  id INTEGER NOT NULL,
  host VARCHAR(255) NOT NULL,
  ssl INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  status INTEGER,
  checked_at TIMESTAMP,
  offline_since TIMESTAMP,
  response_time INTEGER,
  software VARCHAR(255),
  error VARCHAR(255),
  port INTEGER,
  blocked INTEGER,
  scheduled_check INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (host, port)
);

CREATE TABLE poll_answers (
  id INTEGER NOT NULL,
  answer VARCHAR(255) NOT NULL,
  poll_id INTEGER NOT NULL,
  guid VARCHAR(255),
  vote_count INTEGER,
  PRIMARY KEY (id),
  UNIQUE (guid)
);

CREATE TABLE poll_participation_signatures (
  poll_participation_id INTEGER NOT NULL,
  author_signature VARCHAR(255) NOT NULL,
  signature_order_id INTEGER NOT NULL,
  additional_data VARCHAR(255),
  UNIQUE (poll_participation_id)
);

CREATE TABLE poll_participations (
  id INTEGER NOT NULL,
  poll_answer_id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  poll_id INTEGER NOT NULL,
  guid VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (poll_id, author_id),
  UNIQUE (guid)
);

CREATE TABLE polls (
  id INTEGER NOT NULL,
  question VARCHAR(255) NOT NULL,
  status_message_id INTEGER NOT NULL,
  status INTEGER,
  guid VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE (guid)
);

CREATE TABLE posts (
  id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  public INTEGER NOT NULL,
  guid VARCHAR(255) NOT NULL,
  "type" VARCHAR(255) NOT NULL,
  text VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  provider_display_name VARCHAR(255),
  root_guid VARCHAR(255),
  likes_count INTEGER,
  comments_count INTEGER,
  o_embed_cache_id INTEGER,
  reshares_count INTEGER,
  interacted_at TIMESTAMP,
  tweet_id VARCHAR(255),
  open_graph_cache_id INTEGER,
  tumblr_ids VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (guid),
  UNIQUE (author_id, root_guid)
);

CREATE TABLE ppid (
  id INTEGER NOT NULL,
  o_auth_application_id INTEGER,
  user_id INTEGER,
  guid VARCHAR(255),
  identifier VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE profiles (
  id INTEGER NOT NULL,
  diaspora_handle VARCHAR(255),
  first_name VARCHAR(255),
  last_name VARCHAR(255),
  image_url VARCHAR(255),
  image_url_small VARCHAR(255),
  image_url_medium VARCHAR(255),
  birthday DATE,
  gender VARCHAR(255),
  bio VARCHAR(255),
  searchable INTEGER NOT NULL,
  person_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  location VARCHAR(255),
  full_name VARCHAR(255),
  nsfw INTEGER,
  public_details INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE "references" (
  id BIGINT NOT NULL,
  source_id INTEGER NOT NULL,
  source_type VARCHAR(255) NOT NULL,
  target_id INTEGER NOT NULL,
  target_type VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (source_id, source_type, target_id, target_type)
);

CREATE TABLE reports (
  id INTEGER NOT NULL,
  item_id INTEGER NOT NULL,
  item_type VARCHAR(255) NOT NULL,
  reviewed INTEGER,
  text VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  user_id INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE roles (
  id INTEGER NOT NULL,
  person_id INTEGER,
  name VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (person_id, name)
);

CREATE TABLE schema_migrations (
  version VARCHAR(255) NOT NULL,
  PRIMARY KEY (version)
);

CREATE TABLE services (
  id INTEGER NOT NULL,
  "type" VARCHAR(255) NOT NULL,
  user_id INTEGER NOT NULL,
  uid VARCHAR(255),
  access_token VARCHAR(255),
  access_secret VARCHAR(255),
  nickname VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE share_visibilities (
  id INTEGER NOT NULL,
  shareable_id INTEGER NOT NULL,
  hidden INTEGER NOT NULL,
  shareable_type VARCHAR(255) NOT NULL,
  user_id INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (shareable_id, shareable_type, user_id)
);

CREATE TABLE signature_orders (
  id INTEGER NOT NULL,
  "order" VARCHAR(255) NOT NULL,
  PRIMARY KEY (id),
  UNIQUE ("order")
);

CREATE TABLE simple_captcha_data (
  id INTEGER NOT NULL,
  "key" VARCHAR(255),
  "value" VARCHAR(255),
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE tag_followings (
  id INTEGER NOT NULL,
  tag_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (tag_id, user_id)
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
  UNIQUE (taggable_id, taggable_type, tag_id)
);

CREATE TABLE tags (
  id INTEGER NOT NULL,
  name VARCHAR(255),
  taggings_count INTEGER,
  PRIMARY KEY (id),
  UNIQUE (name)
);

CREATE TABLE user_preferences (
  id INTEGER NOT NULL,
  email_type VARCHAR(255),
  user_id INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE users (
  id INTEGER NOT NULL,
  username VARCHAR(255) NOT NULL,
  serialized_private_key VARCHAR(255),
  getting_started INTEGER NOT NULL,
  disable_mail INTEGER NOT NULL,
  language VARCHAR(255),
  email VARCHAR(255) NOT NULL,
  encrypted_password VARCHAR(255) NOT NULL,
  reset_password_token VARCHAR(255),
  remember_created_at TIMESTAMP,
  sign_in_count INTEGER,
  current_sign_in_at TIMESTAMP,
  last_sign_in_at TIMESTAMP,
  current_sign_in_ip VARCHAR(255),
  last_sign_in_ip VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  invited_by_id INTEGER,
  authentication_token VARCHAR(255),
  unconfirmed_email VARCHAR(255),
  confirm_email_token VARCHAR(255),
  locked_at TIMESTAMP,
  show_community_spotlight_in_stream INTEGER NOT NULL,
  auto_follow_back INTEGER,
  auto_follow_back_aspect_id INTEGER,
  hidden_shareables VARCHAR(255),
  reset_password_sent_at TIMESTAMP,
  last_seen TIMESTAMP,
  remove_after TIMESTAMP,
  export VARCHAR(255),
  exported_at TIMESTAMP,
  exporting INTEGER,
  strip_exif INTEGER,
  exported_photos_file VARCHAR(255),
  exported_photos_at TIMESTAMP,
  exporting_photos INTEGER,
  color_theme VARCHAR(255),
  post_default_public INTEGER,
  consumed_timestep INTEGER,
  otp_required_for_login INTEGER,
  otp_backup_codes VARCHAR(255),
  plain_otp_secret VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (email),
  UNIQUE (username),
  UNIQUE (authentication_token)
);
