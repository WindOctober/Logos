CREATE TABLE ar_internal_metadata (
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY ("key")
);

CREATE TABLE comments (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP,
  short_id VARCHAR(255) NOT NULL,
  story_id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  parent_comment_id BIGINT,
  thread_id BIGINT,
  comment VARCHAR(255) NOT NULL,
  upvotes INTEGER NOT NULL,
  downvotes INTEGER NOT NULL,
  confidence FLOAT NOT NULL,
  markeddown_comment VARCHAR(255),
  is_deleted INTEGER,
  is_moderated INTEGER,
  is_from_email INTEGER,
  hat_id BIGINT,
  PRIMARY KEY (id),
  UNIQUE (short_id)
);

CREATE TABLE domains (
  id BIGINT NOT NULL,
  domain VARCHAR(255),
  is_tracker INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  banned_at TIMESTAMP,
  banned_by_user_id INTEGER,
  banned_reason VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE hat_requests (
  id BIGINT NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  user_id BIGINT NOT NULL,
  hat VARCHAR(255) NOT NULL,
  link VARCHAR(255) NOT NULL,
  comment VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE hats (
  id BIGINT NOT NULL,
  created_at TIMESTAMP,
  updated_at TIMESTAMP,
  user_id BIGINT NOT NULL,
  granted_by_user_id BIGINT NOT NULL,
  hat VARCHAR(255) NOT NULL,
  link VARCHAR(255),
  modlog_use INTEGER,
  doffed_at TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE hidden_stories (
  id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  story_id BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, story_id)
);

CREATE TABLE invitation_requests (
  id BIGINT NOT NULL,
  code VARCHAR(255),
  is_verified INTEGER,
  email VARCHAR(255) NOT NULL,
  name VARCHAR(255) NOT NULL,
  memo VARCHAR(255),
  ip_address VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE invitations (
  id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  email VARCHAR(255),
  code VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  memo VARCHAR(255),
  used_at TIMESTAMP,
  new_user_id BIGINT,
  PRIMARY KEY (id)
);

CREATE TABLE keystores (
  "key" VARCHAR(255) NOT NULL,
  "value" BIGINT,
  UNIQUE ("key")
);

CREATE TABLE messages (
  id BIGINT NOT NULL,
  created_at TIMESTAMP,
  author_user_id BIGINT NOT NULL,
  recipient_user_id BIGINT NOT NULL,
  has_been_read INTEGER,
  subject VARCHAR(255),
  body VARCHAR(255),
  short_id VARCHAR(255),
  deleted_by_author INTEGER,
  deleted_by_recipient INTEGER,
  hat_id BIGINT,
  PRIMARY KEY (id),
  UNIQUE (short_id)
);

CREATE TABLE mod_notes (
  id BIGINT NOT NULL,
  moderator_user_id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  note VARCHAR(255) NOT NULL,
  markeddown_note VARCHAR(255) NOT NULL,
  created_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE moderations (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  moderator_user_id BIGINT,
  story_id BIGINT,
  comment_id BIGINT,
  user_id BIGINT,
  action VARCHAR(255),
  reason VARCHAR(255),
  is_from_suggestions INTEGER,
  tag_id BIGINT,
  domain_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE read_ribbons (
  id BIGINT NOT NULL,
  is_following INTEGER,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id BIGINT NOT NULL,
  story_id BIGINT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE saved_stories (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id BIGINT NOT NULL,
  story_id BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, story_id)
);

CREATE TABLE schema_migrations (
  version VARCHAR(255) NOT NULL,
  PRIMARY KEY (version)
);

CREATE TABLE stories (
  id BIGINT NOT NULL,
  created_at TIMESTAMP,
  user_id BIGINT NOT NULL,
  url VARCHAR(255),
  title VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  short_id VARCHAR(255) NOT NULL,
  is_expired INTEGER NOT NULL,
  upvotes INTEGER NOT NULL,
  downvotes INTEGER NOT NULL,
  is_moderated INTEGER NOT NULL,
  hotness FLOAT NOT NULL,
  markeddown_description VARCHAR(255),
  story_cache VARCHAR(255),
  comments_count INTEGER NOT NULL,
  merged_story_id BIGINT,
  unavailable_at TIMESTAMP,
  twitter_id VARCHAR(255),
  user_is_author INTEGER,
  user_is_following INTEGER NOT NULL,
  domain_id BIGINT,
  PRIMARY KEY (id),
  UNIQUE (short_id)
);

CREATE TABLE suggested_taggings (
  id BIGINT NOT NULL,
  story_id BIGINT NOT NULL,
  tag_id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE suggested_titles (
  id BIGINT NOT NULL,
  story_id BIGINT NOT NULL,
  user_id BIGINT NOT NULL,
  title VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE tag_filters (
  id BIGINT NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  user_id BIGINT NOT NULL,
  tag_id BIGINT NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE taggings (
  id BIGINT NOT NULL,
  story_id BIGINT NOT NULL,
  tag_id BIGINT NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (story_id, tag_id)
);

CREATE TABLE tags (
  id BIGINT NOT NULL,
  tag VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  privileged INTEGER,
  is_media INTEGER,
  inactive INTEGER,
  hotness_mod FLOAT,
  permit_by_new_users INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (tag)
);

CREATE TABLE users (
  id BIGINT NOT NULL,
  username VARCHAR(255),
  email VARCHAR(255),
  password_digest VARCHAR(255),
  created_at TIMESTAMP,
  is_admin INTEGER,
  password_reset_token VARCHAR(255),
  session_token VARCHAR(255) NOT NULL,
  about VARCHAR(255),
  invited_by_user_id BIGINT,
  is_moderator INTEGER,
  pushover_mentions INTEGER,
  rss_token VARCHAR(255),
  mailing_list_token VARCHAR(255),
  mailing_list_mode INTEGER,
  karma INTEGER NOT NULL,
  banned_at TIMESTAMP,
  banned_by_user_id BIGINT,
  banned_reason VARCHAR(255),
  deleted_at TIMESTAMP,
  disabled_invite_at TIMESTAMP,
  disabled_invite_by_user_id BIGINT,
  disabled_invite_reason VARCHAR(255),
  settings VARCHAR(255),
  PRIMARY KEY (id),
  UNIQUE (session_token),
  UNIQUE (mailing_list_token),
  UNIQUE (password_reset_token),
  UNIQUE (rss_token),
  UNIQUE (username)
);
