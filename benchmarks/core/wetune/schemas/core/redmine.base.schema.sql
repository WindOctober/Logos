CREATE TABLE ar_internal_metadata (
  "key" VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY ("key")
);

CREATE TABLE attachments (
  id INTEGER NOT NULL,
  container_id INTEGER,
  container_type VARCHAR(255),
  filename VARCHAR(255) NOT NULL,
  disk_filename VARCHAR(255) NOT NULL,
  filesize BIGINT NOT NULL,
  content_type VARCHAR(255),
  digest VARCHAR(255) NOT NULL,
  downloads INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  created_on TIMESTAMP,
  description VARCHAR(255),
  disk_directory VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE auth_sources (
  id INTEGER NOT NULL,
  "type" VARCHAR(255) NOT NULL,
  name VARCHAR(255) NOT NULL,
  host VARCHAR(255),
  port INTEGER,
  account VARCHAR(255),
  account_password VARCHAR(255),
  base_dn VARCHAR(255),
  attr_login VARCHAR(255),
  attr_firstname VARCHAR(255),
  attr_lastname VARCHAR(255),
  attr_mail VARCHAR(255),
  onthefly_register INTEGER NOT NULL,
  tls INTEGER NOT NULL,
  "filter" VARCHAR(255),
  timeout INTEGER,
  verify_peer INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE boards (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  "position" INTEGER,
  topics_count INTEGER NOT NULL,
  messages_count INTEGER NOT NULL,
  last_message_id INTEGER,
  parent_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE changes (
  id INTEGER NOT NULL,
  changeset_id INTEGER NOT NULL,
  action VARCHAR(255) NOT NULL,
  path VARCHAR(255) NOT NULL,
  from_path VARCHAR(255),
  from_revision VARCHAR(255),
  revision VARCHAR(255),
  branch VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE changeset_parents (
  changeset_id INTEGER NOT NULL,
  parent_id INTEGER NOT NULL
);

CREATE TABLE changesets (
  id INTEGER NOT NULL,
  repository_id INTEGER NOT NULL,
  revision VARCHAR(255) NOT NULL,
  committer VARCHAR(255),
  committed_on TIMESTAMP NOT NULL,
  comments VARCHAR(255),
  commit_date DATE,
  scmid VARCHAR(255),
  user_id INTEGER,
  PRIMARY KEY (id),
  UNIQUE (repository_id, revision)
);

CREATE TABLE changesets_issues (
  changeset_id INTEGER NOT NULL,
  issue_id INTEGER NOT NULL,
  UNIQUE (changeset_id, issue_id)
);

CREATE TABLE comments (
  id INTEGER NOT NULL,
  commented_type VARCHAR(255) NOT NULL,
  commented_id INTEGER NOT NULL,
  author_id INTEGER NOT NULL,
  content VARCHAR(255),
  created_on TIMESTAMP NOT NULL,
  updated_on TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE custom_field_enumerations (
  id INTEGER NOT NULL,
  custom_field_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  active INTEGER NOT NULL,
  "position" INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE custom_fields (
  id INTEGER NOT NULL,
  "type" VARCHAR(255) NOT NULL,
  name VARCHAR(255) NOT NULL,
  field_format VARCHAR(255) NOT NULL,
  possible_values VARCHAR(255),
  regexp VARCHAR(255),
  min_length INTEGER,
  max_length INTEGER,
  is_required INTEGER NOT NULL,
  is_for_all INTEGER NOT NULL,
  is_filter INTEGER NOT NULL,
  "position" INTEGER,
  searchable INTEGER,
  default_value VARCHAR(255),
  editable INTEGER,
  visible INTEGER NOT NULL,
  multiple INTEGER,
  format_store VARCHAR(255),
  description VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE custom_fields_projects (
  custom_field_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  UNIQUE (custom_field_id, project_id)
);

CREATE TABLE custom_fields_roles (
  custom_field_id INTEGER NOT NULL,
  role_id INTEGER NOT NULL,
  UNIQUE (custom_field_id, role_id)
);

CREATE TABLE custom_fields_trackers (
  custom_field_id INTEGER NOT NULL,
  tracker_id INTEGER NOT NULL,
  UNIQUE (custom_field_id, tracker_id)
);

CREATE TABLE custom_values (
  id INTEGER NOT NULL,
  customized_type VARCHAR(255) NOT NULL,
  customized_id INTEGER NOT NULL,
  custom_field_id INTEGER NOT NULL,
  "value" VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE documents (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  category_id INTEGER NOT NULL,
  title VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  created_on TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE email_addresses (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  address VARCHAR(255) NOT NULL,
  is_default INTEGER NOT NULL,
  notify INTEGER NOT NULL,
  created_on TIMESTAMP NOT NULL,
  updated_on TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE enabled_modules (
  id INTEGER NOT NULL,
  project_id INTEGER,
  name VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE enumerations (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  "position" INTEGER,
  is_default INTEGER NOT NULL,
  "type" VARCHAR(255),
  active INTEGER NOT NULL,
  project_id INTEGER,
  parent_id INTEGER,
  position_name VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE groups_users (
  group_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  UNIQUE (group_id, user_id)
);

CREATE TABLE import_items (
  id INTEGER NOT NULL,
  import_id INTEGER NOT NULL,
  "position" INTEGER NOT NULL,
  obj_id INTEGER,
  message VARCHAR(255),
  unique_id VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE imports (
  id INTEGER NOT NULL,
  "type" VARCHAR(255),
  user_id INTEGER NOT NULL,
  filename VARCHAR(255),
  settings VARCHAR(255),
  total_items INTEGER,
  finished INTEGER NOT NULL,
  created_at TIMESTAMP NOT NULL,
  updated_at TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE issue_categories (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  assigned_to_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE issue_relations (
  id INTEGER NOT NULL,
  issue_from_id INTEGER NOT NULL,
  issue_to_id INTEGER NOT NULL,
  relation_type VARCHAR(255) NOT NULL,
  delay INTEGER,
  PRIMARY KEY (id),
  UNIQUE (issue_from_id, issue_to_id)
);

CREATE TABLE issue_statuses (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  is_closed INTEGER NOT NULL,
  "position" INTEGER,
  default_done_ratio INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE issues (
  id INTEGER NOT NULL,
  tracker_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  subject VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  due_date DATE,
  category_id INTEGER,
  status_id INTEGER NOT NULL,
  assigned_to_id INTEGER,
  priority_id INTEGER NOT NULL,
  fixed_version_id INTEGER,
  author_id INTEGER NOT NULL,
  lock_version INTEGER NOT NULL,
  created_on TIMESTAMP,
  updated_on TIMESTAMP,
  start_date DATE,
  done_ratio INTEGER NOT NULL,
  estimated_hours FLOAT,
  parent_id INTEGER,
  root_id INTEGER,
  lft INTEGER,
  rgt INTEGER,
  is_private INTEGER NOT NULL,
  closed_on TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE journal_details (
  id INTEGER NOT NULL,
  journal_id INTEGER NOT NULL,
  property VARCHAR(255) NOT NULL,
  prop_key VARCHAR(255) NOT NULL,
  old_value VARCHAR(255),
  "value" VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE journals (
  id INTEGER NOT NULL,
  journalized_id INTEGER NOT NULL,
  journalized_type VARCHAR(255) NOT NULL,
  user_id INTEGER NOT NULL,
  notes VARCHAR(255),
  created_on TIMESTAMP NOT NULL,
  private_notes INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE member_roles (
  id INTEGER NOT NULL,
  member_id INTEGER NOT NULL,
  role_id INTEGER NOT NULL,
  inherited_from INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE members (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  created_on TIMESTAMP,
  mail_notification INTEGER NOT NULL,
  PRIMARY KEY (id),
  UNIQUE (user_id, project_id)
);

CREATE TABLE messages (
  id INTEGER NOT NULL,
  board_id INTEGER NOT NULL,
  parent_id INTEGER,
  subject VARCHAR(255) NOT NULL,
  content VARCHAR(255),
  author_id INTEGER,
  replies_count INTEGER NOT NULL,
  last_reply_id INTEGER,
  created_on TIMESTAMP NOT NULL,
  updated_on TIMESTAMP NOT NULL,
  locked INTEGER,
  sticky INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE news (
  id INTEGER NOT NULL,
  project_id INTEGER,
  title VARCHAR(255) NOT NULL,
  summary VARCHAR(255),
  description VARCHAR(255),
  author_id INTEGER NOT NULL,
  created_on TIMESTAMP,
  comments_count INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE open_id_authentication_associations (
  id INTEGER NOT NULL,
  issued INTEGER,
  lifetime INTEGER,
  handle VARCHAR(255),
  assoc_type VARCHAR(255),
  server_url VARCHAR(255),
  secret VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE open_id_authentication_nonces (
  id INTEGER NOT NULL,
  timestamp INTEGER NOT NULL,
  server_url VARCHAR(255),
  salt VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE projects (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  homepage VARCHAR(255),
  is_public INTEGER NOT NULL,
  parent_id INTEGER,
  created_on TIMESTAMP,
  updated_on TIMESTAMP,
  identifier VARCHAR(255),
  status INTEGER NOT NULL,
  lft INTEGER,
  rgt INTEGER,
  inherit_members INTEGER NOT NULL,
  default_version_id INTEGER,
  default_assigned_to_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE projects_trackers (
  project_id INTEGER NOT NULL,
  tracker_id INTEGER NOT NULL,
  UNIQUE (project_id, tracker_id)
);

CREATE TABLE queries (
  id INTEGER NOT NULL,
  project_id INTEGER,
  name VARCHAR(255) NOT NULL,
  filters VARCHAR(255),
  user_id INTEGER NOT NULL,
  column_names VARCHAR(255),
  sort_criteria VARCHAR(255),
  group_by VARCHAR(255),
  "type" VARCHAR(255),
  visibility INTEGER,
  options VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE queries_roles (
  query_id INTEGER NOT NULL,
  role_id INTEGER NOT NULL,
  UNIQUE (query_id, role_id)
);

CREATE TABLE repositories (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  url VARCHAR(255) NOT NULL,
  login VARCHAR(255),
  password VARCHAR(255),
  root_url VARCHAR(255),
  "type" VARCHAR(255),
  path_encoding VARCHAR(255),
  log_encoding VARCHAR(255),
  extra_info VARCHAR(255),
  identifier VARCHAR(255),
  is_default INTEGER,
  created_on TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE roles (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  "position" INTEGER,
  assignable INTEGER,
  builtin INTEGER NOT NULL,
  permissions VARCHAR(255),
  issues_visibility VARCHAR(255) NOT NULL,
  users_visibility VARCHAR(255) NOT NULL,
  time_entries_visibility VARCHAR(255) NOT NULL,
  all_roles_managed INTEGER NOT NULL,
  settings VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE roles_managed_roles (
  role_id INTEGER NOT NULL,
  managed_role_id INTEGER NOT NULL,
  UNIQUE (role_id, managed_role_id)
);

CREATE TABLE schema_migrations (
  version VARCHAR(255) NOT NULL,
  PRIMARY KEY (version)
);

CREATE TABLE settings (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  "value" VARCHAR(255),
  updated_on TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE time_entries (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  author_id INTEGER,
  user_id INTEGER NOT NULL,
  issue_id INTEGER,
  hours FLOAT NOT NULL,
  comments VARCHAR(255),
  activity_id INTEGER NOT NULL,
  spent_on DATE NOT NULL,
  tyear INTEGER NOT NULL,
  tmonth INTEGER NOT NULL,
  tweek INTEGER NOT NULL,
  created_on TIMESTAMP NOT NULL,
  updated_on TIMESTAMP NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE tokens (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  action VARCHAR(255) NOT NULL,
  "value" VARCHAR(255) NOT NULL,
  created_on TIMESTAMP NOT NULL,
  updated_on TIMESTAMP,
  PRIMARY KEY (id),
  UNIQUE ("value")
);

CREATE TABLE trackers (
  id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  is_in_chlog INTEGER NOT NULL,
  "position" INTEGER,
  is_in_roadmap INTEGER NOT NULL,
  fields_bits INTEGER,
  default_status_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE user_preferences (
  id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  others VARCHAR(255),
  hide_mail INTEGER,
  time_zone VARCHAR(255),
  PRIMARY KEY (id)
);

CREATE TABLE users (
  id INTEGER NOT NULL,
  login VARCHAR(255) NOT NULL,
  hashed_password VARCHAR(255) NOT NULL,
  firstname VARCHAR(255) NOT NULL,
  lastname VARCHAR(255) NOT NULL,
  admin INTEGER NOT NULL,
  status INTEGER NOT NULL,
  last_login_on TIMESTAMP,
  language VARCHAR(255),
  auth_source_id INTEGER,
  created_on TIMESTAMP,
  updated_on TIMESTAMP,
  "type" VARCHAR(255),
  identity_url VARCHAR(255),
  mail_notification VARCHAR(255) NOT NULL,
  salt VARCHAR(255),
  must_change_passwd INTEGER NOT NULL,
  passwd_changed_on TIMESTAMP,
  PRIMARY KEY (id)
);

CREATE TABLE versions (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  name VARCHAR(255) NOT NULL,
  description VARCHAR(255),
  effective_date DATE,
  created_on TIMESTAMP,
  updated_on TIMESTAMP,
  wiki_page_title VARCHAR(255),
  status VARCHAR(255),
  sharing VARCHAR(255) NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE watchers (
  id INTEGER NOT NULL,
  watchable_type VARCHAR(255) NOT NULL,
  watchable_id INTEGER NOT NULL,
  user_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE wiki_content_versions (
  id INTEGER NOT NULL,
  wiki_content_id INTEGER NOT NULL,
  page_id INTEGER NOT NULL,
  author_id INTEGER,
  "data" VARCHAR(255),
  compression VARCHAR(255),
  comments VARCHAR(255),
  updated_on TIMESTAMP NOT NULL,
  version INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE wiki_contents (
  id INTEGER NOT NULL,
  page_id INTEGER NOT NULL,
  author_id INTEGER,
  text VARCHAR(255),
  comments VARCHAR(255),
  updated_on TIMESTAMP NOT NULL,
  version INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE wiki_pages (
  id INTEGER NOT NULL,
  wiki_id INTEGER NOT NULL,
  title VARCHAR(255) NOT NULL,
  created_on TIMESTAMP NOT NULL,
  protected INTEGER NOT NULL,
  parent_id INTEGER,
  PRIMARY KEY (id)
);

CREATE TABLE wiki_redirects (
  id INTEGER NOT NULL,
  wiki_id INTEGER NOT NULL,
  title VARCHAR(255),
  redirects_to VARCHAR(255),
  created_on TIMESTAMP NOT NULL,
  redirects_to_wiki_id INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE wikis (
  id INTEGER NOT NULL,
  project_id INTEGER NOT NULL,
  start_page VARCHAR(255) NOT NULL,
  status INTEGER NOT NULL,
  PRIMARY KEY (id)
);

CREATE TABLE workflows (
  id INTEGER NOT NULL,
  tracker_id INTEGER NOT NULL,
  old_status_id INTEGER NOT NULL,
  new_status_id INTEGER NOT NULL,
  role_id INTEGER NOT NULL,
  assignee INTEGER NOT NULL,
  author INTEGER NOT NULL,
  "type" VARCHAR(255),
  field_name VARCHAR(255),
  rule VARCHAR(255),
  PRIMARY KEY (id)
);
