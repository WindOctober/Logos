use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Attempt {
    pub round: usize,
    pub prompt: String,
    pub raw_output: String,
    pub proposal: Candidate,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Candidate {
    pub decision: Decision,
    #[serde(default)]
    pub reason: String,
    #[serde(default)]
    pub witness_sql: String,
    #[serde(default)]
    pub notes: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Decision {
    CounterexampleCandidate,
    NoCandidate,
    ManualReview,
}
