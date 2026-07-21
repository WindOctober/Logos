use crate::error::{Error, Result};
use crate::proposal::types::{Candidate, Decision};

pub fn parse_proposal(raw: &str) -> Result<Candidate> {
    let proposal: Candidate =
        serde_json::from_str(raw).map_err(|error| Error::InvalidCandidate(error.to_string()))?;
    if proposal.decision == Decision::CounterexampleCandidate
        && proposal.witness_sql.trim().is_empty()
    {
        return Err(Error::InvalidCandidate(
            "counterexample_candidate proposal must include witnessSql".to_owned(),
        ));
    }
    Ok(proposal)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_candidate_json() {
        let raw = "{\"decision\":\"no_candidate\",\"reason\":\"no cex\"}";
        let proposal = parse_proposal(raw).unwrap();
        assert_eq!(proposal.decision, Decision::NoCandidate);
    }

    #[test]
    fn rejects_candidate_without_witness_sql() {
        let raw = "{\"decision\":\"counterexample_candidate\",\"reason\":\"x\"}";
        assert!(parse_proposal(raw).is_err());
    }

    #[test]
    fn rejects_non_json_wrappers() {
        let raw = "```json\n{\"decision\":\"no_candidate\"}\n```";
        assert!(parse_proposal(raw).is_err());
    }

    #[test]
    fn rejects_obsolete_verdict_field_and_decision_value() {
        let raw = "{\"verdict\":\"not_eq\",\"reason\":\"x\",\"witnessSql\":\"INSERT INTO t VALUES (1);\"}";
        assert!(parse_proposal(raw).is_err());
    }
}
