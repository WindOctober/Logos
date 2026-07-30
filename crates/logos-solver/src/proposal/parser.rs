use crate::error::{Error, Result};
use crate::proposal::types::Candidate;

pub fn parse_proposal(raw: &str) -> Result<Candidate> {
    serde_json::from_str(raw).map_err(|error| Error::InvalidCandidate(error.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proposal::Decision;

    #[test]
    fn parses_candidate_json() {
        let raw = "{\"decision\":\"no_candidate\",\"reason\":\"no cex\"}";
        let proposal = parse_proposal(raw).unwrap();
        assert_eq!(proposal.decision, Decision::NoCandidate);
    }

    #[test]
    fn parses_candidate_contract_separately_from_the_wire_format() {
        let raw = "{\"decision\":\"counterexample_candidate\",\"reason\":\"x\"}";
        let proposal = parse_proposal(raw).expect("parse structurally valid candidate JSON");
        assert_eq!(proposal.decision, Decision::CounterexampleCandidate);
        assert!(proposal.witness_sql.is_empty());
    }

    #[test]
    fn needs_review_is_canonical_and_manual_review_remains_a_legacy_alias() {
        let current = parse_proposal("{\"decision\":\"needs_review\"}")
            .expect("parse canonical needs_review decision");
        let legacy = parse_proposal("{\"decision\":\"manual_review\"}")
            .expect("parse legacy manual_review decision");
        assert_eq!(current.decision, Decision::ManualReview);
        assert_eq!(legacy.decision, Decision::ManualReview);
        assert_eq!(
            serde_json::to_value(current).expect("serialize canonical decision")["decision"],
            serde_json::json!("needs_review")
        );
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
