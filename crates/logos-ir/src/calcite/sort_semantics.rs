use crate::ir::{SortDirection, SortNullDirection};

pub fn calcite_text_sort_null_direction(
    text_direction: Option<&str>,
    sort_direction: SortDirection,
) -> Option<SortNullDirection> {
    if let Some(value) = text_direction {
        let lower = value.to_ascii_lowercase();
        if lower.contains("nulls-first") || lower.contains("nulls first") {
            return Some(SortNullDirection::First);
        }
        if lower.contains("nulls-last") || lower.contains("nulls last") {
            return Some(SortNullDirection::Last);
        }
        if lower.starts_with("asc") {
            return SortDirection::Ascending.default_null_direction();
        }
        if lower.starts_with("desc") {
            return SortDirection::Descending.default_null_direction();
        }
    }
    sort_direction.default_null_direction()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_explicit_and_default_calcite_null_directions() {
        assert_eq!(
            calcite_text_sort_null_direction(Some("ASC-nulls-first"), SortDirection::Ascending),
            Some(SortNullDirection::First)
        );
        assert_eq!(
            calcite_text_sort_null_direction(Some("ASC"), SortDirection::Ascending),
            Some(SortNullDirection::Last)
        );
        assert_eq!(
            calcite_text_sort_null_direction(Some("DESC"), SortDirection::Descending),
            Some(SortNullDirection::First)
        );
        assert_eq!(
            calcite_text_sort_null_direction(None, SortDirection::Clustered),
            None
        );
    }
}
