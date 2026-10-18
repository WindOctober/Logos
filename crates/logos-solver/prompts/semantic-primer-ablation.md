# FormalSQL semantics (lemma-independent reference)

The SQL and schema are the input. Generated Rocq definitions and the fixed
FormalSQL semantics, checked by Rocq, define the verification obligation.
This document supplies no proof route or library lemma recommendations.

`QueryExpr` describes queries; its error-aware evaluation relation describes
possible results. Successful results carry row order and multiplicity. Do not
replace an ordered observation with an unordered one without proving that the
actual verification goal permits this. Sorting ties can admit multiple results.
Filtering keeps rows whose condition accepts; NULL/unknown is not true.

SQL NULL, three-valued conditions, data types, coercions, and runtime errors
must follow the generated definitions. Outcome equivalence preserves possible
successful observations and error categories, and requires inhabited outcomes.
Safe equivalence additionally requires successful execution without SQL errors.
Conditional equivalence requires the specified condition and its validity proof.

Generated schemas fix admissible databases. The read-only witness, when present,
is the only database usable by the unconditional countermodel claim. A failed
proof search is neither a countermodel nor evidence of equivalence. Unavailable
lemmas do not change any of these definitions or verification requirements.
