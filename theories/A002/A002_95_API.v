(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Public API surface for A002/CARRYLESS SEQUENT. A single import exposes arithmetic normalization, target-sensitive inductive verification, the end-to-end certified arithmetic entry point, independent certificate replay, local and derivation reflection theorems, plus the legacy compatibility verifier, constructors, parsers, Hilbert-rule checkers, and IO dispatcher.]]@*)

(*@doc.pl@[[Downstream logical developments should prefer `NormalizedProof` and `normalized_verifyb_iff`; arithmetic clients should use the canonical `encode_normalized_*` quotations with `A002_Verify_certified`. Soundness is `certified_verify_accept_sound`, and representational completeness is `certified_verify_complete`. The legacy arithmetic functions remain public for compatibility; artifact generation and sanity probes are excluded from this stable dependency boundary.]]@*)

(*@head.end@*)

From A002 Require Export A002_94_IO.
