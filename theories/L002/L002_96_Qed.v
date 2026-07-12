(*L002_96_Qed.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                           Proofcase / L002_96_Qed                            │
└──────────────────────────────────────────────────────────────────────────────┘
  TRIVIAL FIXED-POINT LEMMA — QED

  Final theorem closure for the Trivial Fixed-Point Lemma. However a proof is
  semantically presented, its validity admits a semantics-free constructive
  witness. Here semantic implication is a proof-relevant operation over every
  future context; the witness is obtained by reifying that semantic operation
  as syntax.

*)

From L002 Require Export L002_01__Erasure.

Definition SEMANTIC_ELIMINATION_CONTRACT : Type :=
  forall Gamma A,
    Semantic Gamma A ->
    Bare (erase_ctx Gamma) A.

Theorem every_semantic_proof_has_a_nonsemantic_proof :
  SEMANTIC_ELIMINATION_CONTRACT.
Proof.
  exact semantic_erasure_preserves_validity.
Qed.

Theorem semantic_presentation_has_no_independent_validity :
  SEMANTIC_ELIMINATION_CONTRACT.
Proof.
  exact every_semantic_proof_has_a_nonsemantic_proof.
Qed.

Definition TRIVIAL_FIXED_POINT_LEMMA_CONTRACT : Type :=
  SEMANTIC_ELIMINATION_CONTRACT.

Definition L002_FINAL_CONTRACT : Type :=
  TRIVIAL_FIXED_POINT_LEMMA_CONTRACT.

Theorem trivial_fixed_point_lemma_qed :
  TRIVIAL_FIXED_POINT_LEMMA_CONTRACT.
Proof.
  exact every_semantic_proof_has_a_nonsemantic_proof.
Qed.

(* Compatibility name for earlier clients of L002. *)
Theorem intuitionistic_lemma_qed :
  L002_FINAL_CONTRACT.
Proof.
  exact trivial_fixed_point_lemma_qed.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         ASSUMPTION REPORT ARTIFACTS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Redirect "theories/L002/_appendix/_assumptions_constructive/semantic_erasure_preserves_validity"
  Print Assumptions semantic_erasure_preserves_validity.

Redirect "theories/L002/_appendix/_assumptions_constructive/semantic_renaming_is_invisible"
  Print Assumptions semantic_renaming_is_invisible.

Redirect "theories/L002/_appendix/_assumptions_constructive/every_semantic_proof_has_a_nonsemantic_proof"
  Print Assumptions every_semantic_proof_has_a_nonsemantic_proof.

Redirect "theories/L002/_appendix/_assumptions_constructive/trivial_fixed_point_lemma_qed"
  Print Assumptions trivial_fixed_point_lemma_qed.

Redirect "theories/L002/_appendix/_assumptions_constructive/intuitionistic_lemma_qed"
  Print Assumptions intuitionistic_lemma_qed.
