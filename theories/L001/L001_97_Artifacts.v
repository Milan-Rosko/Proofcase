(*L001_97_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / L001_97_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Certification and artifact boundary for L001. This file packages the
  already proved fixed-point, collapse, and obstruction theorems into the
  named contract endpoints exported from `L001_95_API`, then redirects `Print
  Assumptions` for the terminal contract and the named witness. L001 has no
  computational extraction surface of its own; executable checking and proof
  transformers remain in M001. The meaningful L001 artifact is the assumption
  report for the public lemma endpoints.

  The final exported obstruction is deliberately reductio-shaped: if a sound
  total function decides the closure-acceptance problem in the presence of
  evaluation closure, modus-ponens closure, and consistency, then
  contradiction; therefore no such function exists under those hypotheses.

*)

From L001 Require Export L001_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         CERTIFIED CONTRACT ENDPOINTS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Theorem certified_aporetic_local_branch_collapse_contract :
  APORETIC_LOCAL_BRANCH_COLLAPSE_CONTRACT.
Proof.
  intros C B Hmp Hfix Hlocal.
  exact (local_branch_collapse C B Hmp Hfix Hlocal).
Qed.

Theorem certified_aporetic_core_diagonal_obstruction_contract :
  APORETIC_CORE_DIAGONAL_OBSTRUCTION_CONTRACT.
Proof.
  intros C B Hmp Hcons Hfix Hlocal.
  exact (core_diagonal_obstruction C B Hmp Hcons Hfix Hlocal).
Qed.

Theorem certified_aporetic_eval_bottom_negfixp_contract :
  APORETIC_EVAL_BOTTOM_NEGFIXP_CONTRACT.
Proof.
  intros C Code ev Hbottom.
  exact (eval_bottom_negfixp C Code ev Hbottom).
Qed.

Theorem certified_aporetic_eval_full_to_eval_bottom_contract :
  APORETIC_EVAL_FULL_TO_EVAL_BOTTOM_CONTRACT.
Proof.
  intros C Code E.
  exact (eval_full_to_eval_bottom C Code E).
Qed.

Theorem certified_aporetic_full_frame_obstruction_corollary_contract :
  APORETIC_FULL_FRAME_OBSTRUCTION_COROLLARY_CONTRACT.
Proof.
  intros C Code E Hcons Hmp Hlem.
  exact
    (full_frame_obstruction_corollary
       C Code E Hcons Hmp Hlem).
Qed.

Theorem certified_aporetic_fixed_point_contract :
  APORETIC_FIXED_POINT_CONTRACT.
Proof.
  intros C Code E.
  destruct
    (eval_bottom_negfixp
       C Code (ceval_apply E)
       (eval_full_to_eval_bottom C Code E))
    as [B Hfix].
  exists B.
  exact Hfix.
Qed.

Theorem certified_aporetic_excluded_middle_collapse_contract :
  APORETIC_EXCLUDED_MIDDLE_COLLAPSE_CONTRACT.
Proof.
  intros C Code E Hmp Hlem.
  exact (lem_collapse C Code E Hmp Hlem).
Qed.

Theorem certified_aporetic_excluded_middle_obstruction_contract :
  APORETIC_EXCLUDED_MIDDLE_OBSTRUCTION_CONTRACT.
Proof.
  intros C Code E Hcons Hmp Hlem.
  exact
    (aporetic_obstruction
       C Code E Hcons Hmp Hlem).
Qed.

Theorem certified_aporetic_decision_collapse_contract :
  APORETIC_DECISION_COLLAPSE_CONTRACT.
Proof.
  intros C Code E Hmp D.
  exact (decision_collapse C Code E Hmp D).
Qed.

(*
│
│          Generic decision obstruction. The decision function first
│          produces collapse to `C Bot`; consistency then discharges
│          the contradiction.
│
*)

Theorem closure_evaluation_decision_obstructed_lemma :
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureDecision C ->
    False.
Proof.
  intros C Code E Hcons Hmp D.
  destruct (decision_collapse C Code E Hmp D)
    as [_ [_ [_ Hbot]]].
  exact (Hcons Hbot).
Qed.

Theorem certified_aporetic_decision_obstruction_contract :
  APORETIC_DECISION_OBSTRUCTION_CONTRACT.
Proof.
  exact closure_evaluation_decision_obstructed_lemma.
Qed.

(*
│
│          Equivalence/ad-absurdum impossibility. A negation fixed
│          point plus a sound decision produces `C Bot`; consistency
│          converts that into `False`.
│
*)

Theorem equivalence_ad_absurdum_impossibility_lemma :
  forall (C : ClosureTheory) (B : Formula),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureNegationFixedPoint C B ->
    ClosureDecision C ->
    False.
Proof.
  intros C B Hcons Hmp Hfix D.
  exact
    (negfixp_obstructs_lem
       C B Hcons Hmp Hfix
       (decision_to_lem C D)).
Qed.

Theorem certified_aporetic_equivalence_ad_absurdum_impossibility_contract :
  APORETIC_EQUIVALENCE_AD_ABSURDUM_IMPOSSIBILITY_CONTRACT.
Proof.
  exact equivalence_ad_absurdum_impossibility_lemma.
Qed.

(*
│
│          Existential decider impossibility. If some sound Boolean
│          decision function exists, destruct it and apply the generic
│          decision obstruction.
│
*)

Theorem closure_decider_impossible_lemma :
  forall (C : ClosureTheory) Code
         (E : ClosureEvaluationFrame C Code),
    ClosureConsistent C ->
    ClosureModusPonens C ->
    ClosureDeciderExists C ->
    False.
Proof.
  intros C Code E Hcons Hmp [D _].
  exact (closure_evaluation_decision_obstructed_lemma C Code E Hcons Hmp D).
Qed.

Theorem certified_aporetic_decider_impossibility_contract :
  APORETIC_DECIDER_IMPOSSIBILITY_CONTRACT.
Proof.
  exact closure_decider_impossible_lemma.
Qed.

Theorem certified_aporetic_lemma_contract :
  APORETIC_LEMMA_CONTRACT.
Proof.
  repeat split.
  - exact certified_aporetic_local_branch_collapse_contract.
  - exact certified_aporetic_core_diagonal_obstruction_contract.
  - exact certified_aporetic_eval_bottom_negfixp_contract.
  - exact certified_aporetic_eval_full_to_eval_bottom_contract.
  - exact certified_aporetic_full_frame_obstruction_corollary_contract.
  - exact certified_aporetic_fixed_point_contract.
  - exact certified_aporetic_excluded_middle_collapse_contract.
  - exact certified_aporetic_excluded_middle_obstruction_contract.
  - exact certified_aporetic_decision_collapse_contract.
  - exact certified_aporetic_decision_obstruction_contract.
  - exact certified_aporetic_equivalence_ad_absurdum_impossibility_contract.
  - exact certified_aporetic_decider_impossibility_contract.
Qed.

Theorem aporetic_lemma_qed :
  WITNESS.
Proof.
  exact certified_aporetic_lemma_contract.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         ASSUMPTION REPORT ARTIFACTS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Terminal endpoints only. The lemma contract is the
│          conjunction of all subordinate contract endpoints; the
│          named witness is the public entry point. Intermediate
│          `certified_aporetic_*_contract` reports inherit their
│          assumption profile from the conjunction.
│
*)

Redirect "theories/L001/_appendix/_assumptions/certified_aporetic_lemma_contract"
  Print Assumptions certified_aporetic_lemma_contract.

Redirect "theories/L001/_appendix/_assumptions/aporetic_lemma_qed"
  Print Assumptions aporetic_lemma_qed.
