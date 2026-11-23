(*L003_97_Artifacts.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / L003_97_Artifacts                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Certification and extraction boundary for L003. Certifies the theorem core
  and the full contract, redirects their assumption reports, and extracts the
  executable layer: quotation and grading, reindexing, the brute-force
  evaluators and certifiers, truth-table classification, circuit-verifier
  recognition, specialization, and Tseitin conversion.

*)

From Stdlib Require Import Extraction.

From L003 Require Export L003_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             CERTIFIED CONTRACTS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Theorem certified_no_internal_classifier_contract :
  NO_INTERNAL_CLASSIFIER_CONTRACT.
Proof.
  split; [exact no_internal_total_classifier |].
  split; [exact closed_level_has_no_internal_evaluator |].
  exact diagonal_closed_level_empty.
Qed.

Theorem certified_coding_free_identity_contract :
  CODING_FREE_IDENTITY_CONTRACT.
Proof.
  split; [exact coding_free_identity |].
  split; [exact size_free_coding_free_identity |].
  exact concrete_coding_free_identity.
Qed.

Theorem certified_self_application_contract :
  SELF_APPLICATION_CONTRACT.
Proof.
  intros C v.
  split; [exact (self_application C v) | exact (certification_fixed_point C v)].
Qed.

Theorem certified_certification_dichotomy_contract :
  CERTIFICATION_DICHOTOMY_CONTRACT.
Proof.
  split.
  - intros C v.
    split.
    + exact (certification_dichotomy C v).
    + exact (certification_dichotomy_exclusive C v).
  - split; [exact decidable_certification_dichotomy |].
    exact boolean_semantics_decidable.
Qed.

Theorem certified_faithful_invariance_contract :
  FAITHFUL_INVARIANCE_CONTRACT.
Proof.
  intros C D I v.
  destruct (faithful_interpretation_invariance C D I v) as [Hs [Hc Hn]].
  split; [exact Hs |].
  split; [exact Hc |].
  split; [exact Hn |].
  intros HdecC HdecD.
  split; [exact (faithful_acceptance_invariance C D I v HdecC HdecD) |].
  exact (faithful_branch_invariance C D I v HdecC HdecD).
Qed.

Theorem certified_dichotomy_sharpness_contract :
  DICHOTOMY_SHARPNESS_CONTRACT.
Proof.
  split; [exact dichotomy_sharpness | exact sharpness_schema].
Qed.

Theorem certified_settled_one_level_up_contract :
  SETTLED_ONE_LEVEL_UP_CONTRACT.
Proof.
  split; [exact exact_diagonal_level |].
  split; [exact evaluator_settles_diagonal | exact settler_above_verifier].
Qed.

Theorem certified_pointwise_incompleteness_contract :
  POINTWISE_INCOMPLETENESS_CONTRACT.
Proof.
  intros R v.
  split.
  - exact (pointwise_incompleteness R v).
  - exact (not_sound_and_complete_at_diagonal R v).
Qed.

Theorem certified_size_free_invariance_contract :
  SIZE_FREE_INVARIANCE_CONTRACT.
Proof.
  intros R T I v.
  destruct (size_free_interpretation_invariance R T I v) as [Hs [Hc Hn]].
  split; [exact Hs |].
  split; [exact Hc |].
  split; [exact Hn |].
  intros HdecR HdecT.
  split; [exact (size_free_acceptance_invariance R T I v HdecR HdecT) |].
  exact (size_free_branch_invariance R T I v HdecR HdecT).
Qed.

Theorem certified_one_semantics_contract :
  ONE_SEMANTICS_CONTRACT.
Proof.
  split; [exact forget_levels_diagonal | exact trivial_grading_diagonal].
Qed.

Theorem certified_concrete_grading_contract :
  CONCRETE_GRADING_CONTRACT.
Proof.
  split; [exact serialize_unique |].
  split; [exact term_level_tag |].
  split; [exact concrete_exact_costs |].
  split; [exact diagonal_term_level |].
  split; [exact concrete_diagonal_closed_level_empty |].
  split; [exact concrete_closed_level_vacuous |].
  exact term_size_level.
Qed.

Theorem certified_brute_force_evaluation_contract :
  BRUTE_FORCE_EVALUATION_CONTRACT.
Proof.
  intro O.
  split; [exact (brute_force_is_ascent O) |].
  split; [exact brute_force_growth |].
  split; [exact concrete_certifier_level |].
  exact (concrete_certification_family O).
Qed.

Theorem certified_concrete_hierarchy_contract :
  CONCRETE_HIERARCHY_CONTRACT.
Proof.
  split; [exact concrete_ascent_hierarchy |].
  split; [exact concrete_hierarchy_growth | exact concrete_proliferation].
Qed.

Theorem certified_minimal_branches_contract :
  MINIMAL_BRANCHES_CONTRACT.
Proof.
  intro O.
  split.
  - exact (accept_all_realizes_first_branch O).
  - exact (accept_none_realizes_second_branch O).
Qed.

Theorem certified_coding_sensitivity_contract :
  CODING_SENSITIVITY_CONTRACT.
Proof.
  split; [exact dichotomy_any_quotation |].
  split; [exact term_code_injective |].
  split; [exact neg_code_injective |].
  split; [exact branch_depends_on_quotation | exact recoding_not_faithful].
Qed.

Theorem certified_tseitin_contract :
  TSEITIN_CONTRACT.
Proof.
  split; [exact tseitin_correct | exact clause_level_specialization].
Qed.

Theorem certified_evaluator_lower_bound_contract :
  EVALUATOR_LOWER_BOUND_CONTRACT.
Proof.
  split; [exact reads_ext |].
  split; [exact reads_cost |].
  split; [exact evaluator_reads |].
  split; [exact evaluator_quadratic_lower_bound |].
  exact brute_force_between_bounds.
Qed.

Theorem certified_relativized_sat_contract :
  RELATIVIZED_SAT_CONTRACT.
Proof.
  split; [exact oclassify_correct |].
  split; [exact circuit_verifier_oracle_circuit |].
  split; [exact oclassify_embed |].
  split; [exact relativized_agrees_on_circuits |].
  split; [exact relativized_specialization |].
  intros ob v Hcircuit.
  split.
  - exact (proj1 (proj2 (proj2 (proj2 (relativized_solvers_paradox ob v Hcircuit))))).
  - exact (relativized_universality_obstruction ob v Hcircuit).
Qed.

(*
│
│          Primary certified endpoint for the L003 theorem core.
│
*)

Theorem l003_core_qed :
  L003_CORE_CONTRACT.
Proof.
  split; [exact certified_coding_free_identity_contract |].
  split; [exact certified_certification_dichotomy_contract |].
  split; [exact size_free_fixed_point |].
  split; [exact certified_brute_force_evaluation_contract |].
  exact solvers_paradox_plain_sat.
Qed.

(*
│
│          Certified endpoint for every L003 contract, in proof order.
│
*)

Theorem l003_contract_qed :
  L003_CONTRACT.
Proof.
  split; [exact lawvere_fixed_point |].
  split; [exact no_point_surjection_to_bool |].
  split; [exact diagonal_escape |].
  split; [exact evaluator_ascent |].
  split; [exact certified_no_internal_classifier_contract |].
  split; [exact certification_ascent |].
  split; [exact certified_coding_free_identity_contract |].
  split; [exact certified_self_application_contract |].
  split; [exact certified_certification_dichotomy_contract |].
  split; [exact certified_dichotomy_sharpness_contract |].
  split; [exact certified_faithful_invariance_contract |].
  split; [exact size_free_fixed_point |].
  split; [exact certified_pointwise_incompleteness_contract |].
  split; [exact constructive_boundary |].
  split; [exact internal_truth_obstruction |].
  split; [exact certified_size_free_invariance_contract |].
  split; [exact certified_one_semantics_contract |].
  split; [split; [exact impredicative_closure_impossible
                 | exact correct_certifier_is_predicative] |].
  split; [exact certified_settled_one_level_up_contract |].
  split; [exact ascent_hierarchy |].
  split; [exact ascent_hierarchy_bounds |].
  split; [exact proliferation |].
  split; [exact loeb |].
  split; [exact goedel_second |].
  split; [split; [exact language_fixed_point
                 | exact consistent_certifies_neither] |].
  split; [split; [exact internal_premises_satisfiable
                 | exact language_premises_satisfiable] |].
  split; [exact certified_concrete_grading_contract |].
  split; [exact certified_brute_force_evaluation_contract |].
  split; [exact certified_concrete_hierarchy_contract |].
  split; [exact relativization |].
  split; [exact classify_correct |].
  split; [exact specialization |].
  split; [exact solvers_paradox_plain_sat |].
  split; [exact certified_minimal_branches_contract |].
  split; [exact certified_tseitin_contract |].
  split; [exact certified_coding_sensitivity_contract |].
  split; [exact certified_evaluator_lower_bound_contract |].
  exact certified_relativized_sat_contract.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              ASSUMPTION REPORTS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Redirect "theories/L003/_appendix/_assumptions/l003_core_qed"
  Print Assumptions l003_core_qed.

Redirect "theories/L003/_appendix/_assumptions/l003_contract_qed"
  Print Assumptions l003_contract_qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               OCAML EXTRACTION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Extraction starts only from computational roots.
│          `term_sem`, oracles, `Satisfiable`, `CNFSatisfiable`, and
│          `ConcreteAccepted` are propositions and are not extracted.
│
*)

Extraction Language OCaml.

Extraction "theories/L003/_appendix/_artifacts/L003_Plain_SAT"
  classify
  truth_table
  formula_eval
  formula_size
  circuit_verifierb
  term_size
  diagonal_term
  term_serialize
  term_code
  term_level
  stream_pair
  reindex
  match_bits
  terms_upto
  brute_force
  concrete_certifier
  specialize_term
  claim_assignment
  specialized_formula
  tseitin
  cnf_eval
  neg_code
  reads
  oclassify
  oracle_specialized_formula
  embed_formula.
