(* T004__Comprehension.v *)

From Coq Require Import Bool List ZArith.
Import ListNotations.

From T004 Require Import
  R01__Cellular_Semantics
  R02__Progenitor_Obstruction
  R03__Faithfulness
  R04__Transversality
  R05__Bounds
  R06__No_Tamper_Checker
  R07__Corollary.

(*************************************************************************)
(*                                                                       *)
(*    Proofcase / T004 -- Comprehension Layer                            *)
(*                                                                       *)
(*    This file serves as a proof-semantic synopsis and comprehension    *)
(*    aid for project T004. It introduces no new constructive content    *)
(*    or derivations; but consolidates the semantic base, constructive   *)
(*    obstructions, conditional routes, bounded audit surfaces, and      *)
(*    corollary-level public packaging into a unified structure for      *)
(*    readability, qualification, and review.                            *)
(*                                                                       *)
(*************************************************************************)

Section Proof_Index.

(*

Proofcase / T004 / Comprehension
================================

  Overview
  --------

  `T004` develops a constructive aperiodicity package for the seeded
  Rule30 orbit. In its present form, the package contains two closed
  constructive obstruction layers (`R02` and `R06`), two independent
  conditional routes to center-strip aperiodicity (`R03` and `R04`),
  one purely computational audit layer (`R05`), and one thin public
  corollary layer (`R07`).

  Local Semantics vs Global Property
  ----------------------------------

  The central difficulty is structural rather than technical. One
  attempts to establish nonperiodicity, which is a global property,
  using a framework whose primitives are entirely local.

  The evolution rule of Rule 30 is radius-1 and therefore intrinsically
  local. All constructive arguments operate on bounded windows, finite
  cones, and finitely supported rows.

  However, periodicity is not a local predicate. It is a statement
  about infinite temporal coherence. The mismatch is therefore not
  accidental: it is a categorical misalignment between the object of
  proof and the tools permitted.

  The repeated failure of local arguments is not evidence of weakness
  in technique, but of insufficiency in the semantic framework.

  The Methodological Constraint
  ----------------------------

  The insistence on finitistic, local reasoning for Rule 30 is a
  methodological constraint, not a logical necessity.

  In other domains, most notably real analysis, one freely extends the
  underlying system in order to make global properties accessible.
  Limits, completions, and equivalence classes are accepted as
  legitimate constructions.

  In contrast, Rule 30 is typically studied as a bare operational
  process, without an agreed-upon semantic completion. This forces all
  reasoning to remain within finite observation and local propagation,
  even when the target property lies outside that regime.

  The difficulty is therefore not that the system is opaque, but that
  it is being interrogated under artificially restricted semantics.

  Semantic Asymmetry with the Reals
  ---------------------------------

  There is a clear asymmetry between how numbers and cellular automata
  are treated.

  For the real numbers, one accepts non-finitary constructions such as
  Cauchy completion or Dedekind cuts. These constructions are not
  derived from finite observation; they are imposed to stabilize
  infinite behavior.

  For Rule 30, no analogous completion is standard. One observes finite
  windows and attempts to infer global behavior directly.

  This creates a double standard: non-constructive semantic anchors are
  accepted in one domain but withheld in another. The resulting gap
  manifests precisely at statements such as eventual periodicity, which
  require stability across arbitrarily large scales.

  (i) CELLULAR SEMANTICS DEFINITION LAYER

      `R01` fixes the ambient objects: Boolean cells, bi-infinite rows,
      the local Rule30 update rule, iterated evolution from the single
      seed, centered windows, the center strip, and the eventual-period
      predicates used later.

  (ii) CELLULAR SEMANTICS BRIDGE LAYER

      Still in `R01`, the development proves the structural lemmas that
      let finite observations control rows: pointwise recovery from a
      centered window, radius-zero identification of the center strip,
      finite-support propagation, and the key fact that the canonical
      seeded orbit never repeats at any positive lag.

  (iii) PROGENITOR OBSTRUCTION LAYER

      `R02` proves the closed contradiction core. No finitely supported
      row can evolve in one Rule30 step to the single-seed row. The same
      argument also rules out support-covering replay of sufficiently
      wide centered windows.

  (iv) FAITHFULNESS LIFT LAYER

      `R03` isolates one external premise,
      `Faithfulness_Hypothesis`: if a periodic tail is observed at
      radius `R`, then the same tail persists at radius `S R`. Iterating
      this lift yields a uniform family of periodic tails, which
      contradicts the non-repetition result already proved in `R01`.

  (v) TRANSVERSAL OBSTRUCTION LAYER

      `R04` develops an independent arithmetic route. The centered
      observable is linked to concrete right diagonals of the seeded
      orbit, while the single external bridge premise says that any
      eventual center period must be divisible by every power-of-two
      diagonal period. Since powers of two are unbounded, a positive
      eventual period cannot satisfy all those divisibility constraints.

  (vi) BOUNDED AUDIT LAYER

      `R05` is computational only. It packages executable bounded tests
      for periodic tails, radius-survival scans, search-box counts, and
      stable-period summaries for extraction-side audit work. No theorem
      in the core proof path depends on this layer.

  (vii) OBSERVATION-ONLY TAMPER OBSTRUCTION LAYER

      `R06` is fully constructive and unconditional. It reconstructs
      reverse carriers from a visible observation by solving Rule30
      leftward, uses the two free right-boundary bits to build distinct
      carriers with the same observation, and concludes that no Boolean
      function of the observation alone can act as a tamper checker.

  (viii) COROLLARY LAYER

      `R07` packages the observation-only tamper obstruction as an
      explicit corollary surface, with no additional proof content and
      no additional conditions.
*)

(*************************************************************************)
(*                                                                       *)
(*                  CELLULAR SEMANTICS DEFINITION LAYER                  *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  CORE CELLULAR OBJECTS
*)

Definition audit_bit := bit.
Definition audit_row := row.
Definition audit_cellular_rule := cellular_rule.
Definition audit_Rule30 := Rule30.
Definition audit_step_of := step_of.
Definition audit_iterate_step := iterate_step.
Definition audit_seed_row := seed_row.
Definition audit_Rule30_row := Rule30_row.
Definition audit_canonical_row := canonical_row.

(*
  (ii)
  OBSERVABLE SURFACES AND PERIODICITY PREDICATES
*)

Definition audit_supported_in := supported_in.
Definition audit_finitely_supported := finitely_supported.
Definition audit_centered_window := centered_window.
Definition audit_centered_line := centered_line.
Definition audit_center_strip := center_strip.
Definition audit_eventually_periodic_center_strip :=
  eventually_periodic_center_strip.
Definition audit_eventually_periodic_centered_window :=
  eventually_periodic_centered_window.
Definition audit_eventually_periodic_full_rows :=
  eventually_periodic_full_rows.

(*************************************************************************)
(*                                                                       *)
(*                   CELLULAR SEMANTICS BRIDGE LAYER                     *)
(*                                                                       *)
(*************************************************************************)

(*
  (iii)
  LOCAL RULE REDUCTIONS AND CANONICAL EVOLUTION
*)

Definition audit_Rule30_00c := Rule30_00c.
Definition audit_Rule30_01c_true := Rule30_01c_true.
Definition audit_Rule30_quiescent := Rule30_quiescent.
Definition audit_canonical_row_seed_at_time_zero :=
  canonical_row_seed_at_time_zero.
Definition audit_canonical_row_step := canonical_row_step.

(*
  (iv)
  WINDOW-TO-ROW BRIDGES
*)

Definition audit_nth_error_centered_window :=
  nth_error_centered_window.
Definition audit_centered_window_eq_pointwise :=
  centered_window_eq_pointwise.
Definition audit_centered_window_radius_zero_is_center_strip :=
  centered_window_radius_zero_is_center_strip.
Definition audit_centered_line_radius_zero_period_iff_center_strip_period :=
  centered_line_radius_zero_period_iff_center_strip_period.

(*
  (v)
  FINITE-SUPPORT PROPAGATION AND NON-REPETITION
*)

Definition audit_seed_supported_in_0 := seed_supported_in_0.
Definition audit_supported_step := supported_step.
Definition audit_Rule30_supported := Rule30_supported.
Definition audit_left_edge_of_canonical_cone_is_active :=
  left_edge_of_canonical_cone_is_active.
Definition audit_canonical_rows_never_repeat_at_positive_lag :=
  canonical_rows_never_repeat_at_positive_lag.
Definition audit_uniform_tail_implies_full_row_periodicity :=
  uniform_tail_implies_full_row_periodicity.

(*
  Backward-compatible aliases exported by `R01`.
*)

Definition audit_local_rule := local_rule.
Definition audit_iter_row_of := iter_row_of.
Definition audit_seed := seed.
Definition audit_canonical_row_of := canonical_row_of.
Definition audit_canonical_center_strip := canonical_center_strip.
Definition audit_canonical_centered_line := canonical_centered_line.
Definition audit_Rule30_row_zero_eq_seed := Rule30_row_zero_eq_seed.
Definition audit_Rule30_row_successor := Rule30_row_successor.
Definition audit_canonical_centered_line_0_eq_center_strip :=
  canonical_centered_line_0_eq_center_strip.
Definition audit_canonical_centered_line0_period_iff_center_strip_period :=
  canonical_centered_line0_period_iff_center_strip_period.

(*************************************************************************)
(*                                                                       *)
(*                     PROGENITOR OBSTRUCTION LAYER                      *)
(*                                                                       *)
(*************************************************************************)

(*
  (vi)
  PROGENITOR VOCABULARY AND LOCAL CONTRADICTION CORE
*)

Definition audit_Progenitor := Progenitor.
Definition audit_boundary_forcing_on_seed_predecessor :=
  boundary_forcing_on_seed_predecessor.
Definition audit_local_contradiction_at_origin_and_adjacent_site :=
  local_contradiction_at_origin_and_adjacent_site.

(*
  (vii)
  CLOSED EX NIHILO ENDPOINTS
*)

Definition audit_No_Progenitor_Theorem := No_Progenitor_Theorem.
Definition audit_Ex_Nihilo_Obstruction := Ex_Nihilo_Obstruction.
Definition audit_no_progenitor_theorem := no_progenitor_theorem.
Definition audit_seed_not_created_from_finite_support :=
  seed_not_created_from_finite_support.
Definition audit_support_covering_centered_line_replay_impossible :=
  support_covering_centered_line_replay_impossible.
Definition audit_support_covering_centered_line_single_replay_at_zero_impossible :=
  support_covering_centered_line_single_replay_at_zero_impossible.

(*************************************************************************)
(*                                                                       *)
(*                      FAITHFULNESS LIFT LAYER                          *)
(*                                                                       *)
(*************************************************************************)

(*
  (viii)
  PERIODIC-TAIL VOCABULARY AND EXTERNAL PREMISE
*)

Definition audit_observational_periodic_tail :=
  observational_periodic_tail.
Definition audit_uniform_eventual_periodic_tail :=
  uniform_eventual_periodic_tail.
Definition audit_Faithfulness_Hypothesis :=
  Faithfulness_Hypothesis.

(*
  (ix)
  FAITHFULNESS LIFT AND CONDITIONAL APERIODICITY
*)

Definition audit_faithful_growth_iterates :=
  faithful_growth_iterates.
Definition audit_faithfulness_implies_uniform_tail_lift :=
  faithfulness_implies_uniform_tail_lift.
Definition audit_No_Uniform_Periodic_Tail_Witness :=
  No_Uniform_Periodic_Tail_Witness.
Definition audit_No_Observational_Periodic_Tail :=
  No_Observational_Periodic_Tail.
Definition audit_No_Eventual_Periodicity_Of_Centered_Windows :=
  No_Eventual_Periodicity_Of_Centered_Windows.
Definition audit_Faithful_Aperiodicity_Theorem :=
  Faithful_Aperiodicity_Theorem.

(*************************************************************************)
(*                                                                       *)
(*                    TRANSVERSAL OBSTRUCTION LAYER                      *)
(*                                                                       *)
(*************************************************************************)

(*
  (x)
  CONCRETE DIAGONAL VOCABULARY
*)

Definition audit_divides := divides.
Definition audit_right_diagonal := right_diagonal.
Definition audit_right_diagonal_center_link := right_diagonal_center_link.
Definition audit_right_period := right_period.
Definition audit_right_period_lower_bound := right_period_lower_bound.
Definition audit_right_period_unbounded := right_period_unbounded.

(*
  (xi)
  TRANSVERSAL BRIDGE AND ARITHMETIC CONTRADICTION CORE
*)

Definition audit_Transversal_Bridge := Transversal_Bridge.
Definition audit_divisor_cannot_exceed_dividend :=
  divisor_cannot_exceed_dividend.
Definition audit_Transversal_Aperiodicity_Theorem :=
  Transversal_Aperiodicity_Theorem.

(*************************************************************************)
(*                                                                       *)
(*                         BOUNDED AUDIT LAYER                           *)
(*                                                                       *)
(*************************************************************************)

(*
  (xii)
  BOOLEAN WINDOW COMPARISON AND BOUNDED TAIL TESTS
*)

Definition audit_list_bool_beq := list_bool_beq.
Definition audit_list_bool_beq_correct := list_bool_beq_correct.
Definition audit_forallb_range := forallb_range.
Definition audit_forallb_range_correct := forallb_range_correct.
Definition audit_bounded_observational_tailb :=
  bounded_observational_tailb.
Definition audit_bounded_observational_tailb_correct :=
  bounded_observational_tailb_correct.
Definition audit_survives_next_radiusb := survives_next_radiusb.
Definition audit_persistence_depth := persistence_depth.

(*
  (xiii)
  FINITE SEARCH-BOX COUNTS AND PERIOD SUMMARIES
*)

Definition audit_candidate_count_P := candidate_count_P.
Definition audit_candidate_count := candidate_count.
Definition audit_survival_count_P := survival_count_P.
Definition audit_survival_count := survival_count.
Definition audit_survival_rate_num := survival_rate_num.
Definition audit_survival_rate_den := survival_rate_den.
Definition audit_max_stable_period_P := max_stable_period_P.
Definition audit_max_stable_period_T := max_stable_period_T.
Definition audit_max_stable_period := max_stable_period.

(*
  (xiv)
  CONCRETE SCAN PARAMETER SURFACES
*)

Definition audit_scan_small_Rmax := scan_small_Rmax.
Definition audit_scan_small_Pmax := scan_small_Pmax.
Definition audit_scan_small_Tmax := scan_small_Tmax.
Definition audit_scan_small_Lmin_factor := scan_small_Lmin_factor.
Definition audit_scan_mid_Rmax := scan_mid_Rmax.
Definition audit_scan_mid_Pmax := scan_mid_Pmax.
Definition audit_scan_mid_Tmax := scan_mid_Tmax.
Definition audit_scan_mid_Lmin_factor := scan_mid_Lmin_factor.
Definition audit_scan_stress_Rmax := scan_stress_Rmax.
Definition audit_scan_stress_Pmax := scan_stress_Pmax.
Definition audit_scan_stress_Tmax := scan_stress_Tmax.
Definition audit_scan_stress_Lmin_factor := scan_stress_Lmin_factor.

(*************************************************************************)
(*                                                                       *)
(*              OBSERVATION-ONLY TAMPER OBSTRUCTION LAYER               *)
(*                                                                       *)
(*************************************************************************)

(*
  (xv)
  RULE 30 XOR STRUCTURE AND REVERSE-CARRIER RECONSTRUCTION
*)

Definition audit_Rule30_xorb_orb := Rule30_xorb_orb.
Definition audit_Rule30_left_inverse := Rule30_left_inverse.
Definition audit_reverse_carrier := reverse_carrier.
Definition audit_carrier_step := carrier_step.
Definition audit_carrier_val := carrier_val.
Definition audit_reconstructed_row := reconstructed_row.
Definition audit_carrier_val_0 := carrier_val_0.
Definition audit_carrier_val_1 := carrier_val_1.
Definition audit_carrier_val_step := carrier_val_step.
Definition audit_reconstructed_row_valid := reconstructed_row_valid.

(*
  (xvi)
  BOUNDARY INJECTIVITY AND NO-TAMPER IMPOSSIBILITY
*)

Definition audit_reconstructed_row_at_R := reconstructed_row_at_R.
Definition audit_reconstructed_row_at_Rplus1 := reconstructed_row_at_Rplus1.
Definition audit_boundary_injective := boundary_injective.
Definition audit_canonical_is_reverse_carrier := canonical_is_reverse_carrier.
Definition audit_alternative_carrier_exists := alternative_carrier_exists.
Definition audit_tamper_checker_at := tamper_checker_at.
Definition audit_No_Tamper_Checker := No_Tamper_Checker.

(*************************************************************************)
(*                                                                       *)
(*                         COROLLARY LAYER                               *)
(*                                                                       *)
(*************************************************************************)

Definition audit_COROLLARIUM_NO_OBSERVATION_ONLY_TAMPER_CHECKER :=
  COROLLARIUM_NO_OBSERVATION_ONLY_TAMPER_CHECKER.
Definition audit_no_observation_only_tamper_checker :=
  no_observation_only_tamper_checker.

(*************************************************************************)
(*                                                                       *)
(*                             PROOF SKETCH                              *)
(*                                                                       *)
(*    Step 1. `R01` fixes the canonical single-seed Rule30 orbit and     *)
(*            the observable surfaces that later arguments may inspect:  *)
(*            centered windows of arbitrary radius and the radius-zero   *)
(*            center strip.                                              *)
(*                                                                       *)
(*    Step 2. `R02` proves the closed ex nihilo obstruction. Any         *)
(*            finitely supported predecessor of `seed_row` would force   *)
(*            two adjacent local Rule30 evaluations to take mutually     *)
(*            incompatible values.                                       *)
(*                                                                       *)
(*    Step 3. `R03` assumes only `Faithfulness_Hypothesis`: an observed  *)
(*            periodic tail at radius `R` lifts to radius `S R` without  *)
(*            changing the same tail parameters `T` and `P`.             *)
(*                                                                       *)
(*    Step 4. Iterating that lift yields periodic agreement on every     *)
(*            radius extension of a fixed base window. The bridge lemma  *)
(*            `centered_window_eq_pointwise` then converts sufficiently  *)
(*            wide window equality into full-row equality.               *)
(*                                                                       *)
(*    Step 5. But `R01` already proves `canonical_rows_never_repeat_     *)
(*            at_positive_lag`: for every positive lag `P`, the seeded   *)
(*            orbit differs somewhere between times `T` and `T + P`.     *)
(*            Hence no uniform periodic tail can exist.                  *)
(*                                                                       *)
(*    Step 6. Therefore, under faithfulness, no observational periodic   *)
(*            tail exists at any radius; in particular the radius-zero   *)
(*            observable, the center strip, is not eventually periodic.  *)
(*                                                                       *)
(*    Step 7. Independently, `R04` studies the concrete right diagonals  *)
(*            of the canonical orbit and fixes their period profile to   *)
(*            be the powers of two.                                      *)
(*                                                                       *)
(*    Step 8. The unique external premise `Transversal_Bridge` says      *)
(*            that any eventual center period `P` must be divisible by   *)
(*            `2^k` for every diagonal index `k`. Choosing `k` so that   *)
(*            `2^k > P` contradicts the elementary fact that a divisor   *)
(*            of a positive natural cannot exceed it.                    *)
(*                                                                       *)
(*    Step 9. `R05` contributes no new proof-theoretic force; it merely  *)
(*            packages bounded executable scans for empirical audit and   *)
(*            extraction-side inspection.                                *)
(*                                                                       *)
(*    Step 10. `R06` returns to a closed constructive obstruction.      *)
(*             Rule30's XOR form lets one solve left inputs from an      *)
(*             observed output and chosen center/right inputs. Hence a   *)
(*             fixed observation admits multiple distinct reverse        *)
(*             carriers, so no observation-only Boolean checker can      *)
(*             distinguish the canonical carrier from all tampered       *)
(*             alternatives.                                             *)
(*                                                                       *)
(*    Step 11. `R07` repackages that same closed result as an explicit   *)
(*             corollary surface, still without any additional premise.  *)
(*                                                                       *)
(*                             MECHANIZATION                             *)
(*                                                                       *)
(*    CLOSED OBSTRUCTION CORE                                            *)
(*                                                                       *)
(*      forall u,                                                        *)
(*        ~ Progenitor u seed_row                                        *)
(*                                                                       *)
(*    CONDITIONAL FAITHFULNESS ROUTE                                     *)
(*                                                                       *)
(*      ~ eventually_periodic_center_strip                               *)
(*                                                                       *)
(*      with the unique additional premise                               *)
(*      `Faithfulness_Hypothesis`.                                       *)
(*                                                                       *)
(*    CONDITIONAL TRANSVERSAL ROUTE                                      *)
(*                                                                       *)
(*      ~ eventually_periodic_center_strip                               *)
(*                                                                       *)
(*      with the unique additional premise `Transversal_Bridge`.         *)
(*                                                                       *)
(*    CLOSED OBSERVATION-ONLY TAMPER OBSTRUCTION                         *)
(*                                                                       *)
(*      forall R T Theta,                                                *)
(*        ~ tamper_checker_at R T Theta                                  *)
(*                                                                       *)
(*    COROLLARY SURFACE                                                  *)
(*                                                                       *)
(*      forall R T Theta,                                                *)
(*        ~ tamper_checker_at R T Theta                                  *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    T004 should be read as a mixed package with two closed             *)
(*    constructive obstructions, two conditional aperiodicity routes,    *)
(*    one computational audit layer, and one corollary-level public      *)
(*    restatement. `R02` and `R06` are fully constructive. `R03` and     *)
(*    `R04` do not hide their extra premises; the assumptions are        *)
(*    named explicitly in the source and are later surfaced again by     *)
(*    the QED assumption reports. `R07` adds visibility, not proof       *)
(*    strength.                                                          *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    The public QED surface in `T004__QED.v` exposes five endpoints:    *)
(*    `ex_nihilo_QED`, `faithful_aperiodicity_QED`,                      *)
(*    `transversal_aperiodicity_QED`, `no_tamper_checker_QED`, and       *)
(*    `no_observation_only_tamper_checker_QED`. Their assumption         *)
(*    reports confirm the exact status of the package:                   *)
(*                                                                       *)
(*      (1) `ex_nihilo_QED` is closed under the global context;          *)
(*      (2) `faithful_aperiodicity_QED` depends on                      *)
(*          `Faithfulness_Hypothesis`; and                               *)
(*      (3) `transversal_aperiodicity_QED` depends on                    *)
(*          `Transversal_Bridge`; and                                    *)
(*      (4) `no_tamper_checker_QED` is closed under the global context;  *)
(*          and                                                          *)
(*      (5) `no_observation_only_tamper_checker_QED` is closed under     *)
(*          the global context.                                          *)
(*                                                                       *)
(*    The bounded layer `R05__Bounds` is computational only and does     *)
(*    not alter the logical qualification of these proof endpoints.      *)
(*                                                                       *)
(*************************************************************************)

End Proof_Index.
