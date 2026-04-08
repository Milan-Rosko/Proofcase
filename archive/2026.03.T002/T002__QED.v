(* T002__QED.v *)

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│     ________________________  _________________                         │
│     ___________________  __ \ ___  ____/__  __ \                        │
│     __________________  / / / __  __/  __  / / /                        │
│     _________________/ /_/ /___  /______  /_/ /__                       │
│     _________________\___\_\(_)_____/(_)_____/_(_)                      │
│                                                                         │
│                                                                         │
│     This file states an exact public target, the Rocq-side criteria     │
│     required  by  the reductions, certifies each endpoint by direct     │
│     reuse, and exposes the key assumption reports.                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
  Proofcase / T002 / Certification Layer
  ======================================

  TIER 1 -- CERTIFIED COMPILATION  (Definitions, then claim)

  Step 1.  FORMULAS AND PROOFS.
           `Form` is the Hilbert formula type (generated from `Bot` and `Imp`),
           and `Proof` is a finite list of formulas.  The executable checker
           `check pf target` verifies that each line is an axiom instance
           (K/S/EFQ) or follows by modus ponens from earlier lines, and that
           the last line equals `target`.

  Step 2.  POLYNOMIAL COMPILATION.
           Each concrete pair `(pf, target)` is compiled to a finite polynomial
           system whose members have total degree at most 3, then aggregated to
           one cubic equation
           `(L, R) := emit_single_cubic pf target`
           with `total_degree L <= 3` and `total_degree R <= 3`.

  Step 3.  CUBIC SATISFIABILITY (Diophantine predicate).
           An `Assignment` stores a proof trace, a target formula, and
           auxiliary naturals.  `CubicWitness pf target` means:
           there exists `a` such that
           `as_pf a = pf`, `as_target a = target`, and
           `equation_holds (emit_single_cubic pf target) a`,
           i.e. the single cubic equation has a natural-number solution.

  Step 4.  CODING AND SOURCE/TARGET PREDICATES.
           Formula and proof data are coded by carryless Zeckendorf pairing.
           The concrete instance code is
           `code_of_concrete pf target = pair P0 (code_pf pf) (enc_form_nat target)`.
           Source predicate:
             `Thm u := exists pf target,
                         u = code_of_concrete pf target /\
                         check pf target = true.`
           Target predicate:
             `CubicSat n := exists pf target,
                              n = code_of_concrete pf target /\
                              CubicWitness pf target.`

  Step 5.  THE REDUCTION.
           The compiler map is `f u := u` (identity), so the same code indexes
           both source and target instances.  Tier-1 endpoint:
             `forall u, Thm u <-> CubicSat (f u)`.
           Equivalently, `many_one Thm CubicSat` with witness `f`, and
           `primitive_recursive f`.

  TIER 2 -- UNDECIDABILITY  (Definitions, then claim)

  Step 1.  CODED DECIDERS.
           `DeciderCode` is `nat`.  Execution is `EvalRM e input b`, and
           `TotalRM e` states totality (here, always true by construction).

  Step 2.  CORRECTNESS.
           `CorrectCode e := TotalRM e /\
                             forall s, EvalRM e s true <-> CubicSat s`.
           So a correct code decides cubic satisfiability on all inputs.

  Step 3.  TOGGLE FIXED POINT.
           For every code `e`, recursion-theorem machinery yields `q` with
             `forall input b, EvalRM q input b <-> EvalRM e q (negb b)`.
           At the source level:
             `exists u, Thm u <-> EvalRM e (f u) false`.

  Step 4.  CONTRADICTION.
           Transporting this source toggle through Tier 1 yields a cubic
           toggle witness; determinism/totality of coded evaluation then
           contradict `CorrectCode e`.

  Step 5.  ENDPOINT.
           `~ exists e : DeciderCode, CorrectCode e`.
           Corollaries:
             `~ exists D : Decider, Computable D /\ Correct D`
             and `~ DecidableCode CubicSat`.

  TIER 3 -- CERTIFICATION COROLLARY

  Step 1.  Let `RA_Certified_DeciderCode : DeciderCode -> Prop` and assume
           `RA_certified_sound : forall e,
             RA_Certified_DeciderCode e -> CorrectCode e`.

  Step 2.  Then `~ exists e, RA_Certified_DeciderCode e`, by immediate appeal
           to the Tier-2 endpoint.
*)

From Coq Require Import Bool List PeanoNat.
Import ListNotations.

From T002 Require Import
  R18__Sigma_Reduction_API
  P00__Provability_Interface
  P03__Undecidability
  P04__RA_Certification.

(*************************************************************************)
(*                                                                       *)
(*                              PROPOSITIO                               *)
(*                                                                       *)
(*************************************************************************)

Definition PROPOSITIO : Prop :=
  (* Tier 1: Certified compilation *)
  (forall u, Thm u <-> CubicSat (f u)) /\
  many_one Thm CubicSat /\
  primitive_recursive f /\
  (* Tier 2: Undecidability *)
  (~ exists e : DeciderCode, CorrectCode e) /\
  (~ exists D : Decider, Computable D /\ Correct D) /\
  (~ DecidableCode CubicSat).

(*************************************************************************)
(*                                                                       *)
(*                                Q.E.D.                                 *)
(*                                                                       *)
(*************************************************************************)

Theorem sigma_reduction_QED :
  forall u, Thm u <-> CubicSat (f u).
Proof.
  exact sigma_reduction.
Qed.

Theorem thm_reduces_to_cubic_QED :
  many_one Thm CubicSat.
Proof.
  exact thm_reduces_to_cubic.
Qed.

Theorem compiler_primitive_QED :
  primitive_recursive f.
Proof.
  exact compiler_primitive.
Qed.

Theorem no_total_correct_code_CubicSat_QED :
  ~ exists e : DeciderCode, CorrectCode e.
Proof.
  exact no_total_correct_code_CubicSat.
Qed.

Theorem no_total_correct_decider_computable_QED :
  ~ exists D : Decider, Computable D /\ Correct D.
Proof.
  exact no_total_correct_decider_CubicSat_computable.
Qed.

Theorem CubicSat_undecidable_code_QED :
  ~ DecidableCode CubicSat.
Proof.
  exact CubicSat_undecidable_code.
Qed.

Section Tier3.

Variable RA_Certified_DeciderCode : DeciderCode -> Prop.
Hypothesis RA_certified_sound :
  forall e, RA_Certified_DeciderCode e -> CorrectCode e.

Theorem no_RA_certified_decider_code_QED :
  ~ exists e : DeciderCode, RA_Certified_DeciderCode e.
Proof.
  exact (no_RA_certified_decider_code _ RA_certified_sound).
Qed.

End Tier3.

(*************************************************************************)
(*                                                                       *)
(*                         KEY ASSUMPTION REPORT                         *)
(*                                                                       *)
(*************************************************************************)

Theorem cubic_diophantine_reduction_QED : PROPOSITIO.
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - exact sigma_reduction.
  - exact thm_reduces_to_cubic.
  - exact compiler_primitive.
  - exact no_total_correct_code_CubicSat.
  - exact no_total_correct_decider_CubicSat_computable.
  - exact CubicSat_undecidable_code.
Qed.

Print Assumptions sigma_reduction_QED.
Print Assumptions thm_reduces_to_cubic_QED.
Print Assumptions compiler_primitive_QED.
Print Assumptions no_total_correct_code_CubicSat_QED.
Print Assumptions no_total_correct_decider_computable_QED.
Print Assumptions CubicSat_undecidable_code_QED.
Print Assumptions cubic_diophantine_reduction_QED.

Redirect "theories/T002/appendix/assumptions/cubic_diophantine_reduction_QED"
  Print Assumptions cubic_diophantine_reduction_QED.
Redirect "theories/T002/appendix/assumptions/sigma_reduction_QED"
  Print Assumptions sigma_reduction_QED.
Redirect "theories/T002/appendix/assumptions/no_total_correct_code_CubicSat_QED"
  Print Assumptions no_total_correct_code_CubicSat_QED.
