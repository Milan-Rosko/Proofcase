(* T004__QED.v *)

From Coq Require Import Bool List ZArith.
Import ListNotations.

From T004 Require Import
  R01__Cellular_Semantics
  R02__Progenitor_Obstruction
  R03__Faithfulness
  R04__Transversality
  R06__No_Tamper_Checker
  R07__Corollary.

(*************************************************************************)
(*                                                                       *)
(*    Proofcase / T004 -- QED Surface                                    *)
(*                                                                       *)
(*    This file states the exact public targets of T004, certifies       *)
(*    them by direct reuse of the internal endpoints, and records the    *)
(*    resulting assumption reports.                                      *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*                              PROPOSITIO                               *)
(*                                                                       *)
(*************************************************************************)

Definition PROPOSITIO_EX_NIHILO : Prop :=
  forall u,
    ~ Progenitor u seed_row.

Definition PROPOSITIO_FAITHFUL_APERIODICITY : Prop :=
  ~ eventually_periodic_center_strip.

Definition PROPOSITIO_TRANSVERSAL_APERIODICITY : Prop :=
  ~ eventually_periodic_center_strip.

Definition PROPOSITIO_NO_TAMPER_CHECKER : Prop :=
  forall R T Theta,
    ~ tamper_checker_at R T Theta.

Definition PROPOSITIO_NO_OBSERVATION_ONLY_TAMPER_CHECKER : Prop :=
  COROLLARIUM_NO_OBSERVATION_ONLY_TAMPER_CHECKER.

(*************************************************************************)
(*                                                                       *)
(*                                Q.E.D.                                 *)
(*                                                                       *)
(*************************************************************************)

Theorem ex_nihilo_QED : PROPOSITIO_EX_NIHILO.
Proof.
  exact No_Progenitor_Theorem.
Qed.

Theorem faithful_aperiodicity_QED : PROPOSITIO_FAITHFUL_APERIODICITY.
Proof.
  exact Faithful_Aperiodicity_Theorem.
Qed.

Theorem transversal_aperiodicity_QED :
  PROPOSITIO_TRANSVERSAL_APERIODICITY.
Proof.
  exact Transversal_Aperiodicity_Theorem.
Qed.

Theorem no_tamper_checker_QED :
  PROPOSITIO_NO_TAMPER_CHECKER.
Proof.
  exact No_Tamper_Checker.
Qed.

Theorem no_observation_only_tamper_checker_QED :
  PROPOSITIO_NO_OBSERVATION_ONLY_TAMPER_CHECKER.
Proof.
  exact no_observation_only_tamper_checker.
Qed.

(*************************************************************************)
(*                                                                       *)
(*                       EXTRACTION SURFACE OMITTED                      *)
(*                                                                       *)
(*  No OCaml extraction interface is exposed at the QED layer of T004.  *)
(*  This package is foundational: its role is to certify semantic       *)
(*  endpoints and their assumption profiles, not to present an          *)
(*  executable extraction surface.                                      *)
(*                                                                       *)
(*************************************************************************)

Redirect "theories/T004/appendix/assumptions/ex_nihilo_QED"
  Print Assumptions ex_nihilo_QED.

Redirect "theories/T004/appendix/assumptions/faithful_aperiodicity_QED"
  Print Assumptions faithful_aperiodicity_QED.

Redirect "theories/T004/appendix/assumptions/transversal_aperiodicity_QED"
  Print Assumptions transversal_aperiodicity_QED.

Redirect "theories/T004/appendix/assumptions/no_tamper_checker_QED"
  Print Assumptions no_tamper_checker_QED.

Redirect
  "theories/T004/appendix/assumptions/no_observation_only_tamper_checker_QED"
  Print Assumptions no_observation_only_tamper_checker_QED.
