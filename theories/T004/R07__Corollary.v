(* R07__Corollary.v *)

From T004 Require Import
  R06__No_Tamper_Checker.

(*************************************************************************)
(*                                                                       *)
(*    Proofcase / T004 -- Corollary Layer                                *)
(*                                                                       *)
(*    This file records a foundational corollary of the constructive     *)
(*    tamper-checker obstruction: no observation-only Boolean test can   *)
(*    distinguish the canonical carrier from non-canonical reverse       *)
(*    carriers that induce the same centered observation.                *)
(*                                                                       *)
(*************************************************************************)

Definition COROLLARIUM_NO_OBSERVATION_ONLY_TAMPER_CHECKER : Prop :=
  forall R T Theta,
    ~ tamper_checker_at R T Theta.

Corollary no_observation_only_tamper_checker :
  COROLLARIUM_NO_OBSERVATION_ONLY_TAMPER_CHECKER.
Proof.
  exact No_Tamper_Checker.
Qed.
