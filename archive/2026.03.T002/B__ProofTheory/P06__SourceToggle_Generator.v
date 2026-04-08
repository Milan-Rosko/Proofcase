(*

  Proofcase / T002 / Source Toggle Generator
  ==========================================

    Overview
    --------

      We develop the Source Toggle Generator layer used by the T002 proof-
      theory route. This file packages the definitions and lemmas exported
      to later modules in the same route.
*)

From T002 Require Import P00__Provability_Interface.
From T002 Require Import P05__Toggle_Contradiction.

Theorem source_toggle_code_generator_internal :
  SourceToggleCodeGenerator.
Proof.
  intro e.
  destruct (source_toggle_point_exists e) as [u Hu].
  exists u.
  unfold SourceTogglePointCode.
  rewrite Prov_iff_Thm.
  exact Hu.
Qed.
