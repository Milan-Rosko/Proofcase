(*

  Proofcase / T002 / Reduction Core
  =================================

    Overview
    --------

      We develop the Reduction Core layer used by the T002 sigma-reduction
      route. This file packages the definitions and lemmas exported to
      later modules in the same route.
*)

From Coq Require Import List.
Import ListNotations.

From T002 Require Import R13__Kernel_API.

Definition CubicSatObj := CubicWitness.

Theorem check_iff_cubic_sat_obj :
  forall pf target,
    cubic_accepts pf target = true <-> CubicSatObj pf target.
Proof.
  intros pf target.
  exact (cubic_accepts_iff_cubic_witness pf target).
Qed.

Definition cubic_constraint_degree_le_3 := kernel_constraint_degree_le_3.

Definition cubic_system_degree_le_3 := kernel_system_degree_le_3.
