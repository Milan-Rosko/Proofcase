(*

  Proofcase / T003 / Variable Map
  ===============================

    Overview
    --------

      We expose the public variable map for the pinned bounded cubic
      artifact. This file names the distinguished coordinates used by the
      universal interface and proves the corresponding index bounds.
*)

From Coq Require Import ZArith List String Lia Arith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

From T003 Require Import R01__Coeff_types.

Definition ix_u : nat := 18711.
Definition var_u : string := "trace_code".
Lemma ix_u_lt_var_count : (ix_u < var_count)%nat.
Proof.
  apply Nat.ltb_lt.
  vm_compute.
  reflexivity.
Qed.

Definition public_var_indices : list (string * nat) := [("u", ix_u)].
