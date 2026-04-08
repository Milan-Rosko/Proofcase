(*

  Proofcase / T003 / Effectivity Checks
  =====================================

    Overview
    --------

      We record executable sanity checks for the pinned bounded universal
      cubic artifact. The computations in this file show that the
      assembled polynomial can be evaluated concretely inside Rocq.
*)

From Coq Require Import ZArith List Bool Arith.
Import ListNotations.
Open Scope Z_scope.

From T003 Require Import R01__Coeff_types R02__Coefficients R03__Degree R04__Universal.

Definition zero_env : env := fun _ => 0%Z.

Example test_eval_zero_env_computable :
  exists z, eval_poly_table zero_env = z.
Proof.
  vm_compute.
  eexists; reflexivity.
Qed.

Example test_eval_deterministic :
  forall rho, eval_poly_table rho = eval_poly_table rho.
Proof.
  intro rho.
  reflexivity.
Qed.

Example test_eval_small_env :
  let rho :=
    fun i =>
      match i with
      | 0%nat => 1%Z
      | _ => 0%Z
      end in
  exists z, eval_poly_table rho = z.
Proof.
  vm_compute.
  eexists; reflexivity.
Qed.

(*
  Structural invariants
*)

Fixpoint var_index_okb (xs : list (nat * nat)) : bool :=
  match xs with
  | [] => true
  | (v, _) :: xs' => Nat.ltb v var_count && var_index_okb xs'
  end.

Definition monom_index_okb (m : monom) : bool :=
  var_index_okb m.(exps).

Fixpoint poly_index_okb (p : list monom) : bool :=
  match p with
  | [] => true
  | m :: p' => monom_index_okb m && poly_index_okb p'
  end.

Example test_all_indices_bounded :
  poly_index_okb poly = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Fixpoint coeffs_nonzero (p : list monom) : bool :=
  match p with
  | [] => true
  | m :: p' => negb (Z.eqb m.(coeff) 0%Z) && coeffs_nonzero p'
  end.

Example test_no_zero_monomials :
  coeffs_nonzero poly = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition poly_nonempty : bool :=
  match poly with
  | [] => false
  | _ :: _ => true
  end.

Example test_poly_nonempty :
  poly_nonempty = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example test_degree_at_most_3 :
  (max_degree <= 3)%nat.
Proof.
  exact degree_at_most_3.
Qed.

Example test_max_degree_eq_3 :
  max_degree = 3%nat.
Proof.
  exact max_degree_eq_3.
Qed.

Example test_has_degree_3_true :
  has_degree_3 = true.
Proof.
  exact has_degree_3_true.
Qed.

(*
  Assumption audit for the concrete effectivity tests.
*)
