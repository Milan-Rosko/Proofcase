(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This file starts Step A of the quartic roadmap by fixing a concrete constructive reduction from cubic families to quadratic families. The present phase sets up the transformation data and proves structural lemmas about fresh-variable allocation and family size.]]@*)

(*@doc.pl@[[No semantic equivalence claim is stated here yet beyond what is proved below. The goal of this pass is to make the reduction executable and its bookkeeping explicit before the bidirectional correctness theorem is added.]]@*)

(*@head.end@*)

From Stdlib Require Import Lia.

From P002 Require Export P002_11__Quadratic_Family.

Record aux_pair : Type := {
  aux_left : nat;
  aux_right : nat
}.

Definition cubic_monomial_count (m : monomial) : nat :=
  match m with
  | m_cubic _ _ _ => 1
  | _ => 0
  end.

Definition cubic_term_count (t : term) : nat :=
  cubic_monomial_count (mono t).

Fixpoint cubic_poly_count (ts : list term) : nat :=
  match ts with
  | [] => 0
  | t :: ts' => cubic_term_count t + cubic_poly_count ts'
  end.

Definition cubic_equation_count (eqn : h10_nd3n_equation) : nat :=
  cubic_poly_count (lhs_terms eqn) + cubic_poly_count (rhs_terms eqn).

Fixpoint cubic_family_count (Gamma : cubic_family_instance) : nat :=
  match Gamma with
  | [] => 0
  | eqn :: Gamma' => cubic_equation_count eqn + cubic_family_count Gamma'
  end.

Fixpoint family_var_bound (Gamma : cubic_family_instance) : nat :=
  match Gamma with
  | [] => 0
  | eqn :: Gamma' => Nat.max (var_count eqn) (family_var_bound Gamma')
  end.

Definition quadratic_target_var_count (Gamma : cubic_family_instance) : nat :=
  family_var_bound Gamma + cubic_family_count Gamma.

Definition linear_term2 (c i : nat) : term2 :=
  {| coeff2 := c; mono2 := m2_linear i |}.

Definition quadratic_term2 (c i j : nat) : term2 :=
  {| coeff2 := c; mono2 := m2_quadratic i j |}.

Definition const_term2 (c : nat) : term2 :=
  {| coeff2 := c; mono2 := m2_const |}.

Fixpoint reduce_terms_from
  (base offset : nat)
  (ts : list term)
  : list term2 * list aux_pair * nat :=
  match ts with
  | [] => ([], [], offset)
  | t :: ts' =>
      match mono t with
      | m_const =>
          let '(ts2, auxs, offset') := reduce_terms_from base offset ts' in
          (const_term2 (coeff t) :: ts2, auxs, offset')
      | m_linear i =>
          let '(ts2, auxs, offset') := reduce_terms_from base offset ts' in
          (linear_term2 (coeff t) i :: ts2, auxs, offset')
      | m_quadratic i j =>
          let '(ts2, auxs, offset') := reduce_terms_from base offset ts' in
          (quadratic_term2 (coeff t) i j :: ts2, auxs, offset')
      | m_cubic i j k =>
          let u := base + offset in
          let '(ts2, auxs, offset') := reduce_terms_from base (S offset) ts' in
          (quadratic_term2 (coeff t) u k :: ts2,
           {| aux_left := i; aux_right := j |} :: auxs,
           offset')
      end
  end.

Fixpoint aux_equations_from
  (target base offset : nat)
  (auxs : list aux_pair)
  : list h10_nd2n_equation :=
  match auxs with
  | [] => []
  | a :: auxs' =>
      {| var_count2 := target;
         lhs_terms2 := [linear_term2 1 (base + offset)];
         rhs_terms2 := [quadratic_term2 1 (aux_left a) (aux_right a)] |}
      :: aux_equations_from target base (S offset) auxs'
  end.

Definition host_equation2
  (target : nat)
  (lhs2 rhs2 : list term2) : h10_nd2n_equation :=
  {| var_count2 := target;
     lhs_terms2 := lhs2;
     rhs_terms2 := rhs2 |}.

Definition reduce_equation_from
  (target base offset : nat)
  (eqn : h10_nd3n_equation)
  : list h10_nd2n_equation * nat :=
  let '(lhs2, auxs_l, offset1) := reduce_terms_from base offset (lhs_terms eqn) in
  let '(rhs2, auxs_r, offset2) := reduce_terms_from base offset1 (rhs_terms eqn) in
  (host_equation2 target lhs2 rhs2
   :: aux_equations_from target base offset auxs_l
   ++ aux_equations_from target base offset1 auxs_r,
   offset2).

Fixpoint reduce_family_from
  (target base offset : nat)
  (Gamma : cubic_family_instance)
  : quadratic_family_instance * nat :=
  match Gamma with
  | [] => ([], offset)
  | eqn :: Gamma' =>
      let '(eqns2, offset1) := reduce_equation_from target base offset eqn in
      let '(Gamma2, offset2) := reduce_family_from target base offset1 Gamma' in
      (eqns2 ++ Gamma2, offset2)
  end.

Definition reduce_to_quadratic
  (Gamma : cubic_family_instance) : quadratic_family_instance :=
  let base := family_var_bound Gamma in
  let target := quadratic_target_var_count Gamma in
  fst (reduce_family_from target base 0 Gamma).

Lemma family_var_bound_nil :
  family_var_bound [] = 0.
Proof.
  reflexivity.
Qed.

Lemma family_var_bound_cons :
  forall eqn Gamma,
    family_var_bound (eqn :: Gamma) =
    Nat.max (var_count eqn) (family_var_bound Gamma).
Proof.
  reflexivity.
Qed.

Lemma cubic_poly_count_app :
  forall ts1 ts2,
    cubic_poly_count (ts1 ++ ts2) =
    cubic_poly_count ts1 + cubic_poly_count ts2.
Proof.
  intros ts1 ts2.
  induction ts1 as [|t ts1 IH]; simpl.
  - reflexivity.
  - rewrite IH.
    lia.
Qed.

Lemma reduce_terms_from_offset_monotone :
  forall base offset ts ts2 auxs offset',
    reduce_terms_from base offset ts = (ts2, auxs, offset') ->
    offset <= offset'.
Proof.
  intros base offset ts.
  revert offset.
  induction ts as [|t ts IH]; intros offset ts2 auxs offset' Hred.
  - inversion Hred; lia.
  - remember (coeff t) as c eqn:Hc.
    remember (mono t) as m0 eqn:Hm.
    simpl in Hred.
    destruct m0 as [|i|i j|i j k].
    + destruct (reduce_terms_from base offset ts)
        as [[ts2r auxsr] offsetr] eqn:Hrec.
      pose proof (IH offset ts2r auxsr offsetr Hrec) as Hih.
      inversion Hred; subst; clear Hred.
      rewrite <- Hm in H0.
      simpl in H0.
      inversion H0; subst; clear H0.
      exact Hih.
    + destruct (reduce_terms_from base offset ts)
        as [[ts2r auxsr] offsetr] eqn:Hrec.
      pose proof (IH offset ts2r auxsr offsetr Hrec) as Hih.
      inversion Hred; subst; clear Hred.
      rewrite <- Hm in H0.
      simpl in H0.
      inversion H0; subst; clear H0.
      exact Hih.
    + destruct (reduce_terms_from base offset ts)
        as [[ts2r auxsr] offsetr] eqn:Hrec.
      pose proof (IH offset ts2r auxsr offsetr Hrec) as Hih.
      inversion Hred; subst; clear Hred.
      rewrite <- Hm in H0.
      simpl in H0.
      inversion H0; subst; clear H0.
      exact Hih.
    + destruct (reduce_terms_from base (S offset) ts)
        as [[ts2r auxsr] offsetr] eqn:Hrec.
      pose proof (IH (S offset) ts2r auxsr offsetr Hrec) as Hih.
      inversion Hred; subst; clear Hred.
      rewrite <- Hm in H0.
      simpl in H0.
      inversion H0; subst; clear H0.
      eapply Nat.le_trans.
      * apply Nat.le_succ_diag_r.
      * exact Hih.
Qed.

Lemma aux_equations_from_length :
  forall target base offset auxs,
    length (aux_equations_from target base offset auxs) = length auxs.
Proof.
  intros target base offset auxs.
  revert offset.
  induction auxs as [|a auxs IH]; intro offset; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma reduce_equation_from_offset_monotone :
  forall target base offset eqn eqns2 offset',
    reduce_equation_from target base offset eqn = (eqns2, offset') ->
    offset <= offset'.
Proof.
  intros target base offset eqn eqns2 offset' Hred.
  unfold reduce_equation_from in Hred.
  destruct (reduce_terms_from base offset (lhs_terms eqn))
    as [[lhs2 auxs_l] offset1] eqn:Hl.
  destruct (reduce_terms_from base offset1 (rhs_terms eqn))
    as [[rhs2 auxs_r] offset2] eqn:Hr.
  inversion Hred; subst; clear Hred.
  eapply reduce_terms_from_offset_monotone in Hl.
  eapply reduce_terms_from_offset_monotone in Hr.
  lia.
Qed.
