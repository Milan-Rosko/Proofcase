(*P002_11__Quadratic_Family.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                    Proofcase / P002_11__Quadratic_Family                     │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This phase introduces only the degree-2 target language needed for Step A
  of the quartic roadmap. It mirrors the existing cubic-family surface, but
  does not yet perform any reduction from cubic families.

  The role of this file is deliberately narrow: define quadratic monomials,
  terms, equations, well-formedness, semantics, family satisfiability, and
  the basic list lemmas that later constructive reductions will need.

*)

From P002 Require Export P002_08__Compiler.

Inductive monomial2 : Type :=
| m2_const
| m2_linear (i : nat)
| m2_quadratic (i j : nat).

Record term2 : Type := {
  coeff2 : nat;
  mono2 : monomial2
}.

Record h10_nd2n_equation : Type := {
  var_count2 : nat;
  lhs_terms2 : list term2;
  rhs_terms2 : list term2
}.

Definition monomial2_wf (n : nat) (m : monomial2) : Prop :=
  match m with
  | m2_const => True
  | m2_linear i => i < n
  | m2_quadratic i j => i < n /\ j < n
  end.

Definition equation2_wf (eqn : h10_nd2n_equation) : Prop :=
  Forall (fun t => monomial2_wf (var_count2 eqn) (mono2 t)) (lhs_terms2 eqn) /\
  Forall (fun t => monomial2_wf (var_count2 eqn) (mono2 t)) (rhs_terms2 eqn).

Definition eval_monomial2 (rho : valuation) (m : monomial2) : nat :=
  match m with
  | m2_const => 1
  | m2_linear i => rho i
  | m2_quadratic i j => rho i * rho j
  end.

Definition eval_term2 (rho : valuation) (t : term2) : nat :=
  coeff2 t * eval_monomial2 rho (mono2 t).

Definition eval_poly2 (ts : list term2) (rho : valuation) : nat :=
  fold_right (fun t acc => eval_term2 rho t + acc)%nat 0 ts.

Definition solves2 (eqn : h10_nd2n_equation) (rho : valuation) : Prop :=
  equation2_wf eqn /\
  eval_poly2 (lhs_terms2 eqn) rho = eval_poly2 (rhs_terms2 eqn) rho.

Definition quadratic_family_instance : Type := list h10_nd2n_equation.

Definition solves_all2 (Gamma : quadratic_family_instance) (rho : valuation) : Prop :=
  Forall (fun eqn => solves2 eqn rho) Gamma.

Definition quadratic_family_yes (Gamma : quadratic_family_instance) : Prop :=
  exists rho : valuation, solves_all2 Gamma rho.

Definition quadratic_family_wf (Gamma : quadratic_family_instance) : Prop :=
  Forall equation2_wf Gamma.

Lemma quadratic_family_yes_iff :
  forall Gamma,
    quadratic_family_yes Gamma <-> exists rho, solves_all2 Gamma rho.
Proof.
  intros Gamma.
  unfold quadratic_family_yes.
  reflexivity.
Qed.

Lemma solves_all2_nil :
  forall rho,
    solves_all2 [] rho.
Proof.
  intro rho.
  constructor.
Qed.

Lemma solves_all2_cons :
  forall eqn Gamma rho,
    solves_all2 (eqn :: Gamma) rho <->
    solves2 eqn rho /\ solves_all2 Gamma rho.
Proof.
  intros eqn Gamma rho.
  split.
  - intro H.
    inversion H; subst.
    tauto.
  - intros [Heq Hrest].
    constructor; assumption.
Qed.

Lemma solves_all2_singleton :
  forall eqn rho,
    solves_all2 [eqn] rho <-> solves2 eqn rho.
Proof.
  intros eqn rho.
  rewrite solves_all2_cons.
  split.
  - intros [Heq _].
    exact Heq.
  - intro Heq.
    split.
    + exact Heq.
    + constructor.
Qed.

Lemma solves_all2_app :
  forall Gamma1 Gamma2 rho,
    solves_all2 (Gamma1 ++ Gamma2) rho <->
    solves_all2 Gamma1 rho /\ solves_all2 Gamma2 rho.
Proof.
  intros Gamma1 Gamma2 rho.
  induction Gamma1 as [|eqn Gamma1 IH]; simpl.
  - split.
    + intro H.
      split.
      * constructor.
      * exact H.
    + intros [_ H].
      exact H.
  - rewrite !solves_all2_cons.
    rewrite IH.
    tauto.
Qed.

Lemma quadratic_family_wf_nil :
  quadratic_family_wf [].
Proof.
  constructor.
Qed.

Lemma quadratic_family_wf_cons :
  forall eqn Gamma,
    quadratic_family_wf (eqn :: Gamma) <->
    equation2_wf eqn /\ quadratic_family_wf Gamma.
Proof.
  intros eqn Gamma.
  split.
  - intro H.
    inversion H; subst.
    tauto.
  - intros [Heq Hrest].
    constructor; assumption.
Qed.

Lemma quadratic_family_wf_singleton :
  forall eqn,
    quadratic_family_wf [eqn] <-> equation2_wf eqn.
Proof.
  intro eqn.
  rewrite quadratic_family_wf_cons.
  split.
  - intros [Heq _].
    exact Heq.
  - intro Heq.
    split.
    + exact Heq.
    + constructor.
Qed.

Lemma quadratic_family_wf_app :
  forall Gamma1 Gamma2,
    quadratic_family_wf (Gamma1 ++ Gamma2) <->
    quadratic_family_wf Gamma1 /\ quadratic_family_wf Gamma2.
Proof.
  intros Gamma1 Gamma2.
  induction Gamma1 as [|eqn Gamma1 IH]; simpl.
  - split.
    + intro H.
      split.
      * constructor.
      * exact H.
    + intros [_ H].
      exact H.
  - rewrite !quadratic_family_wf_cons.
    rewrite IH.
    tauto.
Qed.

Lemma solves_all2_implies_quadratic_family_wf :
  forall Gamma rho,
    solves_all2 Gamma rho ->
    quadratic_family_wf Gamma.
Proof.
  intros Gamma rho Hsolves.
  induction Hsolves as [|eqn Gamma Hsolve Hrest IH]; constructor.
  - exact (proj1 Hsolve).
  - exact IH.
Qed.

Lemma quadratic_family_yes_nil :
  quadratic_family_yes [].
Proof.
  apply (proj2 (quadratic_family_yes_iff [])).
  exists zero_valuation.
  apply solves_all2_nil.
Qed.

Lemma quadratic_family_yes_cons :
  forall eqn Gamma,
    quadratic_family_yes (eqn :: Gamma) ->
    exists rho,
      solves2 eqn rho /\ solves_all2 Gamma rho.
Proof.
  intros eqn Gamma Hsat.
  apply quadratic_family_yes_iff in Hsat.
  destruct Hsat as [rho Hall].
  exists rho.
  now apply solves_all2_cons.
Qed.
