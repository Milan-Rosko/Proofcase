(*P002_08__Compiler.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / P002_08__Compiler                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This layer now stops exactly at the family semantics needed for the reset
  P002 target.

  Its role is narrow: fix the type of finite cubic families, the
  shared-valuation satisfaction relation for a whole family, and the basic
  list lemmas that the later trace emitter proofs use. The broken
  family-to-single-equation compression route is intentionally absent.

*)

From P002 Require Export P002_07__Step_Arithmetization.

Definition equation_family : Type := cubic_family_instance.

Definition family_wf (Gamma : equation_family) : Prop :=
  Forall equation_wf Gamma.

Definition solves_all (Gamma : equation_family) (rho : valuation) : Prop :=
  Forall (fun eqn => solves eqn rho) Gamma.

Definition family_satisfiable (Gamma : equation_family) : Prop :=
  cubic_family_yes Gamma.

Definition zero_valuation : valuation := fun _ => 0.

(*
│
│          An `equation_family` is the honest compilation target of
│          the FM arithmetization: a finite list of atomic cubic
│          equations, all read over one common valuation.
│
*)
(*  family\_satisfiable(\Gamma)\;\equiv\;\exists \rho.\ \forall E\in\Gamma,\  *)
(*                              solves(E,\rho).                               *)

Lemma family_satisfiable_iff :
  forall Gamma,
    family_satisfiable Gamma <-> exists rho, solves_all Gamma rho.
Proof.
  intros Gamma.
  unfold family_satisfiable, cubic_family_yes, solves_all.
  reflexivity.
Qed.

Lemma solves_all_nil :
  forall rho,
    solves_all [] rho.
Proof.
  intro rho.
  constructor.
Qed.

Lemma solves_all_cons :
  forall eqn Gamma rho,
    solves_all (eqn :: Gamma) rho <->
    solves eqn rho /\ solves_all Gamma rho.
Proof.
  intros eqn Gamma rho.
  split.
  - intro H.
    inversion H; subst.
    tauto.
  - intros [Heq Hrest].
    constructor; assumption.
Qed.

Lemma solves_all_singleton :
  forall eqn rho,
    solves_all [eqn] rho <->
    solves eqn rho.
Proof.
  intros eqn rho.
  rewrite solves_all_cons.
  split.
  - intros [Heq Hnil].
    exact Heq.
  - intro Heq.
    split.
    + exact Heq.
    + constructor.
Qed.

Lemma solves_all_app :
  forall Gamma1 Gamma2 rho,
    solves_all (Gamma1 ++ Gamma2) rho <->
    solves_all Gamma1 rho /\ solves_all Gamma2 rho.
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
  - rewrite !solves_all_cons.
    rewrite IH.
    tauto.
Qed.

Lemma family_wf_nil :
  family_wf [].
Proof.
  constructor.
Qed.

Lemma family_wf_cons :
  forall eqn Gamma,
    family_wf (eqn :: Gamma) <->
    equation_wf eqn /\ family_wf Gamma.
Proof.
  intros eqn Gamma.
  split.
  - intro H.
    inversion H; subst.
    tauto.
  - intros [Heq Hrest].
    constructor; assumption.
Qed.

Lemma family_wf_singleton :
  forall eqn,
    family_wf [eqn] <-> equation_wf eqn.
Proof.
  intro eqn.
  rewrite family_wf_cons.
  split.
  - intros [Heq _].
    exact Heq.
  - intro Heq.
    split.
    + exact Heq.
    + constructor.
Qed.

Lemma family_wf_app :
  forall Gamma1 Gamma2,
    family_wf (Gamma1 ++ Gamma2) <->
    family_wf Gamma1 /\ family_wf Gamma2.
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
  - rewrite !family_wf_cons.
    rewrite IH.
    tauto.
Qed.

Lemma solves_all_implies_family_wf :
  forall Gamma rho,
    solves_all Gamma rho ->
    family_wf Gamma.
Proof.
  intros Gamma rho Hsolves.
  induction Hsolves as [|eqn Gamma Hsolve Hrest IH]; constructor.
  - exact (proj1 Hsolve).
  - exact IH.
Qed.

Lemma family_satisfiable_nil :
  family_satisfiable [].
Proof.
  apply (proj2 (family_satisfiable_iff [])).
  exists zero_valuation.
  apply solves_all_nil.
Qed.

Lemma family_satisfiable_cons :
  forall eqn Gamma,
    family_satisfiable (eqn :: Gamma) ->
    exists rho,
      solves eqn rho /\ solves_all Gamma rho.
Proof.
  intros eqn Gamma Hsat.
  apply family_satisfiable_iff in Hsat.
  destruct Hsat as [rho Hall].
  exists rho.
  now apply solves_all_cons.
Qed.

(*
│
│          `solves_all_nil`, `solves_all_cons`,
│          `solves_all_singleton`, and `solves_all_app` are the only
│          family combinators exported here because they are exactly
│          the proof tools needed to decompose emitted trace families
│          blockwise.
│
*)
