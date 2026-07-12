(*M001_07__Obstruction.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / M001_07__Obstruction                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Negative transport and structural monotonicity for regulator theories. The
  previous layer proves that checked derivability and inductive derivability
  coincide. This file stays on the checked side: it transports
  non-derivability backward through a checked implication, and records that
  checked scripts remain checked when contexts or axiom sources are enlarged.

  This layer proves negative transport: if `A → B` is checked and `B` is
  uncheckable, then `A` is uncheckable. The result follows by precomposition
  and uses no consistency hypothesis.

*)

From M001 Require Export M001_06__Syntactic_Adequacy.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           NEGATIVE PRECOMPOSITION                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Negative precomposition is the contrapositive shape of
│          checked MP. Given a checked implication and a meta-level
│          proof that the consequent has no checked derivation, any
│          checked derivation of the antecedent would compose with the
│          implication by
│          `regulator_theory_checked_derivable_mp_lemma`,
│          contradicting the consequent non-derivability claim.
│
*)

(*             R; Γ ⊢check A → B ∧ R; Γ ⊬check B ⇒ R; Γ ⊬check A              *)

Lemma regulator_theory_not_checked_derivable_precompose_lemma :
  forall R Gamma A B,
    regulator_theory_checked_derivable R Gamma (Imp A B) ->
    regulator_theory_not_checked_derivable R Gamma B ->
    regulator_theory_not_checked_derivable R Gamma A.
Proof.
  intros R Gamma A B Himp HnotB Harg.
  apply HnotB.
  apply regulator_theory_checked_derivable_mp_lemma with (A := A).
  - exact Himp.
  - exact Harg.
Qed.

(*   profile, FT; Γ ⊢check A → B ∧ profile, FT; Γ ⊬check B ⇒ profile, FT; Γ   *)
(*                                  ⊬check A                                  *)

Lemma finite_axiom_set_not_checked_derivable_precompose_lemma :
  forall profile T Gamma A B,
    finite_axiom_set_checked_derivable profile T Gamma (Imp A B) ->
    finite_axiom_set_not_checked_derivable profile T Gamma B ->
    finite_axiom_set_not_checked_derivable profile T Gamma A.
Proof.
  intros profile T Gamma A B Himp HnotB Harg.
  pose proof
    (proj1
      (finite_axiom_set_checked_derivable_as_regulator_theory_lemma
        profile T Gamma (Imp A B))
      Himp) as HimpR.
  pose proof
    (proj1
      (finite_axiom_set_checked_derivable_as_regulator_theory_lemma
        profile T Gamma A)
      Harg) as HargR.
  apply HnotB.
  apply
    (proj2
      (finite_axiom_set_checked_derivable_as_regulator_theory_lemma
        profile T Gamma B)).
  apply regulator_theory_checked_derivable_mp_lemma with (A := A).
  - exact HimpR.
  - exact HargR.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             CONTEXT MONOTONICITY                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `context_included Γ Δ` is syntactic Boolean inclusion of
│          assumptions: every formula recognized by `ctx_mem_bool` in
│          `Γ` is also recognized in `Δ`. This matches the Boolean
│          membership test used to validate assumption lines.
│
*)

(*       Γ ≤ctx Δ ≔ ∀A. ctx_mem_bool(A,Γ)=true ⇒ ctx_mem_bool(A,Δ)=true       *)

Definition context_included
    (Gamma Delta : Context) : Prop :=
  forall A,
    ctx_mem_bool A Gamma = true ->
    ctx_mem_bool A Delta = true.

(*
│
│          The line-level context monotonicity proof only changes
│          assumption lines. Axiom lines depend on the same regulator
│          theory, and MP lines depend on the same checked prefix and
│          formula indices, so those branches are definitionally
│          unchanged.
│
*)

Lemma proof_line_valid_bool_context_monotone_lemma :
  forall R Gamma Delta prefix line,
    context_included Gamma Delta ->
    proof_line_valid_bool R Gamma prefix line = true ->
    proof_line_valid_bool R Delta prefix line = true.
Proof.
  intros R Gamma Delta prefix line Hinc Hline.
  destruct line as [phi just].
  destruct just as [| |i j].
  - unfold proof_line_valid_bool in *.
    simpl in *.
    apply Hinc.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
Qed.

Lemma proof_script_check_from_bool_context_monotone_lemma :
  forall R Gamma Delta prefix p,
    context_included Gamma Delta ->
    proof_script_check_from_bool R Gamma prefix p = true ->
    proof_script_check_from_bool R Delta prefix p = true.
Proof.
  intros R Gamma Delta prefix p Hinc.
  revert prefix.
  induction p as [|line rest IH]; intros prefix Hcheck.
  - reflexivity.
  - simpl in Hcheck.
    pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hline.
    pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hrest.
    simpl.
    rewrite
      (proof_line_valid_bool_context_monotone_lemma
        R Gamma Delta prefix line Hinc Hline).
    simpl.
    apply IH.
    exact Hrest.
Qed.

(*
│
│          Full checker monotonicity preserves the same finite proof
│          script. Only the line-checking conjunct is transported from
│          `Γ` to `Δ`; the final-formula comparison is independent of
│          the context.
│
*)

(*               Γ ≤ctx Δ ∧ R; Γ ⊢check[p] A ⇒ R; Δ ⊢check[p] A               *)

Lemma regulator_theory_check_bool_context_monotone_lemma :
  forall R Gamma Delta p A,
    context_included Gamma Delta ->
    regulator_theory_check_bool R Gamma p A = true ->
    regulator_theory_check_bool R Delta p A = true.
Proof.
  intros R Gamma Delta p A Hinc Hcheck.
  unfold regulator_theory_check_bool in *.
  pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hlines.
  pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hlast.
  rewrite
    (proof_script_check_from_bool_context_monotone_lemma
      R Gamma Delta nil p Hinc Hlines).
  simpl.
  exact Hlast.
Qed.

(*                  Γ ≤ctx Δ ∧ R; Γ ⊢check A ⇒ R; Δ ⊢check A                  *)

Lemma regulator_theory_checked_derivable_context_monotone_lemma :
  forall R Gamma Delta A,
    context_included Gamma Delta ->
    regulator_theory_checked_derivable R Gamma A ->
    regulator_theory_checked_derivable R Delta A.
Proof.
  intros R Gamma Delta A Hinc Hder.
  destruct Hder as [p Hp].
  exists p.
  apply regulator_theory_check_bool_context_monotone_lemma
    with (Gamma := Gamma).
  - exact Hinc.
  - exact Hp.
Qed.

(*                  Γ ≤ctx Δ ∧ R; Δ ⊬check A ⇒ R; Γ ⊬check A                  *)

Lemma regulator_theory_not_checked_derivable_context_antitone_lemma :
  forall R Gamma Delta A,
    context_included Gamma Delta ->
    regulator_theory_not_checked_derivable R Delta A ->
    regulator_theory_not_checked_derivable R Gamma A.
Proof.
  intros R Gamma Delta A Hinc Hnot Hder.
  apply Hnot.
  apply regulator_theory_checked_derivable_context_monotone_lemma
    with (Gamma := Gamma).
  - exact Hinc.
  - exact Hder.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                 AXIOM-SET AND REGULATOR-THEORY MONOTONICITY                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `axiom_set_included T U` is pointwise Boolean inclusion for
│          additional axiom sources. `regulator_theory_included R S`
│          is the corresponding inclusion after logical profile and
│          axiom source have been combined by `available_axiom_bool`.
│          The regulator-theory form is the most general monotonicity
│          hypothesis for checked scripts.
│
*)

(*             T ≤ax U ≔ ∀A. axiom_set_contains_bool(T,A)=true ⇒              *)
(*                     axiom_set_contains_bool(U,A)=true                      *)
(*               R ≤rt S ≔ ∀A. available_axiom_bool(R,A)=true ⇒               *)
(*                       available_axiom_bool(S,A)=true                       *)

Definition axiom_set_included
    (T U : AxiomSet) : Prop :=
  forall A,
    axiom_set_contains_bool T A = true ->
    axiom_set_contains_bool U A = true.

Definition regulator_theory_included
    (R S : RegulatorTheory) : Prop :=
  forall A,
    available_axiom_bool R A = true ->
    available_axiom_bool S A = true.

Lemma regulator_theory_included_from_axiom_set_included_lemma :
  forall profile T U,
    axiom_set_included T U ->
    regulator_theory_included
      (regulator_theory_with_axiom_set profile T)
      (regulator_theory_with_axiom_set profile U).
Proof.
  intros profile T U Hinc A Havail.
  unfold available_axiom_bool in *.
  simpl in *.
  apply bool_or_true_cases_lemma in Havail.
  destruct Havail as [Hlogical | Haxiom].
  - rewrite Hlogical.
    reflexivity.
  - rewrite (Hinc A Haxiom).
    destruct (logical_axiom_bool profile A);
      reflexivity.
Qed.

(*          T ≤ax U ⇒ regulator_theory_with_axiom_set(profile,T) ≤rt          *)
(*                 regulator_theory_with_axiom_set(profile,U)                 *)

(*
│
│          Regulator-theory monotonicity changes only axiom lines.
│          Assumption and MP validation are independent of the
│          regulator-theory axiom source once the context and prefix
│          are fixed.
│
*)

Lemma proof_line_valid_bool_regulator_theory_monotone_lemma :
  forall R S Gamma prefix line,
    regulator_theory_included R S ->
    proof_line_valid_bool R Gamma prefix line = true ->
    proof_line_valid_bool S Gamma prefix line = true.
Proof.
  intros R S Gamma prefix line Hinc Hline.
  destruct line as [phi just].
  destruct just as [| |i j].
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in *.
    apply Hinc.
    exact Hline.
  - unfold proof_line_valid_bool in *.
    simpl in *.
    exact Hline.
Qed.

Lemma proof_script_check_from_bool_regulator_theory_monotone_lemma :
  forall R S Gamma prefix p,
    regulator_theory_included R S ->
    proof_script_check_from_bool R Gamma prefix p = true ->
    proof_script_check_from_bool S Gamma prefix p = true.
Proof.
  intros R S Gamma prefix p Hinc.
  revert prefix.
  induction p as [|line rest IH]; intros prefix Hcheck.
  - reflexivity.
  - simpl in Hcheck.
    pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hline.
    pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hrest.
    simpl.
    rewrite
      (proof_line_valid_bool_regulator_theory_monotone_lemma
        R S Gamma prefix line Hinc Hline).
    simpl.
    apply IH.
    exact Hrest.
Qed.

(*               R ≤rt S ∧ R; Γ ⊢check[p] A ⇒ S; Γ ⊢check[p] A                *)

Lemma regulator_theory_check_bool_regulator_theory_monotone_lemma :
  forall R S Gamma p A,
    regulator_theory_included R S ->
    regulator_theory_check_bool R Gamma p A = true ->
    regulator_theory_check_bool S Gamma p A = true.
Proof.
  intros R S Gamma p A Hinc Hcheck.
  unfold regulator_theory_check_bool in *.
  pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hlines.
  pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hlast.
  rewrite
    (proof_script_check_from_bool_regulator_theory_monotone_lemma
      R S Gamma nil p Hinc Hlines).
  simpl.
  exact Hlast.
Qed.

(*                  R ≤rt S ∧ R; Γ ⊢check A ⇒ S; Γ ⊢check A                   *)

Lemma regulator_theory_checked_derivable_regulator_theory_monotone_lemma :
  forall R S Gamma A,
    regulator_theory_included R S ->
    regulator_theory_checked_derivable R Gamma A ->
    regulator_theory_checked_derivable S Gamma A.
Proof.
  intros R S Gamma A Hinc Hder.
  destruct Hder as [p Hp].
  exists p.
  apply regulator_theory_check_bool_regulator_theory_monotone_lemma
    with (R := R).
  - exact Hinc.
  - exact Hp.
Qed.

(*                  R ≤rt S ∧ S; Γ ⊬check A ⇒ R; Γ ⊬check A                   *)

Lemma regulator_theory_not_checked_derivable_regulator_theory_antitone_lemma :
  forall R S Gamma A,
    regulator_theory_included R S ->
    regulator_theory_not_checked_derivable S Gamma A ->
    regulator_theory_not_checked_derivable R Gamma A.
Proof.
  intros R S Gamma A Hinc Hnot Hder.
  apply Hnot.
  apply regulator_theory_checked_derivable_regulator_theory_monotone_lemma
    with (R := R).
  - exact Hinc.
  - exact Hder.
Qed.

(*     T ≤ax U ∧ regulator_theory_with_axiom_set(profile,T); Γ ⊢check A ⇒     *)
(*           regulator_theory_with_axiom_set(profile,U); Γ ⊢check A           *)

Lemma regulator_theory_checked_derivable_axiom_set_monotone_lemma :
  forall profile T U Gamma A,
    axiom_set_included T U ->
    regulator_theory_checked_derivable
      (regulator_theory_with_axiom_set profile T) Gamma A ->
    regulator_theory_checked_derivable
      (regulator_theory_with_axiom_set profile U) Gamma A.
Proof.
  intros profile T U Gamma A Hinc Hder.
  apply regulator_theory_checked_derivable_regulator_theory_monotone_lemma
    with (R := regulator_theory_with_axiom_set profile T).
  - apply regulator_theory_included_from_axiom_set_included_lemma.
    exact Hinc.
  - exact Hder.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        FINITE AXIOM-SET MONOTONICITY                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Finite axiom-set inclusion is the list-level counterpart of
│          `axiom_set_included`: every formula occurring in the source
│          list also occurs in the target list. The bridge lemma
│          converts it to Boolean axiom-set inclusion, after which the
│          general regulator-theory monotonicity theorem applies.
│
*)

(*          FT ≤fin FU ≔ ∀A. A ∈ finite_axiom_set_formulas(FT) ⇒ A ∈          *)
(*                       finite_axiom_set_formulas(FU)                        *)

Definition finite_axiom_set_included
    (T U : FiniteAxiomSet) : Prop :=
  forall A,
    In A T.(finite_axiom_set_formulas) ->
    In A U.(finite_axiom_set_formulas).

(*             FT ≤fin FU ⇒ finite_axiom_set_to_axiom_set(FT) ≤ax             *)
(*                     finite_axiom_set_to_axiom_set(FU)                      *)

Lemma finite_axiom_set_included_as_axiom_set_included_lemma :
  forall T U,
    finite_axiom_set_included T U ->
    axiom_set_included
      (finite_axiom_set_to_axiom_set T)
      (finite_axiom_set_to_axiom_set U).
Proof.
  intros T U Hinc A Hcontains.
  simpl in *.
  apply finite_axiom_set_contains_bool_complete_lemma.
  apply Hinc.
  apply finite_axiom_set_contains_bool_sound_lemma.
  exact Hcontains.
Qed.

(*       FT ≤fin FU ∧ profile, FT; Γ ⊢check A ⇒ profile, FU; Γ ⊢check A       *)

Lemma finite_axiom_set_checked_derivable_axiom_set_monotone_lemma :
  forall profile T U Gamma A,
    finite_axiom_set_included T U ->
    finite_axiom_set_checked_derivable profile T Gamma A ->
    finite_axiom_set_checked_derivable profile U Gamma A.
Proof.
  intros profile T U Gamma A Hinc Hder.
  pose proof
    (proj1
      (finite_axiom_set_checked_derivable_as_regulator_theory_lemma
        profile T Gamma A)
      Hder) as HderR.
  apply
    (proj2
      (finite_axiom_set_checked_derivable_as_regulator_theory_lemma
        profile U Gamma A)).
  apply regulator_theory_checked_derivable_regulator_theory_monotone_lemma
    with (R := finite_axiom_set_to_regulator_theory profile T).
  - unfold finite_axiom_set_to_regulator_theory.
    apply regulator_theory_included_from_axiom_set_included_lemma.
    apply finite_axiom_set_included_as_axiom_set_included_lemma.
    exact Hinc.
  - exact HderR.
Qed.

(*        Γ ≤ctx Δ ∧ profile, FT; Γ ⊢check A ⇒ profile, FT; Δ ⊢check A        *)

Lemma finite_axiom_set_checked_derivable_context_monotone_lemma :
  forall profile T Gamma Delta A,
    context_included Gamma Delta ->
    finite_axiom_set_checked_derivable profile T Gamma A ->
    finite_axiom_set_checked_derivable profile T Delta A.
Proof.
  intros profile T Gamma Delta A Hinc Hder.
  pose proof
    (proj1
      (finite_axiom_set_checked_derivable_as_regulator_theory_lemma
        profile T Gamma A)
      Hder) as HderR.
  apply
    (proj2
      (finite_axiom_set_checked_derivable_as_regulator_theory_lemma
        profile T Delta A)).
  apply regulator_theory_checked_derivable_context_monotone_lemma
    with (Gamma := Gamma).
  - exact Hinc.
  - exact HderR.
Qed.
