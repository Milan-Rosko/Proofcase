(*M001_09__Evaluation_Closure.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                   Proofcase / M001_09__Evaluation_Closure                    │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Evaluation closure above the regulator-theory interface. The generic part
  packages an abstract evaluator `eval_apply c x` with a completeness
  principle saying that every unary behavior can be named by some code. The
  fixed-point theorem is the standard diagonal construction for such a
  complete evaluator.

  The regulator-facing part weakens strict formula equality to
  `regulator_theory_equivalent`: two formulas are equivalent when each
  implication direction belongs to the checked regulator-theory closure. A
  regulated evaluator that names every formula-valued behavior up to this
  equivalence yields a formula equivalent to its transformed image. M001
  stops at this syntactic bridge; it does not assign semantic truth, model
  validity, arithmetic coding, diagonal obstruction, or self-recognition to
  the bridge.

*)

From M001 Require Export M001_08__Regulation.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           GENERIC EVALUATION FRAME                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          An `EvaluationFrame Code Output` packages an evaluator
│          together with a naming-completeness principle.
│          `evaluation_apply E c x` is the result of evaluating the
│          behavior named by code `c` at input/name `x`.
│
*)

(*            evaluation_complete(E) ≔ ∀f : Code → Output. ∃c. ∀x.            *)
(*                        evaluation_apply(E,c,x)=f(x)                        *)

Record EvaluationFrame (Code Output : Type) : Type := {
  evaluation_apply : Code -> Code -> Output;

  evaluation_complete :
    forall f : Code -> Output,
      exists c : Code,
        forall x : Code,
          evaluation_apply c x = f x
}.

Arguments evaluation_apply {Code Output} _ _ _.
Arguments evaluation_complete {Code Output} _ _.

Definition evaluation_has_fixed_point
    {Output : Type}
    (g : Output -> Output) : Prop :=
  exists b : Output, g b = b.

(*                 evaluation_has_fixed_point(g) ≔ ∃b. g(b)=b                 *)

Definition evaluation_fixed_point_free
    {Output : Type}
    (g : Output -> Output) : Prop :=
  forall b : Output, g b <> b.

(*                evaluation_fixed_point_free(g) ≔ ∀b. g(b)≠b                 *)

(*
│
│          Completeness forces a fixed point for every transformer
│          `g`. Name the behavior `fun x => g (evaluation_apply E x
│          x)`, then evaluate its name at itself.
│
*)

(*         evaluation_complete(E) ⇒ ∀g. evaluation_has_fixed_point(g)         *)

Lemma evaluation_frame_fixed_point_lemma :
  forall (Code Output : Type)
         (E : EvaluationFrame Code Output)
         (g : Output -> Output),
    evaluation_has_fixed_point g.
Proof.
  intros Code Output E g.
  destruct
    (evaluation_complete E
      (fun x => g (evaluation_apply E x x)))
    as [c Hc].
  exists (evaluation_apply E c c).
  symmetry.
  apply Hc.
Qed.

(*
│
│          `fixed_point_free_obstructs_frame` is the generic
│          incompatibility principle: a complete evaluation frame
│          forces a fixed point for every transformer, so a supplied
│          fixed-point-free transformer rules out that frame.
│
*)

(*   evaluation_fixed_point_free(g) ∧ EvaluationFrame(Code,Output) ⇒ False    *)

Lemma fixed_point_free_obstructs_frame :
  forall (Code Output : Type)
         (E : EvaluationFrame Code Output)
         (g : Output -> Output),
    evaluation_fixed_point_free g ->
    False.
Proof.
  intros Code Output E g Hfree.
  destruct (evaluation_frame_fixed_point_lemma Code Output E g)
    as [b Hfixed].
  apply (Hfree b).
  exact Hfixed.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               BOOLEAN ENDPOINT                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                         bool_flip(b) ≔ b xor true                          *)

Definition bool_flip (b : bool) : bool :=
  xorb b true.

(*
│
│          `bool_flip` swaps the two Boolean values. It has no fixed
│          point, so a complete evaluator with Boolean output cannot
│          exist.
│
*)

Lemma bool_flip_fixed_point_free_lemma :
  evaluation_fixed_point_free bool_flip.
Proof.
  unfold evaluation_fixed_point_free, bool_flip.
  intro b.
  destruct b; simpl; discriminate.
Qed.

(* evaluation_fixed_point_free(bool_flip) ⇒ ¬∃E : EvaluationFrame(Code,bool). *)
(*                           evaluation_complete(E)                           *)

Lemma no_bool_evaluation_frame_lemma :
  forall Code (E : EvaluationFrame Code bool),
    False.
Proof.
  intros Code E.
  apply (fixed_point_free_obstructs_frame
    Code bool E bool_flip).
  apply bool_flip_fixed_point_free_lemma.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          FORMULA NEGATION ENDPOINT                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The formula endpoint is purely structural: no finite
│          formula tree is equal to the implication whose antecedent
│          is that same tree. Therefore `formula_negation A = A → ⊥`
│          has no strict syntactic fixed point.
│
*)

(*                              ∀A C. A ≠ A → C                               *)
(*               evaluation_fixed_point_free(formula_negation)                *)

Lemma formula_no_self_imp_lemma :
  forall A C : Formula,
    A <> Imp A C.
Proof.
  induction A as [|A1 IH1 A2 IH2]; intros C H.
  - discriminate H.
  - injection H as Hleft _.
    apply (IH1 A2).
    exact Hleft.
Qed.

Lemma formula_negation_fixed_point_free_lemma :
  evaluation_fixed_point_free formula_negation.
Proof.
  unfold evaluation_fixed_point_free, formula_negation.
  intros A H.
  apply (formula_no_self_imp_lemma A Bot).
  symmetry.
  exact H.
Qed.

Lemma no_formula_evaluation_frame_lemma :
  forall E : EvaluationFrame Formula Formula,
    False.
Proof.
  intro E.
  apply (fixed_point_free_obstructs_frame
    Formula Formula E formula_negation).
  apply formula_negation_fixed_point_free_lemma.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          REGULATED EVALUATION FRAME                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A `RegulatorEvaluationFrame` is the checked-regulator
│          version of an evaluation frame. Completeness now names
│          every behavior only up to `regulator_theory_equivalent`,
│          not by syntactic equality of formulas.
│
*)

(*             B ≃_{R,Γ} C ≔ regulator_theory_equivalent(R,Γ,B,C)             *)
(*               regulator_evaluation_complete(E) ≔ ∀f. ∃c. ∀x.               *)
(*               regulator_evaluation_apply(E,c,x) ≃_{R,Γ} f(x)               *)

Record RegulatorEvaluationFrame
    (R : RegulatorTheory)
    (Gamma : Context)
    (Code : Type) : Type := {
  regulator_evaluation_apply : Code -> Code -> Formula;

  regulator_evaluation_complete :
    forall f : Code -> Formula,
      exists c : Code,
        forall x : Code,
          regulator_theory_equivalent R Gamma
            (regulator_evaluation_apply c x)
            (f x)
}.

Arguments regulator_evaluation_apply {R Gamma Code} _ _ _.
Arguments regulator_evaluation_complete {R Gamma Code} _ _.

(*
│
│          The regulated fixed-point bridge names `fun x => g
│          (regulator_evaluation_apply E x x)`. Evaluating the
│          resulting code at itself gives a formula equivalent, under
│          the regulator-theory closure, to its `g`-image.
│
*)

(*         regulator_evaluation_complete(E) ⇒ ∀g. ∃B. B ≃_{R,Γ} g(B)          *)

Lemma regulator_evaluation_frame_fixed_point_lemma :
  forall R Gamma Code
         (E : RegulatorEvaluationFrame R Gamma Code)
         (g : Formula -> Formula),
    exists B : Formula,
      regulator_theory_equivalent R Gamma B (g B).
Proof.
  intros R Gamma Code E g.
  destruct
    (regulator_evaluation_complete E
      (fun x => g (regulator_evaluation_apply E x x)))
    as [c Hc].
  exists (regulator_evaluation_apply E c c).
  apply Hc.
Qed.

(*
│
│          `regulator_equiv_fixed_point_free` is the
│          regulator-equivalence version of fixed-point freeness: no
│          formula may be equivalent, under
│          `regulator_theory_equivalent R Γ`, to its `g`-image.
│
*)

Definition regulator_equiv_fixed_point_free
    (R : RegulatorTheory)
    (Gamma : Context)
    (g : Formula -> Formula) : Prop :=
  forall B : Formula,
    regulator_theory_equivalent R Gamma B (g B) -> False.

(*         equiv_fixed_point_free(R,Γ,g) ≔ ∀B. B ≃_{R,Γ} g(B) ⇒ False         *)

(*
│
│          `regulator_fixed_point_free_obstructs_frame` is the
│          regulated incompatibility principle. A
│          `RegulatorEvaluationFrame` always yields an equivalence
│          fixed point for every formula transformer; therefore an
│          explicit regulator-equivalence fixed-point-free transformer
│          rules out such a frame.
│
*)

(*regulator_equiv_fixed_point_free(R,Γ,g) ∧ RegulatorEvaluationFrame(R,Γ,Code)*)
(*                                  ⇒ False                                   *)

Lemma regulator_fixed_point_free_obstructs_frame :
  forall R Gamma Code
         (E : RegulatorEvaluationFrame R Gamma Code)
         (g : Formula -> Formula),
    regulator_equiv_fixed_point_free R Gamma g ->
    False.
Proof.
  intros R Gamma Code E g Hfree.
  destruct
    (regulator_evaluation_frame_fixed_point_lemma
      R Gamma Code E g)
    as [B Hequiv].
  apply (Hfree B).
  exact Hequiv.
Qed.
