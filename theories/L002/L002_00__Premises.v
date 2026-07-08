(*L002_00__Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / L002_00__Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Picture a system that contains, inside itself, a smaller system reasoning
  about its own situation. The inner system has to operate as though the
  formulas it works with are authoritative, but it cannot, from the inside,
  fully account for the larger system that generated it and licenses what it
  does. This file names the parts of that picture: the object-level symbolic
  regulator `Sλ`, the inner system `M`, the consistency each must satisfy,
  the licensing surface `AsIF` by which `Sλ` authorizes formulas the inner
  one then treats as its own, and the formal trace of an attempted escape
  from those licensing conditions. Rocq is the ambient proof theory `T`; `Sλ`
  is the regulator theory represented inside the formalization. Downstream
  layers show that the inner system cannot coherently refute its licensed
  sentences (`L002_01`), that licensed reasoning accumulates pressure under
  nesting (`L002_02`), that there are facts about itself the inner system
  cannot internally derive (`L002_03`), and that the recursive-pressure
  interfaces have a concrete reusable one-state instance (`L002_04`).

*)

From M001 Require Export M001_95_API.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               BASIC VOCABULARY                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `CodingOfSLambdaDerivability` is the slot for the formula
│          that, inside the inner system, stands for the claim "`Sλ`
│          derives `A`". It is a parameter rather than a construction
│          because the package commits to no particular way of
│          representing `Sλ`-derivability inside the inner system.
│
*)

Definition CodingOfSLambdaDerivability : Type := Formula -> Formula.

(*
│
│          `DiagonalFormula` is the slot for the witness sentence the
│          mirror argument refutes — the sentence whose role is to say
│          that the inner system fully matches the outer one. It is a
│          parameter that constructs an actual witness via evaluation
│          closure.
│
*)

Definition DiagonalFormula : Type := Formula.

(*
│
│          `MirrorConsistent M Gamma` says the inner system does not
│          derive falsity at the working context. The mirror argument
│          is driven inside the inner system, so this is the
│          consistency assumption it relies on.
│
*)

(*                     MirrorConsistent(M, Γ) ≔ M ⊬_Γ ⊥.                      *)

Definition MirrorConsistent
    (M : RegulatorTheory)
    (Gamma : Context) : Prop :=
  ~ regulator_theory_checked_derivable M Gamma Bot.

(*
│
│          `SLambdaConsistent Slambda Gamma` is the consistency
│          assumption for the object-level regulator `Sλ`. Some
│          arguments — non-escape and one-zero exclusion in particular
│          — produce a contradiction inside `Sλ` rather than the inner
│          system, and rely on this rather than on `MirrorConsistent`.
│
*)

(*                    SLambdaConsistent(Sλ, Γ) ≔ Sλ ⊬_Γ ⊥.                    *)

Definition SLambdaConsistent
    (Slambda : RegulatorTheory)
    (Gamma : Context) : Prop :=
  ~ regulator_theory_checked_derivable Slambda Gamma Bot.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             AUTHORITY AND ESCAPE                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `AsIF` is the central object of the package: a predicate
│          over formulas marking which ones `Sλ` has authorized the
│          inner system to operate under. The reading of `asif A` is
│          that the inner system may proceed under `A` as if it held,
│          without thereby having an internal certificate that it
│          does.
│
*)

Definition AsIF : Type :=
  Formula -> Prop.

(*
│
│          `OperationalAdmissible` is an older spelling of `AsIF`,
│          kept for compatibility. Both names refer to the same type.
│
*)

Definition OperationalAdmissible : Type :=
  AsIF.

(*
│
│          `Escape M Gamma escape_claim` records that the inner system
│          has internally derived a formula whose intended reading is
│          that it has stepped outside its licensing conditions. The
│          predicate notes only the derivation event, not that any
│          actual escape has occurred.
│
*)

(*                         Escape(M, Γ, e) ≔ M ⊢_Γ e.                         *)

Definition Escape
    (M : RegulatorTheory)
    (Gamma : Context)
    (escape_claim : Formula) : Prop :=
  regulator_theory_checked_derivable M Gamma escape_claim.

(*
│
│          `LocalAuthority M Gamma asif` says that whatever `Sλ` has
│          authorized, the inner system actually derives. This is the
│          condition under which licensing is operationally
│          indistinguishable from derivation.
│
*)

(*            LocalAuthority(M, Γ, asif) ≔ ∀A. asif(A) ⇒ M ⊢_Γ A.             *)

Definition LocalAuthority
    (M : RegulatorTheory)
    (Gamma : Context)
    (asif : AsIF) : Prop :=
  forall A : Formula,
    asif A ->
    regulator_theory_checked_derivable M Gamma A.

(*
│
│          `EscapeReabsorbed M Gamma asif A escape_claim` says that
│          performing the escape re-licenses the very formula the
│          escape was meant to undercut. The structural mechanism
│          behind `regulator_non_escape`: every attempt to step
│          outside is itself recorded by `Sλ` as authorization to
│          continue.
│
*)

(*      EscapeReabsorbed(M, Γ, asif, A, e) ≔ Escape(M, Γ, e) ⇒ asif(A).       *)

Definition EscapeReabsorbed
    (M : RegulatorTheory)
    (Gamma : Context)
    (asif : AsIF)
    (A escape_claim : Formula) : Prop :=
  Escape M Gamma escape_claim ->
  asif A.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               MIRROR INTERFACE                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `InternalInclusionViaCoding` says the inner system,
│          whenever it derives `A`, also derives the formula
│          representing "`Sλ` derives `A`". The inner system cannot
│          derive anything without internally tracking that `Sλ`
│          covers it.
│
*)

(*                      ∀A. M ⊢_Γ A ⇒ M ⊢_Γ code_Sλ(A).                       *)

Definition InternalInclusionViaCoding
    (M : RegulatorTheory)
    (Gamma : Context)
    (code_Slambda_derives : CodingOfSLambdaDerivability) : Prop :=
  forall A : Formula,
    regulator_theory_checked_derivable M Gamma A ->
    regulator_theory_checked_derivable M Gamma
      (code_Slambda_derives A).

(*
│
│          `CodingInternalAccuracy` is the converse: whenever the
│          inner system derives "`Sλ` derives `A`", it already derives
│          `A` itself. The two predicates together say the inner
│          system's representation of `Sλ`-derivability matches its
│          own behavior.
│
*)

(*                      ∀A. M ⊢_Γ code_Sλ(A) ⇒ M ⊢_Γ A.                       *)

Definition CodingInternalAccuracy
    (M : RegulatorTheory)
    (Gamma : Context)
    (code_Slambda_derives : CodingOfSLambdaDerivability) : Prop :=
  forall A : Formula,
    regulator_theory_checked_derivable M Gamma
      (code_Slambda_derives A) ->
    regulator_theory_checked_derivable M Gamma A.

(*
│
│          `coding_soundness_from_accuracy_and_inclusion` derives
│          forward soundness — if the inner system's representation
│          says `Sλ` derives `A`, then it really does — from the two
│          coding hypotheses plus inclusion. A free consequence of
│          what we already have, not a separate assumption.
│
*)

(*              CodingInternalAccuracy(M, Γ, code_Sλ) ∧ M ⊆ Sλ ⇒              *)
(*                      ∀A. M ⊢_Γ code_Sλ(A) ⇒ Sλ ⊢_Γ A.                      *)

Lemma coding_soundness_from_accuracy_and_inclusion :
  forall (Slambda M : RegulatorTheory)
         (Gamma : Context)
         (code_Slambda_derives : CodingOfSLambdaDerivability),
    CodingInternalAccuracy M Gamma code_Slambda_derives ->
    regulator_theory_included M Slambda ->
    forall A : Formula,
      regulator_theory_checked_derivable M Gamma
        (code_Slambda_derives A) ->
      regulator_theory_checked_derivable Slambda Gamma A.
Proof.
  intros Slambda M Gamma code_Slambda_derives Haccuracy Hincluded A Hcoded.
  apply regulator_theory_checked_derivable_regulator_theory_monotone_lemma
    with (R := M).
  - exact Hincluded.
  - exact (Haccuracy A Hcoded).
Qed.

(*
│
│          `DiagonalEliminator` is the `Sλ`-side reading of the
│          witness sentence: `Sλ` derives the witness exactly when the
│          two systems agree on every formula. Retained for the public
│          wrapper theorem; the load-bearing argument uses
│          `ChiEqMInternal` below.
│
*)

(*                  Sλ ⊢_Γ χ_eq ⇔ (∀A. M ⊢_Γ A ⇔ Sλ ⊢_Γ A).                   *)

Definition DiagonalEliminator
    (Slambda M : RegulatorTheory)
    (Gamma : Context)
    (chi_eq : DiagonalFormula) : Prop :=
  regulator_theory_checked_derivable Slambda Gamma chi_eq <->
    (forall A : Formula,
       regulator_theory_checked_derivable M Gamma A <->
       regulator_theory_checked_derivable Slambda Gamma A).

(*
│
│          `ChiEqMInternal M Gamma chi_eq` is the trap that makes the
│          mirror argument work: refuting the witness inside the inner
│          system already forces deriving it. `L002_01` constructs an
│          actual witness with this property from the L001 evaluation
│          closure.
│
*)

(*                         M ⊢_Γ ¬χ_eq ⇒ M ⊢_Γ χ_eq.                          *)

Definition ChiEqMInternal
    (M : RegulatorTheory)
    (Gamma : Context)
    (chi_eq : DiagonalFormula) : Prop :=
  regulator_theory_checked_derivable M Gamma
    (formula_negation chi_eq) ->
  regulator_theory_checked_derivable M Gamma chi_eq.
