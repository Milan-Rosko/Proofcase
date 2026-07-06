(*A002_03__Formula_Syntax.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                     Proofcase / A002_03__Formula_Syntax                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Formula-syntax layer for A002-Core. We encode the implicational Hilbert
  object language as A001-canonical natural-number trees, provide bounded
  formula recognition, and expose an arithmetic implication parser.

  Formula recognition is syntactic and fuel-bounded. The parser never treats
  the total A001 decoder as a validity oracle: every formula node and every
  implication payload must pass canonical A001 destructuring before its
  components are inspected as formula structure.

*)

From A002 Require Export A002_02__Tagged_Lists.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             FORMULA CONSTRUCTORS                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Variables carry tag `0` and a natural-number variable index
│          as payload.
│
*)

Definition TAG_VAR : nat := 0.

(*
│
│          Implications carry tag `1` and an A001 pair containing
│          antecedent and consequent formula codes.
│
*)

Definition TAG_IMP : nat := 1.

(*
│
│          `code_var i` is the canonical formula code for variable
│          `i`.
│
*)

Definition code_var (i : nat) : nat :=
  encode TAG_VAR i.

(*
│
│          `code_imp a b` is the canonical formula code for
│          implication from `a` to `b`. Well-formedness of `a` and `b`
│          is checked separately.
│
*)

Definition code_imp (a b : nat) : nat :=
  encode TAG_IMP (encode a b).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             FORMULA PROJECTIONS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `formula_tag` reads the outer formula tag exposed by A001
│          decoding. It is used as a formula tag only in branches that
│          have already checked A001 canonicity.
│
*)

Definition formula_tag (c : nat) : nat :=
  fst001 c.

(*
│
│          `formula_payload` reads the outer formula payload exposed
│          by A001 decoding. It is interpreted according to the outer
│          formula tag only after canonicity has been established.
│
*)

Definition formula_payload (c : nat) : nat :=
  snd001 c.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         BOUNDED FORMULA RECOGNITION                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `is_formula_fuel fuel c` checks well-formedness by bounded
│          recursive descent through canonical formula nodes.
│          Variables stop the descent; implication nodes consume one
│          unit of fuel and then check both subformulas.
│
*)

Fixpoint is_formula_fuel (fuel c : nat) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      if canonical001b c then
        let tag := formula_tag c in
        let payload := formula_payload c in
        if Nat.eqb tag TAG_VAR then
          true
        else if Nat.eqb tag TAG_IMP then
          if canonical001b payload then
            is_formula_fuel fuel' (fst001 payload)
            && is_formula_fuel fuel' (snd001 payload)
          else false
        else false
      else false
  end.

(*
│
│          `formula_bound c` is the current explicit arithmetic fuel
│          budget for total formula recognition. The first
│          implementation uses `S c`; stronger constructor lemmas for
│          this total wrapper depend on later size facts about A001
│          encodings.
│
*)

Definition formula_bound (c : nat) : nat :=
  S c.

(*
│
│          `is_formula` is the total formula recognizer obtained by
│          running the bounded recognizer at `formula_bound c`.
│
*)

Definition is_formula (c : nat) : bool :=
  is_formula_fuel (formula_bound c) c.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              IMPLICATION PARSER                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `parse_imp phi` returns `accept payload` when `phi` is a
│          canonical implication node and `payload` is the canonical
│          A001 pair of antecedent and consequent. Failures are
│          returned as arithmetic errors.
│
*)

Definition parse_imp (phi : nat) : nat :=
  if canonical001b phi then
    let tag := formula_tag phi in
    let payload := formula_payload phi in
    if Nat.eqb tag TAG_IMP then
      if canonical001b payload then
        accept payload
      else
        reject STAGE_FORMULA 0 ERR_BAD_IMP_PAYLOAD
    else
      reject STAGE_FORMULA 0 ERR_NOT_IMP
  else
    reject STAGE_FORMULA 0 ERR_NONCANONICAL_FORMULA.

(*
│
│          `parse_formula_diagnostic` exposes formula recognition as
│          an arithmetic status/payload result for the IO layer. On
│          success the payload is the original formula code; on
│          failure it reports the generic formula-stage diagnostic.
│
*)

Definition parse_formula_diagnostic (phi : nat) : nat :=
  if is_formula phi then
    accept phi
  else
    reject STAGE_FORMULA 0 ERR_BAD_FORMULA_TAG.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CONSTRUCTOR FACTS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A variable constructor is recognized as a well-formed
│          formula with any positive fuel.
│
*)

Lemma is_formula_fuel_var :
  forall fuel i,
    0 < fuel ->
    is_formula_fuel fuel (code_var i) = true.
Proof.
  intros fuel i Hfuel.
  destruct fuel as [|fuel']; [lia|].
  cbn [is_formula_fuel].
  unfold code_var, formula_tag, formula_payload.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*
│
│          Every encoded variable is a well-formed formula.
│
*)

Lemma is_formula_var :
  forall i, is_formula (code_var i) = true.
Proof.
  intro i.
  unfold is_formula, formula_bound.
  apply is_formula_fuel_var.
  lia.
Qed.

(*
│
│          If both sides are recognized with the same explicit fuel,
│          their implication constructor is recognized with one
│          additional fuel step.
│
*)

Lemma is_formula_fuel_imp :
  forall fuel a b,
    is_formula_fuel fuel a = true ->
    is_formula_fuel fuel b = true ->
    is_formula_fuel (S fuel) (code_imp a b) = true.
Proof.
  intros fuel a b Ha Hb.
  cbn [is_formula_fuel].
  unfold code_imp, formula_tag, formula_payload.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  cbn [TAG_VAR TAG_IMP].
  rewrite Nat.eqb_refl.
  rewrite canonical001b_encode.
  apply Bool.andb_true_iff.
  split.
  - rewrite fst001_encode. exact Ha.
  - rewrite snd001_encode. exact Hb.
Qed.

(*
│
│          Parsing a constructed implication returns the original
│          canonical antecedent/consequent payload.
│
*)

Lemma parse_imp_code_imp :
  forall a b, parse_imp (code_imp a b) = accept (encode a b).
Proof.
  intros a b.
  unfold parse_imp, code_imp, formula_tag, formula_payload.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  cbn [TAG_VAR TAG_IMP].
  rewrite Nat.eqb_refl.
  rewrite canonical001b_encode.
  reflexivity.
Qed.
