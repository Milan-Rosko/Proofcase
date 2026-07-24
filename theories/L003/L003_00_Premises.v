(*L003_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / L003_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Premise layer for L003/TURING-ZOMBIE. We introduce the code, query, output,
  and halting relations used by the evaluator-relative diagonal argument,
  without assuming a universal machine or a particular machine language.

  The development is constructive and conditional. `CompilerCorrect` names
  the operational law that a supplied diagonal compiler must satisfy; it is a
  proposition to be established by a concrete semantics, not an implicit
  identification between a code label and the evaluator currently executing.

*)

From Stdlib Require Export Arith PeanoNat Lia Program.Equality.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            RELATIONAL VOCABULARY                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Codes, inputs, and outputs are represented by natural
│          numbers. The aliases keep their operational roles visible
│          in later statements.
│
*)

Definition Code : Type := nat.
Definition Input : Type := nat.
Definition Output : Type := nat.

(*
│
│          An output relation records that code `e` produces output
│          `b` on input `x`; no determinism or totality is built into
│          the relation itself.
│
*)

Definition OutputRelation : Type :=
  Code -> Input -> Output -> Prop.

Definition HaltingRelation : Type :=
  Code -> Input -> Prop.

(*
│
│          A query coding combines a program code and an input into
│          the single input consumed by an evaluator.
│
*)

Definition QueryCoding : Type :=
  Code -> Input -> Input.

Definition DiagonalCompiler : Type :=
  Code -> Code.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           TOTAL BINARY EVALUATION                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `BinaryOutput b` restricts the distinguished evaluator
│          verdicts to `0` and `1`.
│
*)

(*                      BinaryOutput(b) ⇔ b = 0 ∨ b = 1.                      *)

Definition BinaryOutput (b : Output) : Prop :=
  b < 2.

(*
│
│          `Tot2 out h` says that `h` has exactly one distinguished
│          binary output on every query. Outputs outside `{0,1}` are
│          not constrained by this predicate.
│
*)

(*         Tot2(out, h) ⇔ ∀ q, ∃! b, BinaryOutput(b) ∧ out(h, q, b).          *)

Definition Tot2 (out : OutputRelation) (h : Code) : Prop :=
  forall q : Input,
    exists! b : Output,
      BinaryOutput b /\ out h q b.

(*
│
│          `EvalC` expresses evaluator correctness on a selected code
│          domain `C`: `h` is total on binary verdicts, and verdict
│          `1` is equivalent to halting for every code in `C`. The
│          binary lemmas derive verdict `0` as the constructive
│          complement.
│
*)

(*                EvalC(out, halt, query, C, h) ⇔ Tot2(out, h)                *)
(*            ∧ ∀ e x, C(e) ⇒ (out(h, query(e,x), 1) ⇔ halt(e,x)).            *)

Definition EvalC
    (out : OutputRelation)
    (halt : HaltingRelation)
    (query : QueryCoding)
    (C : Code -> Prop)
    (h : Code) : Prop :=
  Tot2 out h /\
  forall (e : Code) (x : Input),
    C e ->
    (out h (query e x) 1 <-> halt e x).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                   DIAGONAL COMPILATION AND DOMAIN CLOSURE                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `CompilerCorrect` is the exact operational behavior
│          required of a diagonal compiler. For a total binary
│          evaluator `h`, the compiled code `diagonal h` halts on `x`
│          exactly when `h` returns `0` on the doubled query `(x,x)`.
│
*)

(*               CompilerCorrect(out, halt, query, diagonal) ⇔                *)
(*     ∀ h x, Tot2(out,h) ⇒ (halt(diagonal(h),x) ⇔ out(h,query(x,x),0)).      *)

Definition CompilerCorrect
    (out : OutputRelation)
    (halt : HaltingRelation)
    (query : QueryCoding)
    (diagonal : DiagonalCompiler) : Prop :=
  forall (h : Code) (x : Input),
    Tot2 out h ->
    (halt (diagonal h) x <-> out h (query x x) 0).

(*
│
│          A domain is evaluator-diagonally closed when it contains
│          the diagonal compiler product of every evaluator that is
│          correct on that same domain.
│
*)

(*   EvaluatorDiagonalClosure(…, C) ⇔ ∀ h, EvalC(…, C, h) ⇒ C(diagonal(h)).   *)

Definition EvaluatorDiagonalClosure
    (out : OutputRelation)
    (halt : HaltingRelation)
    (query : QueryCoding)
    (diagonal : DiagonalCompiler)
    (C : Code -> Prop) : Prop :=
  forall h : Code,
    EvalC out halt query C h ->
    C (diagonal h).
