(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Premise layer for L003/TURING-ZOMBIE. We formulate the evaluator-relative diagonal argument over code, query, output, and halting relations. This machine-independent interface exposes the exact semantic structure used by the proof and admits direct instantiation by concrete machine models.]]@*)

(*@doc.pl@[[The development is constructive. `CompilerCorrect` names the uniform diagonal compiler law; `L003_03__Compiled_Countermachine` realizes that law with the explicit code transformer `h ↦ 2h+1` and proves its operational correctness.]]@*)

(*@head.end@*)

From Stdlib Require Export Arith PeanoNat Lia Program.Equality.

(*@section@[[RELATIONAL VOCABULARY]]@*)

(*@inline@[[Codes, inputs, and outputs are represented by natural numbers. The aliases keep their operational roles visible in later statements.]]@*)

Definition Code : Type := nat.
Definition Input : Type := nat.
Definition Output : Type := nat.

(*@inline@[[An output relation records that code `e` produces output `b` on input `x`; no determinism or totality is built into the relation itself.]]@*)

Definition OutputRelation : Type :=
  Code -> Input -> Output -> Prop.

Definition HaltingRelation : Type :=
  Code -> Input -> Prop.

(*@inline@[[A query coding combines a program code and an input into the single input consumed by an evaluator.]]@*)

Definition QueryCoding : Type :=
  Code -> Input -> Input.

Definition DiagonalCompiler : Type :=
  Code -> Code.

(*@section@[[TOTAL BINARY EVALUATION]]@*)

(*@inline@[[`BinaryOutput b` restricts the distinguished evaluator verdicts to `0` and `1`.]]@*)

(*@unicodemath@[[BinaryOutput(b) ⇔ b = 0 ∨ b = 1.]]@*)

Definition BinaryOutput (b : Output) : Prop :=
  b < 2.

(*@inline@[[`Tot2 out h` says that `h` has exactly one distinguished binary output on every query. The contract isolates verdicts `{0,1}`; other values of the ambient relation are semantically irrelevant to binary evaluation.]]@*)

(*@unicodemath@[[Tot2(out, h) ⇔ ∀ q, ∃! b, BinaryOutput(b) ∧ out(h, q, b).]]@*)

Definition Tot2 (out : OutputRelation) (h : Code) : Prop :=
  forall q : Input,
    exists! b : Output,
      BinaryOutput b /\ out h q b.

(*@inline@[[`EvalC` expresses evaluator correctness on a selected code domain `C`: `h` is total on binary verdicts, and verdict `1` is equivalent to halting for every code in `C`. The binary lemmas derive verdict `0` as the constructive complement.]]@*)

(*@unicodemath@[[EvalC(out, halt, query, C, h) ⇔ Tot2(out, h)]][[∧ ∀ e x, C(e) ⇒ (out(h, query(e,x), 1) ⇔ halt(e,x)).]]@*)

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

(*@section@[[DIAGONAL COMPILATION AND DOMAIN CLOSURE]]@*)

(*@inline@[[`CompilerCorrect` is the exact operational behavior required of a diagonal compiler. For a total binary evaluator `h`, the compiled code `diagonal h` halts on `x` exactly when `h` returns `0` on the doubled query `(x,x)`.]]@*)

(*@unicodemath@[[CompilerCorrect(out, halt, query, diagonal) ⇔]][[∀ h x, Tot2(out,h) ⇒ (halt(diagonal(h),x) ⇔ out(h,query(x,x),0)).]]@*)

Definition CompilerCorrect
    (out : OutputRelation)
    (halt : HaltingRelation)
    (query : QueryCoding)
    (diagonal : DiagonalCompiler) : Prop :=
  forall (h : Code) (x : Input),
    Tot2 out h ->
    (halt (diagonal h) x <-> out h (query x x) 0).

(*@inline@[[A domain is evaluator-diagonally closed when it contains the diagonal compiler product of every evaluator that is correct on that same domain.]]@*)

(*@unicodemath@[[EvaluatorDiagonalClosure(…, C) ⇔ ∀ h, EvalC(…, C, h) ⇒ C(diagonal(h)).]]@*)

Definition EvaluatorDiagonalClosure
    (out : OutputRelation)
    (halt : HaltingRelation)
    (query : QueryCoding)
    (diagonal : DiagonalCompiler)
    (C : Code -> Prop) : Prop :=
  forall h : Code,
    EvalC out halt query C h ->
    C (diagonal h).
