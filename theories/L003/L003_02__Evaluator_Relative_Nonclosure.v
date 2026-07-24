(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Evaluator-relative nonclosure layer for L003. Given a compiler satisfying `CompilerCorrect`, every total binary evaluator that is correct on a code domain must exclude its own diagonal compiler product from that domain.]]@*)

(*@doc.pl@[[The proof is constructive. Evaluator correctness, uniform compiler correctness, and exact binary totality force the diagonal query to carry a verdict equivalent to its own negation; evaluator-relative domain membership is therefore impossible.]]@*)

(*@head.end@*)

From L003 Require Export L003_01__Binary_Evaluation.

(*@section@[[EVALUATOR-RELATIVE NONCLOSURE]]@*)

(*@inline@[[Assuming the diagonal product lies in `C` turns verdict `1` into halting, compiler correctness turns halting into verdict `0`, and binary totality turns verdict `0` into the negation of verdict `1`. The resulting self-negating verdict is impossible constructively.]]@*)

(*@unicodemath@[[CompilerCorrect(…) ∧ EvalC(…, C, h) ⇒ ¬ C(diagonal(h)).]]@*)

Theorem evaluator_relative_nonclosure :
  forall (out : OutputRelation)
         (halt : HaltingRelation)
         (query : QueryCoding)
         (diagonal : DiagonalCompiler)
         (C : Code -> Prop)
         (h : Code),
    CompilerCorrect out halt query diagonal ->
    EvalC out halt query C h ->
    ~ C (diagonal h).
Proof.
  intros out halt query diagonal C h Hcompiler Heval Hin.
  destruct Heval as [Htotal Hcorrect].
  specialize (Hcorrect (diagonal h) (diagonal h) Hin).
  specialize (Hcompiler h (diagonal h) Htotal).
  pose proof
    (tot2_zero_iff_not_one
       out h (query (diagonal h) (diagonal h)) Htotal)
    as Hbinary.
  assert
    (Hcycle :
       out h (query (diagonal h) (diagonal h)) 1 <->
       ~ out h (query (diagonal h) (diagonal h)) 1).
  {
    split.
    - intro Hone.
      apply Hbinary.
      apply Hcompiler.
      apply Hcorrect.
      exact Hone.
    - intro Hnot_one.
      apply Hcorrect.
      apply Hcompiler.
      apply Hbinary.
      exact Hnot_one.
  }
  destruct Hcycle as [Hpositive Hnegative].
  assert
    (Hnot : ~ out h (query (diagonal h) (diagonal h)) 1).
  {
    intro Hone.
    exact (Hpositive Hone Hone).
  }
  exact (Hnot (Hnegative Hnot)).
Qed.

(*@section@[[DIAGONALLY CLOSED DOMAINS]]@*)

(*@inline@[[If `C` contains the diagonal compiler product of every evaluator correct on `C`, then no individual evaluator can satisfy `EvalC` on that domain.]]@*)

Theorem diagonally_closed_domain_excludes_evaluator :
  forall (out : OutputRelation)
         (halt : HaltingRelation)
         (query : QueryCoding)
         (diagonal : DiagonalCompiler)
         (C : Code -> Prop),
    CompilerCorrect out halt query diagonal ->
    EvaluatorDiagonalClosure out halt query diagonal C ->
    forall h : Code,
      ~ EvalC out halt query C h.
Proof.
  intros out halt query diagonal C Hcompiler Hclosed h Heval.
  pose proof
    (evaluator_relative_nonclosure
       out halt query diagonal C h Hcompiler Heval)
    as Houtside.
  apply Houtside.
  exact (Hclosed h Heval).
Qed.

(*@inline@[[The pointwise exclusion immediately rules out the existence of any total binary evaluator correct on a diagonally closed domain.]]@*)

(*@unicodemath@[[CompilerCorrect(…) ∧ EvaluatorDiagonalClosure(…, C)]][[⇒ ¬ ∃ h, EvalC(…, C, h).]]@*)

Theorem no_total_evaluator_on_diagonally_closed_domain :
  forall (out : OutputRelation)
         (halt : HaltingRelation)
         (query : QueryCoding)
         (diagonal : DiagonalCompiler)
         (C : Code -> Prop),
    CompilerCorrect out halt query diagonal ->
    EvaluatorDiagonalClosure out halt query diagonal C ->
    ~ exists h : Code,
        EvalC out halt query C h.
Proof.
  intros out halt query diagonal C Hcompiler Hclosed [h Heval].
  exact
    (diagonally_closed_domain_excludes_evaluator
       out halt query diagonal C Hcompiler Hclosed h Heval).
Qed.
