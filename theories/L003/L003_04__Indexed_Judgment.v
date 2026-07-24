(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Indexed-judgment layer for L003. We separate a token that returns an externally assigned machine label from the additional proposition that this label denotes the active evaluator. Successful checking of the assigned label therefore does not silently establish operational identity.]]@*)

(*@doc.pl@[[The equality model isolates the exact binding question. A concrete mismatched configuration proves that assigned-label checking alone does not entail active-evaluator binding. The bound-evaluator theorem then grants binding explicitly and shows that evaluator-relative nonclosure remains in force.]]@*)

(*@head.end@*)

From L003 Require Export L003_02__Evaluator_Relative_Nonclosure.

(*@section@[[ASSIGNED AND ACTIVE LABELS]]@*)

(*@inline@[[An indexed self-configuration stores the active evaluator label separately from the label assigned to the self token.]]@*)

Record IndexedSelfConfiguration : Type :=
  Build_Indexed_Self_Configuration
  {
    active_evaluator : Code;
    assigned_self_code : Code
  }.

(*@inline@[[The token returns the externally assigned label from its configuration.]]@*)

Definition self_token_result
    (configuration : IndexedSelfConfiguration) : Code :=
  assigned_self_code configuration.

(*@inline@[[`SelfTokenChecks` records agreement with the assigned label; because `self_token_result` is defined by that projection, this judgment always checks.]]@*)

Definition SelfTokenChecks
    (configuration : IndexedSelfConfiguration) : Prop :=
  self_token_result configuration = assigned_self_code configuration.

(*@inline@[[`SelfTokenBound` is the additional identity proposition: the returned label equals the active evaluator label.]]@*)

Definition SelfTokenBound
    (configuration : IndexedSelfConfiguration) : Prop :=
  self_token_result configuration = active_evaluator configuration.

(*@inline@[[A witnessed self judgment contains both successful assigned-label checking and explicit active-evaluator binding.]]@*)

Definition WitnessedSelfJudgment
    (configuration : IndexedSelfConfiguration) : Prop :=
  SelfTokenChecks configuration /\ SelfTokenBound configuration.

(*@inline@[[Every indexed self token checks against the label from which its result is defined.]]@*)

Theorem indexed_self_token_always_checks :
  forall configuration : IndexedSelfConfiguration,
    SelfTokenChecks configuration.
Proof.
  intro configuration.
  reflexivity.
Qed.

(*@section@[[CHECKING DOES NOT SUPPLY BINDING]]@*)

(*@inline@[[The configuration with active label `0` and assigned label `1` is a concrete countermodel to the claim that successful checking always supplies active-evaluator binding.]]@*)

(*@unicodemath@[[¬ (∀ configuration, SelfTokenChecks(configuration)]][[⇒ SelfTokenBound(configuration)).]]@*)

Theorem indexed_self_checking_does_not_supply_binding :
  ~ (forall configuration : IndexedSelfConfiguration,
       SelfTokenChecks configuration ->
       SelfTokenBound configuration).
Proof.
  intro Hsupplies.
  pose
    (mismatch :=
       Build_Indexed_Self_Configuration 0 1).
  assert (Hchecks : SelfTokenChecks mismatch).
  {
    apply indexed_self_token_always_checks.
  }
  specialize (Hsupplies mismatch Hchecks).
  unfold SelfTokenBound, self_token_result in Hsupplies.
  discriminate.
Qed.

(*@inline@[[A witnessed self judgment exposes its explicit binding component.]]@*)

Theorem witnessed_self_judgment_exposes_binding :
  forall configuration : IndexedSelfConfiguration,
    WitnessedSelfJudgment configuration ->
    SelfTokenBound configuration.
Proof.
  intros configuration [_ Hbound].
  exact Hbound.
Qed.

(*@inline@[[Conversely, supplying the binding proposition completes the witnessed judgment because assigned-label checking is automatic.]]@*)

Theorem supplied_binding_completes_indexed_judgment :
  forall configuration : IndexedSelfConfiguration,
    SelfTokenBound configuration ->
    WitnessedSelfJudgment configuration.
Proof.
  intros configuration Hbound.
  split.
  - apply indexed_self_token_always_checks.
  - exact Hbound.
Qed.

(*@section@[[BOUND EVALUATORS]]@*)

(*@inline@[[`BoundEvaluator` combines the explicit self-binding proposition with evaluator correctness at the active evaluator label.]]@*)

Definition BoundEvaluator
    (out : OutputRelation)
    (halt : HaltingRelation)
    (query : QueryCoding)
    (C : Code -> Prop)
    (configuration : IndexedSelfConfiguration) : Prop :=
  SelfTokenBound configuration /\
  EvalC out halt query C (active_evaluator configuration).

(*@inline@[[Active-label binding and evaluator-relative nonclosure coexist: once the active evaluator satisfies `EvalC`, its diagonal product lies outside the correctness domain.]]@*)

(*@unicodemath@[[CompilerCorrect(…) ∧ BoundEvaluator(…, C, configuration)]][[⇒ ¬ C(diagonal(active_evaluator(configuration))).]]@*)

Theorem bound_evaluator_relative_nonclosure :
  forall (out : OutputRelation)
         (halt : HaltingRelation)
         (query : QueryCoding)
         (diagonal : DiagonalCompiler)
         (C : Code -> Prop)
         (configuration : IndexedSelfConfiguration),
    CompilerCorrect out halt query diagonal ->
    BoundEvaluator out halt query C configuration ->
    ~ C (diagonal (active_evaluator configuration)).
Proof.
  intros out halt query diagonal C configuration Hcompiler Hbound.
  destruct Hbound as [_ Heval].
  exact
    (evaluator_relative_nonclosure
       out halt query diagonal C
       (active_evaluator configuration)
       Hcompiler Heval).
Qed.
