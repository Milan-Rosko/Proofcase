(*L002_00_Premise.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / L002_00_Premise                          │
└──────────────────────────────────────────────────────────────────────────────┘
  TRIVIAL FIXED-POINT LEMMA — PREMISE

  Premise layer for L002/TRIVIAL FIXED-POINT LEMMA. We define a minimal
  implicational object language and its bare constructive derivability
  judgment. The semantic layer built above this syntax will interpret
  implication as a proof-relevant function over future contexts, rather than
  merely copying the constructors of bare derivability. Reflection and
  reification will exhibit constructive validity as a fixed point of semantic
  presentation.

*)

From Stdlib Require Export Lists.List.
From Stdlib Require Export Strings.String.

Export ListNotations.
Global Open Scope string_scope.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               OBJECT LANGUAGE                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Inductive Form : Type :=
| Atom : nat -> Form
| Impl : Form -> Form -> Form.

Definition Ctx := list Form.

Record NamedHyp : Type := mkNamedHyp {
  hyp_name : string;
  hyp_form : Form
}.

Definition NCtx := list NamedHyp.

Fixpoint erase_ctx (Gamma : NCtx) : Ctx :=
  match Gamma with
  | nil => nil
  | h :: Gamma' => hyp_form h :: erase_ctx Gamma'
  end.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           BARE CONSTRUCTIVE PROOFS                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Inductive Has : Ctx -> Form -> Type :=
| has_here :
    forall Gamma A,
      Has (A :: Gamma) A
| has_there :
    forall Gamma A B,
      Has Gamma A ->
      Has (B :: Gamma) A.

Inductive Bare : Ctx -> Form -> Type :=
| bare_hyp :
    forall Gamma A,
      Has Gamma A ->
      Bare Gamma A
| bare_intro :
    forall Gamma A B,
      Bare (A :: Gamma) B ->
      Bare Gamma (Impl A B)
| bare_elim :
    forall Gamma A B,
      Bare Gamma (Impl A B) ->
      Bare Gamma A ->
      Bare Gamma B.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                     CONTEXT EXTENSION AND STRUCTURALITY                      │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A future context preserves every hypothesis available now.
│          This is the accessibility relation used by the Kripke
│          semantics.
│
*)

Definition CtxExt (Gamma Delta : Ctx) : Type :=
  forall A, Has Gamma A -> Has Delta A.

Definition ctx_ext_refl : forall Gamma, CtxExt Gamma Gamma :=
  fun Gamma A h => h.

Definition ctx_ext_trans :
  forall Gamma Delta Theta,
    CtxExt Gamma Delta -> CtxExt Delta Theta -> CtxExt Gamma Theta :=
  fun Gamma Delta Theta e1 e2 A h => e2 A (e1 A h).

Definition ctx_ext_push :
  forall Gamma A,
    CtxExt Gamma (A :: Gamma) :=
  fun Gamma A B h => has_there Gamma B A h.

Definition ctx_ext_under :
  forall Gamma Delta A,
    CtxExt Gamma Delta -> CtxExt (A :: Gamma) (A :: Delta).
Proof.
  intros Gamma Delta A e B h.
  inversion h; subst.
  - apply has_here.
  - apply has_there.
    apply e.
    assumption.
Defined.

Fixpoint bare_weaken {Gamma A}
    (p : Bare Gamma A)
    : forall Delta,
        CtxExt Gamma Delta ->
        Bare Delta A.
Proof.
  destruct p as [Gamma A h | Gamma A B p' | Gamma A B p_imp p_arg].
  - intros Delta e.
    exact (bare_hyp Delta A (e A h)).
  - intros Delta e.
    apply bare_intro.
    exact (@bare_weaken _ _ p' (A :: Delta) (ctx_ext_under Gamma Delta A e)).
  - intros Delta e.
    exact
      (bare_elim Delta A B
         (@bare_weaken _ _ p_imp Delta e)
         (@bare_weaken _ _ p_arg Delta e)).
Defined.
