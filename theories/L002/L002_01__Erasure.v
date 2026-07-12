(*L002_01__Erasure.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / L002_01__Erasure                         │
└──────────────────────────────────────────────────────────────────────────────┘
  TRIVIAL FIXED-POINT LEMMA — SEMANTIC REIFICATION

  Semantic elimination for the Trivial Fixed-Point Lemma. Formulas are
  interpreted in a proof-relevant Kripke semantics whose worlds are bare
  contexts. An atom is evidence at the present world. An implication is a
  polymorphic operation that transports to every future world and maps
  semantic evidence of its antecedent to semantic evidence of its consequent.
  Reflection and reification show that this genuinely semantic function-space
  presentation has a bare constructive witness.

*)

From L002 Require Export L002_00_Premise.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       PROOF-RELEVANT KRIPKE SEMANTICS                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Fixpoint Forces (Gamma : Ctx) (A : Form) : Type :=
  match A with
  | Atom n => Bare Gamma (Atom n)
  | Impl A B =>
      forall Delta,
        CtxExt Gamma Delta ->
        Forces Delta A ->
        Forces Delta B
  end.

(*
│
│          A semantic proof combines an explanatory presentation with
│          proof-relevant forcing evidence. The description is
│          intentionally irrelevant to validity; the evidence is
│          semantic because implication is represented by a function
│          acting uniformly over all future contexts.
│
*)

Record Semantic (Gamma : NCtx) (A : Form) : Type := mkSemantic {
  semantic_description : string;
  semantic_evidence : Forces (erase_ctx Gamma) A
}.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          REFLECTION AND REIFICATION                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Fixpoint reflect (Gamma : Ctx) (A : Form)
    : Bare Gamma A -> Forces Gamma A :=
  match A as A0 return Bare Gamma A0 -> Forces Gamma A0 with
  | Atom n => fun p => p
  | Impl A B =>
      fun p Delta e sA =>
        reflect Delta B
          (bare_elim Delta A B
             (bare_weaken p Delta e)
             (reify Delta A sA))
  end
with reify (Gamma : Ctx) (A : Form)
    : Forces Gamma A -> Bare Gamma A :=
  match A as A0 return Forces Gamma A0 -> Bare Gamma A0 with
  | Atom n => fun s => s
  | Impl A B =>
      fun s =>
        bare_intro Gamma A B
          (reify (A :: Gamma) B
             (s (A :: Gamma)
                (ctx_ext_push Gamma A)
                (reflect (A :: Gamma) A
                   (bare_hyp (A :: Gamma) A
                      (has_here Gamma A)))))
  end.

Definition erase_semantic_proof {Gamma A}
    (p : Semantic Gamma A)
    : Bare (erase_ctx Gamma) A :=
  reify (erase_ctx Gamma) A (semantic_evidence Gamma A p).

Theorem semantic_erasure_preserves_validity :
  forall Gamma A,
    Semantic Gamma A ->
    Bare (erase_ctx Gamma) A.
Proof.
  intros Gamma A p.
  exact (erase_semantic_proof p).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             SEMANTIC OPERATIONS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition forces_monotone :
  forall Gamma Delta A,
    CtxExt Gamma Delta ->
    Forces Gamma A ->
    Forces Delta A :=
  fun Gamma Delta A e s =>
    reflect Delta A (bare_weaken (reify Gamma A s) Delta e).

Definition semantic_apply {Gamma A B}
    (sf : Forces Gamma (Impl A B))
    (sa : Forces Gamma A)
    : Forces Gamma B :=
  sf Gamma (ctx_ext_refl Gamma) sa.

Definition semantic_identity (Gamma : Ctx) (A : Form)
    : Forces Gamma (Impl A A) :=
  fun Delta e sA => sA.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           PRESENTATION INVARIANCE                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Fixpoint rename_ctx (f : string -> string) (Gamma : NCtx) : NCtx :=
  match Gamma with
  | nil => nil
  | h :: Gamma' =>
      mkNamedHyp (f (hyp_name h)) (hyp_form h) :: rename_ctx f Gamma'
  end.

Fixpoint erase_ctx_rename
    (f : string -> string)
    (Gamma : NCtx)
    : erase_ctx (rename_ctx f Gamma) = erase_ctx Gamma :=
  match Gamma with
  | nil => eq_refl
  | h :: Gamma' =>
      f_equal
        (fun Delta => hyp_form h :: Delta)
        (erase_ctx_rename f Gamma')
  end.

Definition transport {X : Type}
    (P : X -> Type) {x y : X} (e : x = y) (u : P x) : P y :=
  match e in _ = y return P y with
  | eq_refl => u
  end.

Definition rename_semantic_proof
    (f : string -> string)
    {Gamma A}
    (p : Semantic Gamma A)
    : Semantic (rename_ctx f Gamma) A :=
  mkSemantic
    (rename_ctx f Gamma)
    A
    (semantic_description Gamma A p)
    (transport
       (fun Delta => Forces Delta A)
       (eq_sym (erase_ctx_rename f Gamma))
       (semantic_evidence Gamma A p)).

Lemma reify_transport :
  forall Gamma Delta A
         (e : Gamma = Delta)
         (s : Forces Delta A),
    transport
      (fun Theta => Bare Theta A)
      e
      (reify Gamma A
         (transport
            (fun Theta => Forces Theta A)
            (eq_sym e)
            s))
    =
    reify Delta A s.
Proof.
  intros Gamma Delta A e s.
  destruct e.
  reflexivity.
Qed.

Theorem semantic_renaming_is_invisible :
  forall (f : string -> string) Gamma A (p : Semantic Gamma A),
    transport
      (fun Delta => Bare Delta A)
      (erase_ctx_rename f Gamma)
      (erase_semantic_proof (rename_semantic_proof f p))
    =
    erase_semantic_proof p.
Proof.
  intros f Gamma A p.
  unfold erase_semantic_proof, rename_semantic_proof.
  simpl.
  apply reify_transport.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                   EXAMPLES                                   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition semantic_ground_ctx : NCtx :=
  mkNamedHyp "semantic_ground" (Atom 0) :: nil.

Definition semantic_identity_presentation :
  Semantic nil (Impl (Atom 0) (Atom 0)) :=
  mkSemantic
    nil
    (Impl (Atom 0) (Atom 0))
    "identity means that evidence is preserved"
    (semantic_identity nil (Atom 0)).

Example reified_semantic_identity :
  Bare nil (Impl (Atom 0) (Atom 0)).
Proof.
  exact (erase_semantic_proof semantic_identity_presentation).
Qed.

Definition semantic_ground_presentation :
  Semantic semantic_ground_ctx (Atom 0) :=
  mkSemantic
    semantic_ground_ctx
    (Atom 0)
    "the named ground is available at the present world"
    (bare_hyp (Atom 0 :: nil) (Atom 0) (has_here nil (Atom 0))).

Example reified_semantic_ground :
  Bare (erase_ctx semantic_ground_ctx) (Atom 0).
Proof.
  exact (erase_semantic_proof semantic_ground_presentation).
Qed.
