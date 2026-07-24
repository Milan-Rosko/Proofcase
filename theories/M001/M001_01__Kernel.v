(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[We compute over the closed implicational-falsity syntax,
finite-list contexts, functional and finite-data axiom sets, logical profiles,
regulator theories, and finite proof scripts declared in `M001_00`.  This
layer adds structural equality, membership, axiom recognition, MP validation,
and the total Boolean checker.  It performs no proof search, semantic
validation, unification, or implicit normalization.]]@*)

(*@doc.pl@[[Every later component is stated as a property of `regulator_theory_check_bool` over the `Formula`, `Context`, `RegulatorTheory`, and `Proof` in the premise layer. The full list of exported names is in README. This layer is the finite syntactic kernel of M001.]]@*)

(*@head.end@*)

From M001 Require Export M001_00_Premises.

From Stdlib Require Import Lia.

(*@section@[[DECIDABLE FORMULA AND CONTEXT STRUCTURE]]@*)

(*@inline@[[`formula_eq_bool` is structural Boolean equality over the formula tree. Its computational form supports direct use under `simpl` / `vm_compute` and keeps the certificate verifier closed.]]@*)

(*@unicodemath@[[formula_eq_bool(A,B) = true  ⇔  A = B]]@*)

Fixpoint formula_eq_bool (A B : Formula) : bool :=
  match A, B with
  | Bot, Bot => true
  | Imp A1 A2, Imp B1 B2 =>
      andb (formula_eq_bool A1 B1) (formula_eq_bool A2 B2)
  | _, _ => false
  end.

(*@inline@[[The two retained equality lemmas are exactly the rewrite hooks
used later: reflexivity and soundness from Boolean equality to formula
equality.]]@*)

Lemma formula_eq_bool_refl_lemma :
  forall A, formula_eq_bool A A = true.
Proof.
  induction A as [|A1 IH1 A2 IH2].
  - reflexivity.
  - simpl.
    rewrite IH1.
    rewrite IH2.
    reflexivity.
Qed.

Lemma formula_eq_bool_true_lemma :
  forall A B, formula_eq_bool A B = true -> A = B.
Proof.
  induction A as [|A1 IH1 A2 IH2]; intros B H.
  - destruct B as [|B1 B2].
    + reflexivity.
    + discriminate H.
  - destruct B as [|B1 B2].
    + discriminate H.
    + simpl in H.
      destruct (formula_eq_bool A1 B1) eqn:Hleft.
      * destruct (formula_eq_bool A2 B2) eqn:Hright.
        -- apply IH1 in Hleft.
           apply IH2 in Hright.
           subst.
           reflexivity.
        -- discriminate H.
      * discriminate H.
Qed.

(*@inline@[[`formula_size` supplies the strict size comparison used by the
syntax contract.]]@*)

(*@unicodemath@[[formula_size(A) ≥ 1]]@*)

Fixpoint formula_size (A : Formula) : nat :=
  match A with
  | Bot => 1
  | Imp B C => 1 + formula_size B + formula_size C
  end.

(*@inline@[[A finite formula cannot be syntactically identical to its own
object-language negation: the latter has strictly larger tree size.  Later
fixed-point claims therefore use accepted mutual implication rather than
formula equality.]]@*)

Theorem formula_not_self_negation :
  forall A : Formula,
    A <> formula_negation A.
Proof.
  intros A Heq.
  pose proof (f_equal formula_size Heq) as Hsize.
  unfold formula_negation in Hsize.
  simpl in Hsize.
  lia.
Qed.

(*@inline@[[`ctx_mem_bool` is the Boolean structural search the checker uses to recognize a line as an assumption. We pair it below with `In`-form soundness and completeness so that downstream proofs can move freely between the computational and propositional readings of context membership.]]@*)

(*@unicodemath@[[ctx_mem_bool(A,Γ) = true ⇔ A ∈ Γ]]@*)

Fixpoint ctx_mem_bool (A : Formula) (Gamma : Context) : bool :=
  match Gamma with
  | nil => false
  | cons B Gamma' =>
      if formula_eq_bool A B then true else ctx_mem_bool A Gamma'
  end.

Lemma ctx_mem_bool_sound_lemma :
  forall A Gamma,
    ctx_mem_bool A Gamma = true ->
    In A Gamma.
Proof.
  intros A Gamma.
  induction Gamma as [|B Gamma' IH]; intro Hmem.
  - simpl in Hmem.
    discriminate Hmem.
  - simpl in Hmem.
    destruct (formula_eq_bool A B) eqn:Heq.
    + apply formula_eq_bool_true_lemma in Heq.
      subst.
      left.
      reflexivity.
    + right.
      apply IH.
      exact Hmem.
Qed.

Lemma ctx_mem_bool_complete_lemma :
  forall A Gamma,
    In A Gamma ->
    ctx_mem_bool A Gamma = true.
Proof.
  intros A Gamma.
  induction Gamma as [|B Gamma' IH]; intro Hin.
  - contradiction.
  - simpl in Hin.
    simpl.
    destruct Hin as [HA | Hin].
    + subst.
      rewrite formula_eq_bool_refl_lemma.
      reflexivity.
    + destruct (formula_eq_bool A B).
      * reflexivity.
      * apply IH.
        exact Hin.
Qed.

(*@inline@[[The three `ctx_extend` lemmas record the elementary list facts the deduction and reductio transformers need when a hypothesis is consed onto a context. They keep assumption handling fully syntactic: `ctx_extend A Γ` reduces to `A :: Γ` and membership is still decided by `ctx_mem_bool`, so no semantic notion of context entailment ever has to enter later proofs.]]@*)

Lemma ctx_mem_bool_extend_self_lemma :
  forall A Gamma,
    ctx_mem_bool A (ctx_extend A Gamma) = true.
Proof.
  intros A Gamma.
  unfold ctx_extend.
  simpl.
  rewrite formula_eq_bool_refl_lemma.
  reflexivity.
Qed.

Lemma ctx_mem_bool_extend_preserve_lemma :
  forall A B Gamma,
    ctx_mem_bool A Gamma = true ->
    ctx_mem_bool A (ctx_extend B Gamma) = true.
Proof.
  intros A B Gamma Hmem.
  unfold ctx_extend.
  simpl.
  destruct (formula_eq_bool A B).
  - reflexivity.
  - exact Hmem.
Qed.

(*@section@[[FINITE AXIOM SETS]]@*)

(*@inline@[[`finite_axiom_set_contains_bool` applies the ordinary context
membership computation to the stored formula list.  The bridge packages that
computation as the functional `AxiomSet` expected by a regulator theory.]]@*)

(*@unicodemath@[[finite_axiom_set_contains_bool(FT,A) = true ⇔ A ∈ finite_axiom_set_formulas(FT)]]@*)

Definition finite_axiom_set_contains_bool
    (FT : FiniteAxiomSet)
    (A : Formula) : bool :=
  ctx_mem_bool A FT.(finite_axiom_set_formulas).

Definition finite_axiom_set_to_axiom_set (FT : FiniteAxiomSet) : AxiomSet :=
  {| axiom_set_contains_bool := finite_axiom_set_contains_bool FT |}.

(*@section@[[SCHEMA RECOGNITION]]@*)

(*@inline@[[The Hilbert axiom recognizers inspect concrete closed formula trees; they do not perform object-level substitution, unification, proof search, or semantic checking. K is recognized syntactically: the head implication's antecedent must coincide with the inner consequent, using `formula_eq_bool` so that every non-K shape returns `false` cleanly for later disjunctive checks.]]@*)

(*@unicodemath@[[K ≔ A → (B → A)]]@*)

Definition k_axiom_bool (phi : Formula) : bool :=
  match phi with
  | Imp A (Imp _ A') => formula_eq_bool A A'
  | _ => false
  end.

(*@inline@[[`k_axiom_bool_complete_lemma` is the rewrite hook for the canonical K instance — every concrete `Imp A (Imp B A)` is recognized. `k_axiom_bool_sound_lemma` is the converse: every formula the recognizer accepts has the K shape. Both directions are exposed because the inductive-derivability layer in `M001_06` needs soundness to unfold a `J_Axiom` line back to its K shape, while the deduction transformer only needs completeness.]]@*)

Lemma k_axiom_bool_complete_lemma :
  forall A B,
    k_axiom_bool (Imp A (Imp B A)) = true.
Proof.
  intros A B.
  simpl.
  apply formula_eq_bool_refl_lemma.
Qed.

Lemma k_axiom_bool_sound_lemma :
  forall F,
    k_axiom_bool F = true ->
    exists A B,
      F = Imp A (Imp B A).
Proof.
  intros F H.
  destruct F as [|A F2]; simpl in H;
    try discriminate H.
  destruct F2 as [|B A']; simpl in H;
    try discriminate H.
  apply formula_eq_bool_true_lemma in H.
  subst A'.
  exists A, B.
  reflexivity.
Qed.

(*@unicodemath@[[S ≔ (A → (B → C)) → ((A → B) → (A → C))]]@*)

(*@inline@[[S is recognized by the same purely syntactic pattern: we destructure the full nested shape and confirm the four shared sub-positions through `formula_eq_bool`. The pattern is intentionally rigid — any S-equivalent rewriting is rejected as the deduction transformer `is what generates the precise shape we accept here.]]@*)

Definition s_axiom_bool (phi : Formula) : bool :=
  match phi with
  | Imp
      (Imp A1 (Imp B1 C1))
      (Imp
        (Imp A2 B2)
        (Imp A3 C2)) =>
      formula_eq_bool A1 A2 &&
      formula_eq_bool A1 A3 &&
      formula_eq_bool B1 B2 &&
      formula_eq_bool C1 C2
  | _ => false
  end.

(*@inline@[[`s_axiom_bool_complete_lemma` and `s_axiom_bool_sound_lemma` mirror the K pair: completeness is the canonical S instance under its public-surface name, and soundness extracts the four parameter formulas from a successful recognizer hit. The soundness proof is the file's longest single Boolean-destructor sequence; downstream layers consume only the existential witness.]]@*)

Lemma s_axiom_bool_complete_lemma :
  forall A B C,
    s_axiom_bool
      (Imp
        (Imp A (Imp B C))
        (Imp
          (Imp A B)
          (Imp A C))) = true.
Proof.
  intros A B C.
  simpl.
  rewrite !formula_eq_bool_refl_lemma.
  reflexivity.
Qed.

Lemma s_axiom_bool_sound_lemma :
  forall F,
    s_axiom_bool F = true ->
    exists A B C,
      F =
        Imp
          (Imp A (Imp B C))
          (Imp
            (Imp A B)
            (Imp A C)).
Proof.
  intros F H.
  destruct F as [|F1 F2]; simpl in H;
    try discriminate H.
  destruct F1 as [|A1 F12]; simpl in H;
    try discriminate H.
  destruct F12 as [|B1 C1]; simpl in H;
    try discriminate H.
  destruct F2 as [|F21 F22]; simpl in H;
    try discriminate H.
  destruct F21 as [|A2 B2]; simpl in H;
    try discriminate H.
  destruct F22 as [|A3 C2]; simpl in H;
    try discriminate H.
  destruct (formula_eq_bool A1 A2) eqn:HA12;
    try discriminate H.
  destruct (formula_eq_bool A1 A3) eqn:HA13;
    try discriminate H.
  destruct (formula_eq_bool B1 B2) eqn:HB;
    try discriminate H.
  destruct (formula_eq_bool C1 C2) eqn:HC;
    try discriminate H.
  apply formula_eq_bool_true_lemma in HA12.
  apply formula_eq_bool_true_lemma in HA13.
  apply formula_eq_bool_true_lemma in HB.
  apply formula_eq_bool_true_lemma in HC.
  subst A2 A3 B2 C2.
  exists A1, B1, C1.
  reflexivity.
Qed.

(*@unicodemath@[[EFQ ≔ ⊥ → A]]@*)

(*@inline@[[EFQ is recognized by the head shape `Bot → _` alone. We isolate it from K and S so that admitting it becomes a single explicit profile choice; the unconditional core never accepts an EFQ instance. No `efq_axiom_bool_sound_lemma` is needed — the recognizer fires exactly when the formula already has the head shape `Imp Bot _`, so the existential witness is the conclusion subterm read off by direct pattern matching, and no downstream layer needs an existential extraction lemma.]]@*)

Definition efq_axiom_bool (phi : Formula) : bool :=
  match phi with
  | Imp Bot _ => true
  | _ => false
  end.

(*@unicodemath@[[available_axiom_bool(R, φ) ≔ logical_axiom_bool(profile_R, φ) ∨ axiom_set_R(φ)]]@*)

(*@inline@[[Logical axioms are selected by the regulator theory's profile and then joined with its axiom set's extra axioms. A line marked `J_Axiom` may therefore appeal to K, S, optionally EFQ, or any formula the regulator theory's axiom set accepts. We mark `available_axiom_bool` as `simpl never` so that later proofs must rewrite through `logical_axiom_bool_*` and axiom-set-side lemmas explicitly, rather than letting `simpl` unfold the disjunction silently.]]@*)

Definition logical_axiom_bool
    (profile : RegulatorLogicProfile)
    (phi : Formula) : bool :=
  match profile with
  | regulator_profile_minimal => k_axiom_bool phi || s_axiom_bool phi
  | regulator_profile_with_efq =>
      k_axiom_bool phi || s_axiom_bool phi || efq_axiom_bool phi
  end.

Definition available_axiom_bool
    (R : RegulatorTheory)
    (phi : Formula) : bool :=
  logical_axiom_bool R.(regulator_theory_profile) phi ||
  R.(regulator_theory_axiom_set).(axiom_set_contains_bool) phi.

Arguments available_axiom_bool : simpl never.

(*@inline@[[The four `logical_axiom_bool_*` and `available_axiom_bool_*` lemmas are the rewrite endpoints downstream proofs use when they need to discharge a `J_Axiom` line for K or S. We state both forms because the deduction transformer emits axioms through `available_axiom_bool`, while several internal correctness arguments work directly against `logical_axiom_bool`.]]@*)

Lemma logical_axiom_bool_k_lemma :
  forall profile A B,
    logical_axiom_bool profile (Imp A (Imp B A)) = true.
Proof.
  intros profile A B.
  destruct profile; simpl.
  - rewrite formula_eq_bool_refl_lemma.
    reflexivity.
  - rewrite formula_eq_bool_refl_lemma.
    reflexivity.
Qed.

Lemma logical_axiom_bool_s_lemma :
  forall profile A B C,
    logical_axiom_bool profile
      (Imp
        (Imp A (Imp B C))
        (Imp
          (Imp A B)
          (Imp A C))) = true.
Proof.
  intros profile A B C.
  destruct profile; unfold logical_axiom_bool.
  - rewrite s_axiom_bool_complete_lemma.
    destruct (k_axiom_bool
      (Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp A C))));
      reflexivity.
  - rewrite s_axiom_bool_complete_lemma.
    destruct (k_axiom_bool
      (Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp A C))));
      reflexivity.
Qed.

Lemma available_axiom_bool_k_lemma :
  forall R A B,
    available_axiom_bool R (Imp A (Imp B A)) = true.
Proof.
  intros R A B.
  unfold available_axiom_bool.
  rewrite logical_axiom_bool_k_lemma.
  reflexivity.
Qed.

Lemma available_axiom_bool_s_lemma :
  forall R A B C,
    available_axiom_bool R
      (Imp
        (Imp A (Imp B C))
        (Imp
          (Imp A B)
          (Imp A C))) = true.
Proof.
  intros R A B C.
  unfold available_axiom_bool.
  rewrite logical_axiom_bool_s_lemma.
  reflexivity.
Qed.

(*@section@[[PROOF SCRIPT ACCESSORS AND THE CHECKER]]@*)

(*@inline@[[`nth_formula` reads the formula at a referenced line, the `pl_*` constructors build raw lines, and `last_formula` exposes the claimed conclusion. We isolate these helpers because every transformer builds proof scripts by direct list construction and reads them back through these same accessors.]]@*)

Definition nth_formula
    (prefix : list ProofLine)
    (i : nat) : option Formula :=
  match nth_error prefix i with
  | Some line => Some line.(line_formula)
  | None => None
  end.

Definition pl_assumption (A : Formula) : ProofLine :=
  {| line_formula := A;
     line_justification := J_Assumption |}.

Definition pl_axiom (A : Formula) : ProofLine :=
  {| line_formula := A;
     line_justification := J_Axiom |}.

Definition pl_mp (A : Formula) (i j : nat) : ProofLine :=
  {| line_formula := A;
     line_justification := J_MP i j |}.

Fixpoint last_formula (p : Proof) : option Formula :=
  match p with
  | nil => None
  | cons line nil => Some line.(line_formula)
  | cons _ p' => last_formula p'
  end.

(*@inline@[[The three Boolean destructors below let later checker proofs unpack a successful conjunction or disjunction without invoking propositional decidability lemmas.]]@*)

Lemma bool_and_true_left_lemma :
  forall a b,
    a && b = true ->
    a = true.
Proof.
  destruct a, b; simpl; intros H; try discriminate; reflexivity.
Qed.

Lemma bool_and_true_right_lemma :
  forall a b,
    a && b = true ->
    b = true.
Proof.
  destruct a, b; simpl; intros H; try discriminate; reflexivity.
Qed.

Lemma bool_or_true_cases_lemma :
  forall a b,
    a || b = true ->
    a = true \/ b = true.
Proof.
  destruct a, b; simpl; intros H; try discriminate; auto.
Qed.

(*@inline@[[MP checking accepts either reference order. A line for `B` is valid when the accepted prefix contains both `C` and `C → B`, regardless of which index is listed first. This is a certificate-format convention only: it adds no logical rule beyond ordinary modus ponens, but makes the two reference positions orientation-insensitive. We expose the two orientations as distinct Boolean predicates so that constructive reductio can pick whichever orientation its generated block emits, without an internal case split.]]@*)

Definition mp_orientation_left_bool
    (Fi Fj target : Formula) : bool :=
  match Fj with
  | Imp C B =>
      formula_eq_bool Fi C && formula_eq_bool B target
  | _ => false
  end.

Definition mp_orientation_right_bool
    (Fi Fj target : Formula) : bool :=
  match Fi with
  | Imp C B =>
      formula_eq_bool C Fj && formula_eq_bool B target
  | _ => false
  end.

Definition mp_valid_bool
    (prefix : list ProofLine)
    (i j : nat)
    (target : Formula) : bool :=
  match nth_formula prefix i, nth_formula prefix j with
  | Some Fi, Some Fj =>
      mp_orientation_left_bool Fi Fj target ||
      mp_orientation_right_bool Fi Fj target
  | _, _ => false
  end.

(*@inline@[[The `mp_valid_bool_*` lemmas package the two orientations as forward rewrites and the reverse as component-extraction facts. Together they expose `mp_valid_bool` as a Prop-level relation without losing the Boolean form: emitters use `mp_valid_bool_direct_lemma` / `mp_valid_bool_reverse_lemma`, while consumers use `mp_valid_bool_components_lemma` or `mp_valid_bool_sound_unordered_lemma` to recover the antecedent and implication that produced a successful MP line.]]@*)

Lemma mp_valid_bool_direct_lemma :
  forall prefix i j C B,
    nth_formula prefix i = Some C ->
    nth_formula prefix j = Some (Imp C B) ->
    mp_valid_bool prefix i j B = true.
Proof.
  intros prefix i j C B Hi Hj.
  unfold mp_valid_bool.
  rewrite Hi, Hj.
  unfold mp_orientation_left_bool.
  rewrite !formula_eq_bool_refl_lemma.
  reflexivity.
Qed.

Lemma mp_valid_bool_reverse_lemma :
  forall prefix i j C B,
    nth_formula prefix i = Some (Imp C B) ->
    nth_formula prefix j = Some C ->
    mp_valid_bool prefix i j B = true.
Proof.
  intros prefix i j C B Hi Hj.
  unfold mp_valid_bool.
  rewrite Hi, Hj.
  unfold mp_orientation_right_bool.
  rewrite !formula_eq_bool_refl_lemma.
  destruct (mp_orientation_left_bool (Imp C B) C B);
    reflexivity.
Qed.

(*@inline@[[The two `Example` lemmas below are worked illustrations of the unordered-MP convention: in a two-line prefix carrying `A` and `A → B` in either order, `mp_valid_bool` accepts the MP line for `B` regardless of which line is referenced first. They are the smallest nontrivial checks exercising both orientations and serve as a reference point for later sanity-test.]]@*)

Example mp_accepts_argument_then_implication :
  forall A B,
    mp_valid_bool
      (cons (pl_assumption A)
        (cons (pl_assumption (Imp A B)) nil))
      0 1 B = true.
Proof.
  intros A B.
  apply mp_valid_bool_direct_lemma with (C := A);
    reflexivity.
Qed.

Example mp_accepts_implication_then_argument :
  forall A B,
    mp_valid_bool
      (cons (pl_assumption (Imp A B))
        (cons (pl_assumption A) nil))
      0 1 B = true.
Proof.
  intros A B.
  apply mp_valid_bool_reverse_lemma with (C := A);
    reflexivity.
Qed.

Lemma mp_valid_bool_components_lemma :
  forall prefix i j target,
    mp_valid_bool prefix i j target = true ->
    exists C,
      (nth_formula prefix i = Some C /\
       nth_formula prefix j = Some (Imp C target)) \/
      (nth_formula prefix i = Some (Imp C target) /\
       nth_formula prefix j = Some C).
Proof.
  intros prefix i j target Hvalid.
  unfold mp_valid_bool in Hvalid.
  destruct (nth_formula prefix i) as [Fi|] eqn:Hi;
    try discriminate.
  destruct (nth_formula prefix j) as [Fj|] eqn:Hj;
    try discriminate.
  apply bool_or_true_cases_lemma in Hvalid.
  destruct Hvalid as [H1 | H2].
  - unfold mp_orientation_left_bool in H1.
    destruct Fj as [|C B]; try discriminate.
    apply bool_and_true_left_lemma in H1 as HC.
    apply bool_and_true_right_lemma in H1 as HB.
    apply formula_eq_bool_true_lemma in HC.
    apply formula_eq_bool_true_lemma in HB.
    subst Fi.
    subst B.
    exists C.
    left.
    split; reflexivity.
  - unfold mp_orientation_right_bool in H2.
    destruct Fi as [|C B]; try discriminate.
    apply bool_and_true_left_lemma in H2 as HC.
    apply bool_and_true_right_lemma in H2 as HB.
    apply formula_eq_bool_true_lemma in HC.
    apply formula_eq_bool_true_lemma in HB.
    subst C.
    subst B.
    exists Fj.
    right.
    split; reflexivity.
Qed.

(*@inline@[[`mp_valid_bool_sound_unordered_lemma` is the public surface name for `mp_valid_bool_components_lemma`: it states the unordered-MP soundness fact directly, that a successful `mp_valid_bool` hit at indices `i, j` produces an antecedent `A` and an implication `A → B` somewhere in the prefix, in *some* orientation. The inductive-derivability layer in  and the regulator in both consume this lemma when they need to recover the two MP premises from a checked line.]]@*)

Lemma mp_valid_bool_sound_unordered_lemma :
  forall prefix i j B,
    mp_valid_bool prefix i j B = true ->
    exists A,
      (nth_formula prefix i = Some A /\
       nth_formula prefix j = Some (Imp A B)) \/
      (nth_formula prefix i = Some (Imp A B) /\
       nth_formula prefix j = Some A).
Proof.
  intros prefix i j B Hvalid.
  apply mp_valid_bool_components_lemma.
  exact Hvalid.
Qed.

(*@inline@[[The checker accepts a line only as a context assumption, an available axiom, or MP from earlier accepted lines, and additionally requires the script to end with the claimed conclusion. `proof_line_valid_bool R Gamma prefix line = true` means `line` is syntactically valid relative to the already accepted prefix and regulator theory `R`. `proof_script_check_from_bool R Gamma prefix p = true` means every line of `p` is valid relative to the accumulated accepted prefix, in proof order. `regulator_theory_check_bool R Gamma p A = true` means `p` is a valid finite proof script in regulator theory `R` and the last formula of `p` is syntactically equal to `A`; empty scripts are rejected because they have no last formula.]]@*)

Definition proof_line_valid_bool
    (R : RegulatorTheory)
    (Gamma : Context)
    (prefix : list ProofLine)
    (line : ProofLine) : bool :=
  let phi := line.(line_formula) in
  match line.(line_justification) with
  | J_Assumption =>
      ctx_mem_bool phi Gamma
  | J_Axiom =>
      available_axiom_bool R phi
  | J_MP i j =>
      Nat.ltb i (length prefix) &&
      Nat.ltb j (length prefix) &&
      mp_valid_bool prefix i j phi
  end.

(*@unicodemath@[[regulator_theory_check_bool : RegulatorTheory → Context → Proof → Formula → bool]]@*)

Fixpoint proof_script_check_from_bool
    (R : RegulatorTheory)
    (Gamma : Context)
    (prefix : list ProofLine)
    (todo : list ProofLine) : bool :=
  match todo with
  | nil => true
  | cons line rest =>
      proof_line_valid_bool R Gamma prefix line &&
      proof_script_check_from_bool R Gamma (prefix ++ cons line nil) rest
  end.

Definition regulator_theory_check_bool
    (R : RegulatorTheory)
    (Gamma : Context)
    (p : Proof)
    (A : Formula) : bool :=
  proof_script_check_from_bool R Gamma nil p &&
  match last_formula p with
  | Some B => formula_eq_bool B A
  | None => false
  end.

(*@inline@[[`regulator_theory_check_empty_false_lemma` records that the empty proof script is rejected on every input.]]@*)

Lemma regulator_theory_check_empty_false_lemma :
  forall R Gamma A,
    regulator_theory_check_bool R Gamma nil A = false.
Proof.
  reflexivity.
Qed.

(*@inline@[[The checker over the finite-data axiom-set interface bridges a `FiniteAxiomSet` value across `finite_axiom_set_to_axiom_set` and runs the underlying `regulator_theory_check_bool`.]]@*)

(*@unicodemath@[[profile, FT; Γ ⊢check[p] A  ≔  finite_axiom_set_check_bool(profile,FT,Γ,p,A) = true]]@*)

Definition finite_axiom_set_to_regulator_theory
    (profile : RegulatorLogicProfile)
    (T : FiniteAxiomSet) : RegulatorTheory :=
  regulator_theory_with_axiom_set profile (finite_axiom_set_to_axiom_set T).

Definition finite_axiom_set_check_bool
    (profile : RegulatorLogicProfile)
    (T : FiniteAxiomSet)
    (Gamma : Context)
    (p : Proof)
    (A : Formula) : bool :=
  regulator_theory_check_bool
    (finite_axiom_set_to_regulator_theory profile T)
    Gamma p A.

(*@inline@[[The closing lemmas split a successful `regulator_theory_check_bool` into its two conjuncts and record the list-index facts needed when the deduction transformer concatenates checked proof fragments. Later checker-correctness theorems compose this finite-script bookkeeping with the `mp_valid_bool_*` lemmas and the `formula_eq_bool` / `ctx_mem_bool` specifications above.]]@*)

Lemma regulator_theory_check_true_lines_lemma :
  forall R Gamma p A,
    regulator_theory_check_bool R Gamma p A = true ->
    proof_script_check_from_bool R Gamma nil p = true.
Proof.
  intros R Gamma p A H.
  unfold regulator_theory_check_bool in H.
  exact (bool_and_true_left_lemma _ _ H).
Qed.

Lemma regulator_theory_check_true_last_lemma :
  forall R Gamma p A,
    regulator_theory_check_bool R Gamma p A = true ->
    last_formula p = Some A.
Proof.
  intros R Gamma p A H.
  unfold regulator_theory_check_bool in H.
  pose proof (bool_and_true_right_lemma _ _ H) as Hlast.
  destruct (last_formula p) as [B|] eqn:Hlf.
  - apply formula_eq_bool_true_lemma in Hlast.
    subst.
    reflexivity.
  - discriminate Hlast.
Qed.

(*@inline@[[`last_formula_has_line_lemma` and `regulator_theory_check_true_has_last_lemma` together expose the witness behind a successful regulator_theory_check_bool: a checked script for `A` actually contains a proof line whose claimed formula is `A` (its last line).]]@*)

Lemma last_formula_has_line_lemma :
  forall p A,
    last_formula p = Some A ->
    exists line,
      In line p /\
      line_formula line = A.
Proof.
  induction p as [|line p IH]; intros A Hlast.
  - discriminate Hlast.
  - destruct p as [|line' p'].
    + simpl in Hlast.
      inversion Hlast.
      subst.
      exists line.
      split.
      * left.
        reflexivity.
      * reflexivity.
    + simpl in Hlast.
      destruct (IH A Hlast) as [last_line [Hin Hformula]].
      exists last_line.
      split.
      * right.
        exact Hin.
      * exact Hformula.
Qed.

Lemma regulator_theory_check_true_has_last_lemma :
  forall R Gamma p A,
    regulator_theory_check_bool R Gamma p A = true ->
    exists line,
      In line p /\
      line_formula line = A.
Proof.
  intros R Gamma p A Hcheck.
  apply last_formula_has_line_lemma.
  apply regulator_theory_check_true_last_lemma with
    (R := R)
    (Gamma := Gamma).
  exact Hcheck.
Qed.

Lemma nth_formula_some_ltb_lemma :
  forall prefix i F,
    nth_formula prefix i = Some F ->
    Nat.ltb i (length prefix) = true.
Proof.
  induction prefix as [|line prefix IH]; intros i F Hnth.
  - destruct i; discriminate Hnth.
  - destruct i as [|i'].
    + reflexivity.
    + simpl in Hnth.
      simpl.
      exact (IH i' F Hnth).
Qed.

Lemma nth_formula_app_left_lemma :
  forall prefix suffix i F,
    nth_formula prefix i = Some F ->
    nth_formula (prefix ++ suffix) i = Some F.
Proof.
  induction prefix as [|line prefix IH]; intros suffix i F Hnth.
  - destruct i; discriminate Hnth.
  - destruct i as [|i'].
    + simpl in Hnth.
      simpl.
      exact Hnth.
    + simpl in Hnth.
      simpl.
      exact (IH suffix i' F Hnth).
Qed.

Lemma nth_formula_app_length_plus_lemma :
  forall prefix suffix n,
    nth_formula (prefix ++ suffix) (length prefix + n) =
    nth_formula suffix n.
Proof.
  induction prefix as [|line prefix IH]; intros suffix n.
  - reflexivity.
  - simpl.
    exact (IH suffix n).
Qed.

Lemma proof_script_check_from_app_lemma :
  forall R Gamma prefix p q,
    proof_script_check_from_bool R Gamma prefix (p ++ q) =
    proof_script_check_from_bool R Gamma prefix p &&
    proof_script_check_from_bool R Gamma (prefix ++ p) q.
Proof.
  intros R Gamma prefix p.
  revert prefix.
  induction p as [|line p IH]; intros prefix q.
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl.
    rewrite IH.
    rewrite <- app_assoc.
    simpl.
    destruct (proof_line_valid_bool R Gamma prefix line);
      destruct (proof_script_check_from_bool R Gamma (prefix ++ cons line nil) p);
      reflexivity.
Qed.

(*@inline@[[`proof_script_check_from_app_left_lemma` is the left-projection of `proof_script_check_from_app_lemma`: a successful `proof_script_check_from_bool` on `p ++ q` against any prefix forces a successful check on `p` alone.]]@*)

Lemma proof_script_check_from_app_left_lemma :
  forall R Gamma prefix p q,
    proof_script_check_from_bool R Gamma prefix (p ++ q) = true ->
    proof_script_check_from_bool R Gamma prefix p = true.
Proof.
  intros R Gamma prefix p q Hcheck.
  rewrite proof_script_check_from_app_lemma in Hcheck.
  apply bool_and_true_left_lemma in Hcheck.
  exact Hcheck.
Qed.

Lemma proof_script_check_append_true_lemma :
  forall R Gamma output block,
    proof_script_check_from_bool R Gamma nil output = true ->
    proof_script_check_from_bool R Gamma output block = true ->
    proof_script_check_from_bool R Gamma nil (output ++ block) = true.
Proof.
  intros R Gamma output block Hout Hblock.
  rewrite proof_script_check_from_app_lemma.
  simpl.
  rewrite Hout.
  rewrite Hblock.
  reflexivity.
Qed.
