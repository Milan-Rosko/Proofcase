(*M001_02__Abstraction.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / M001_02__Abstraction                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Checked deduction abstraction for regulator theories. `M001_00_Premises`
  supplies the primitive vocabulary (`Formula`, `Context`, `RegulatorTheory`,
  and `Proof`), and `M001_01__Kernel` supplies the Boolean checker over that
  vocabulary. This file proves the first abstraction principle above the
  checker: a checked proof script for `B` under `A :: Γ` can be compiled into
  a checked proof script for `A → B` under `Γ`. The compilation is a
  computable function on finite proof scripts; no semantic notion of validity
  is used at any stage. The primary user-facing theorem is
  `regulator_theory_deduction_checked`;
  `regulator_theory_deduction_minimal_checked` is the EFQ-free
  specialization.

  The construction is line-local and switches on the source line's
  `Justification`. A `J_Assumption` line whose formula equals the discharged
  hypothesis `A` emits `deduction_identity_block_from`, proving `A → A`; an
  inherited `J_Assumption` line emits `deduction_assumption_lift_block_from`;
  a `J_Axiom` line emits `deduction_axiom_lift_block_from`; and a `J_MP` line
  emits `deduction_mp_lift_block_from`, which uses S to re-derive the MP step
  under the discharged context. An index map records, for each consumed
  source line at position `i`, the output index of the generated line whose
  formula is `A → φ_i`; this map is what allows source MP references to be
  replayed in the target proof without rebuilding from scratch. The public
  exports are the general deduction theorem and its minimal-profile
  specialization; everything else (`*_block_*`, `DeductionState`,
  `deduction_transform_*`, `deduction_index_map_verified`, and
  `deduction_state_verified`) is internal scaffolding consumed only inside
  this file. This file does not introduce semantic validity, external model
  theory, modal provability, arithmetic coding, diagonal obstruction, or
  self-recognition.

*)

From M001 Require Export M001_01__Kernel.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        CHECKED DEDUCTION CONSTRUCTION                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `k_axiom_formula` and `s_axiom_formula` package the
│          canonical K and S instances as functions on the relevant
│          formula parameters. We name them so that the Hilbert blocks
│          below read as small algebraic expressions in K and S rather
│          than as nested `Imp` trees, and so that the
│          recognizer-level lemmas
│          `available_axiom_bool_k_formula_lemma` / `_S_formula` give
│          one-step rewrites every block-checking proof can rely on.
│
*)

(*                    k_axiom_formula(A, B) ≔ A → (B → A)                     *)
(*       s_axiom_formula(A, B, C) ≔ (A → (B → C)) → ((A → B) → (A → C))       *)

Definition k_axiom_formula (A B : Formula) : Formula :=
  Imp A (Imp B A).

Definition s_axiom_formula (A B C : Formula) : Formula :=
  Imp
    (Imp A (Imp B C))
    (Imp
      (Imp A B)
      (Imp A C)).

Lemma available_axiom_bool_k_formula_lemma :
  forall R A B,
    available_axiom_bool R (k_axiom_formula A B) = true.
Proof.
  intros R A B.
  unfold k_axiom_formula.
  apply available_axiom_bool_k_lemma.
Qed.

Lemma available_axiom_bool_s_formula_lemma :
  forall R A B C,
    available_axiom_bool R (s_axiom_formula A B C) = true.
Proof.
  intros R A B C.
  unfold s_axiom_formula.
  apply available_axiom_bool_s_lemma.
Qed.

(*
│
│          The four deduction block constructors are finite Hilbert
│          templates emitted by
│          `regulator_theory_deduction_transform`; each checked
│          fragment ends with the formula needed at that source
│          position, and its `base` parameter records the absolute
│          output index where the block starts.
│          `deduction_identity_block_from` is the five-line K/S proof
│          of `A → A` used for the discharged hypothesis itself; it
│          consults neither `Γ` nor the external axiom set, and its
│          reverse-orientation MP lines are accepted by `M001_01`'s
│          unordered `mp_valid_bool`.
│
*)

(*                    K(A,A), K(A,A→A), S(A,A→A,A) ⇒ A → A                    *)

Definition deduction_identity_block_from (base : nat) (A : Formula) : Proof :=
  cons (pl_axiom (k_axiom_formula A A))
  (cons (pl_axiom (k_axiom_formula A (Imp A A)))
  (cons (pl_axiom (s_axiom_formula A (Imp A A) A))
  (cons (pl_mp
          (Imp (Imp A (Imp A A)) (Imp A A))
          (base + 2)
          (base + 1))
  (cons (pl_mp
          (Imp A A)
          (base + 3)
          (base + 0))
  nil)))).

(*
│
│          `deduction_assumption_lift_block_from` and
│          `deduction_axiom_lift_block_from` lift a context assumption
│          (resp. an available axiom) `C` to `A → C` by following K
│          with one MP. The two blocks differ only in the
│          justification of their first line; isolating them as two
│          constructors keeps the case split explicit at the
│          transformer call site.
│
*)

(*                             C, K(C,A) ⇒ A → C                              *)

Definition deduction_assumption_lift_block_from
    (base : nat)
    (A C : Formula) : Proof :=
  cons (pl_assumption C)
  (cons (pl_axiom (k_axiom_formula C A))
  (cons (pl_mp (Imp A C) (base + 0) (base + 1))
  nil)).

Definition deduction_axiom_lift_block_from
    (base : nat)
    (A C : Formula) : Proof :=
  cons (pl_axiom C)
  (cons (pl_axiom (k_axiom_formula C A))
  (cons (pl_mp (Imp A C) (base + 0) (base + 1))
  nil)).

(*
│
│          `deduction_mp_lift_block_from` is the heart of the
│          transformer: a source MP from `φ_i` and `φ_j` becomes an
│          output MP of `A → φ_i` and `A → φ_j` mediated by S. The two
│          indices `idx_imp` and `idx_arg` point into the output proof
│          — they are the entries the index map has already recorded
│          for the implication and its antecedent.
│
*)

(*                    S(A,C,B), A → (C → B), A → C ⇒ A → B                    *)

Definition deduction_mp_lift_block_from
    (base : nat)
    (A C B : Formula)
    (idx_imp idx_arg : nat) : Proof :=
  cons (pl_axiom (s_axiom_formula A C B))
  (cons (pl_mp
          (Imp (Imp A C) (Imp A B))
          (base + 0)
          idx_imp)
  (cons (pl_mp
          (Imp A B)
          (base + 1)
          idx_arg)
  nil)).

(*
│
│          `DeductionState` carries the transformer's working state:
│          the output proof built so far, and the index map that, for
│          each already-processed source line at position `i`, records
│          the output index of the line whose formula is `A → φ_i`.
│          Pairing the two means each new source line can be
│          transformed by reading at most two map entries, regardless
│          of how far back the source MP references reach.
│
*)

(*                  idx[i]=k ∧ source[i]=φ ⇒ output[k]=A → φ                  *)

Record DeductionState : Type := {
  deduction_state_output : Proof;
  deduction_state_index_map : list nat
}.

Definition deduction_state_empty : DeductionState :=
  {| deduction_state_output := nil;
     deduction_state_index_map := nil |}.

(*
│
│          `deduction_state_next_index` is the absolute output
│          position at which the next block will start. We expose it
│          as a small helper because every block constructor needs it
│          both as its `base` parameter and as the offset into the new
│          index-map entry.
│
*)

Definition deduction_state_next_index (st : DeductionState) : nat :=
  length st.(deduction_state_output).

(*
│
│          `deduction_state_append_block` appends a generated block to
│          the output proof and records the absolute index of its
│          final line — the one whose formula is `A → φ` for the
│          source line just transformed — into the index map. The four
│          `deduction_state_append_*` wrappers below specialize this
│          to the four block shapes, each passing the offset within
│          the block at which the final line sits.
│
*)

Definition deduction_state_append_block
    (st : DeductionState)
    (block : Proof)
    (final_offset : nat) : DeductionState :=
  let base := deduction_state_next_index st in
  {| deduction_state_output := st.(deduction_state_output) ++ block;
     deduction_state_index_map := st.(deduction_state_index_map) ++ cons (base + final_offset) nil |}.

Definition deduction_state_append_identity
    (A : Formula)
    (st : DeductionState) : DeductionState :=
  deduction_state_append_block st (deduction_identity_block_from (deduction_state_next_index st) A) 4.

Definition deduction_state_append_assumption_lift
    (A C : Formula)
    (st : DeductionState) : DeductionState :=
  deduction_state_append_block st
    (deduction_assumption_lift_block_from (deduction_state_next_index st) A C)
    2.

Definition deduction_state_append_axiom_lift
    (A C : Formula)
    (st : DeductionState) : DeductionState :=
  deduction_state_append_block st
    (deduction_axiom_lift_block_from (deduction_state_next_index st) A C)
    2.

Definition deduction_state_append_mp_lift
    (A C B : Formula)
    (idx_imp idx_arg : nat)
    (st : DeductionState) : DeductionState :=
  deduction_state_append_block st
    (deduction_mp_lift_block_from (deduction_state_next_index st) A C B idx_imp idx_arg)
    2.

(*
│
│          `deduction_transform_mp_line` looks up the source formulas
│          at the two MP indices, consults the index map for their
│          already-transformed counterparts, and emits a
│          `deduction_mp_lift_block_from` block in whichever of the
│          two MP orientations succeeds. The two orientations
│          correspond exactly to `mp_orientation_left_bool` and
│          `mp_orientation_right_bool` of `M001_01`'s `mp_valid_bool`
│          — that is the unordered-MP certificate convention. On any
│          input that already passed `mp_valid_bool` for the source
│          line at least one orientation succeeds, by
│          `mp_valid_bool_components_lemma` /
│          `mp_valid_bool_sound_unordered_lemma`; we nevertheless keep
│          a structural fallback to `deduction_state_append_identity`
│          so that `deduction_transform_mp_line` is total on every
│          `DeductionState`, which lets the surrounding fixpoint stay
│          strictly structural without a partial-match obligation. The
│          fallback is unreachable on checked input and never appears
│          in any reachable certificate.
│
*)

Definition deduction_transform_mp_line
    (A target : Formula)
    (source_prefix : list ProofLine)
    (i j : nat)
    (st : DeductionState) : DeductionState :=
  match nth_formula source_prefix i,
        nth_formula source_prefix j,
        nth_error st.(deduction_state_index_map) i,
        nth_error st.(deduction_state_index_map) j with
  | Some Fi, Some Fj, Some idx_i, Some idx_j =>
      if mp_orientation_left_bool Fi Fj target
      then deduction_state_append_mp_lift A Fi target idx_j idx_i st
      else if mp_orientation_right_bool Fi Fj target
           then deduction_state_append_mp_lift A Fj target idx_i idx_j st
           else deduction_state_append_identity A st
  | _, _, _, _ =>
      deduction_state_append_identity A st
  end.

(*
│
│          `deduction_transform_line` is the single-line dispatcher. A
│          discharged hypothesis (`J_Assumption` whose formula is
│          exactly `A`) emits the identity block; an inherited
│          assumption emits the assumption-lift block; an axiom emits
│          the axiom-lift block; and an MP emits the MP-lift block
│          through `deduction_transform_mp_line`. The case split is by
│          source justification, mirroring the checker in `M001_01`.
│
*)

Definition deduction_transform_line
    (A : Formula)
    (source_prefix : list ProofLine)
    (line : ProofLine)
    (st : DeductionState) : DeductionState :=
  let phi := line.(line_formula) in
  match line.(line_justification) with
  | J_Assumption =>
      if formula_eq_bool phi A
      then deduction_state_append_identity A st
      else deduction_state_append_assumption_lift A phi st
  | J_Axiom =>
      deduction_state_append_axiom_lift A phi st
  | J_MP i j =>
      deduction_transform_mp_line A phi source_prefix i j st
  end.

(*
│
│          `deduction_transform_lines` walks the source script left to
│          right, threading the `DeductionState` through
│          `deduction_transform_line` while extending the source
│          prefix at every step. Concatenation is on the right so that
│          source MP references — which point backward into the prefix
│          already consumed — read naturally from the index map.
│
*)

Fixpoint deduction_transform_lines
    (A : Formula)
    (source_prefix : list ProofLine)
    (todo : list ProofLine)
    (st : DeductionState) : DeductionState :=
  match todo with
  | nil => st
  | cons line rest =>
      let st' := deduction_transform_line A source_prefix line st in
      deduction_transform_lines A (source_prefix ++ cons line nil) rest st'
  end.

(*
│
│          `regulator_theory_deduction_transform A p` runs the
│          transformer from the empty state and returns only the
│          produced output proof. The index map is internal to the
│          construction; downstream layers see only this function and
│          the deduction theorem below.
│
*)

(*    deduction_transform(A,p) ≔ regulator_theory_deduction_transform(A,p)    *)

Definition regulator_theory_deduction_transform (A : Formula) (p : Proof) : Proof :=
  (deduction_transform_lines A nil p deduction_state_empty).(deduction_state_output).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                BLOCK CHECKING                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The block-checking lemmas provide the local certificate
│          arithmetic behind the transformer: each generated template
│          checks when appended after an already accepted prefix.
│          `regulator_theory_deduction_cbn` is the corresponding
│          reduction tactic; its unfolding list is explicit so that
│          proofs reduce the checker stack, line constructors, K/S
│          formula constructors, block templates, and proof-script
│          accessors without unfolding the index-map machinery or the
│          dispatcher.
│
*)

Ltac regulator_theory_deduction_cbn :=
  cbn [
    regulator_theory_check_bool proof_script_check_from_bool proof_line_valid_bool line_formula line_justification
    pl_axiom pl_assumption pl_mp k_axiom_formula s_axiom_formula
    deduction_identity_block_from
    deduction_assumption_lift_block_from deduction_axiom_lift_block_from
    deduction_mp_lift_block_from last_formula nth_formula
  ].

(*
│
│          The four `*_block_check` lemmas — one per template —
│          discharge the block's `proof_script_check_from_bool`
│          obligation against any prefix of the right length. They are
│          the only proofs in this file that have to inspect MP
│          orientation: they call `mp_valid_bool_reverse_lemma` for
│          the K/S-built blocks and `mp_valid_bool_direct_lemma` for
│          the simpler lift blocks. Once these four are established,
│          the block-checking API becomes orientation-agnostic.
│
*)

(*           checked_from([],output) ∧ checked_from(output,block) ⇒           *)
(*                      checked_from([],output ⧺ block)                       *)

Lemma deduction_identity_block_check_lemma :
  forall R Gamma prefix A,
    proof_script_check_from_bool R Gamma prefix
      (deduction_identity_block_from (length prefix) A) = true.
Proof.
  intros R Gamma prefix A.
  unfold deduction_identity_block_from.
  regulator_theory_deduction_cbn.
  rewrite available_axiom_bool_k_formula_lemma.
  rewrite available_axiom_bool_k_formula_lemma.
  rewrite available_axiom_bool_s_formula_lemma.
  set (l0 := pl_axiom (k_axiom_formula A A)).
  set (l1 := pl_axiom (k_axiom_formula A (Imp A A))).
  set (l2 := pl_axiom (s_axiom_formula A (Imp A A) A)).
  assert (H2 :
    nth_formula (((prefix ++ cons l0 nil) ++ cons l1 nil) ++ cons l2 nil)
      (length prefix + 2) =
    Some (s_axiom_formula A (Imp A A) A)).
  {
    subst l0 l1 l2.
    repeat rewrite <- app_assoc.
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  assert (H1 :
    nth_formula (((prefix ++ cons l0 nil) ++ cons l1 nil) ++ cons l2 nil)
      (length prefix + 1) =
    Some (k_axiom_formula A (Imp A A))).
  {
    subst l0 l1 l2.
    repeat rewrite <- app_assoc.
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  rewrite (nth_formula_some_ltb_lemma _ _ _ H2).
  rewrite (nth_formula_some_ltb_lemma _ _ _ H1).
  rewrite (mp_valid_bool_reverse_lemma
    (((prefix ++ cons l0 nil) ++ cons l1 nil) ++ cons l2 nil)
    (length prefix + 2)
    (length prefix + 1)
    (Imp A (Imp (Imp A A) A))
    (Imp (Imp A (Imp A A)) (Imp A A))).
  2: exact H2.
  2: exact H1.
  regulator_theory_deduction_cbn.
  set (l3 := pl_mp
    (Imp (Imp A (Imp A A)) (Imp A A))
    (length prefix + 2)
    (length prefix + 1)).
  assert (H3 :
    nth_formula
      ((((prefix ++ cons l0 nil) ++ cons l1 nil) ++ cons l2 nil) ++
        cons l3 nil)
      (length prefix + 3) =
    Some (Imp (Imp A (Imp A A)) (Imp A A))).
  {
    subst l0 l1 l2 l3.
    repeat rewrite <- app_assoc.
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  assert (H0 :
    nth_formula
      ((((prefix ++ cons l0 nil) ++ cons l1 nil) ++ cons l2 nil) ++
        cons l3 nil)
      (length prefix + 0) =
    Some (k_axiom_formula A A)).
  {
    subst l0 l1 l2 l3.
    repeat rewrite <- app_assoc.
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  rewrite (nth_formula_some_ltb_lemma _ _ _ H3).
  rewrite (nth_formula_some_ltb_lemma _ _ _ H0).
  rewrite (mp_valid_bool_reverse_lemma
    ((((prefix ++ cons l0 nil) ++ cons l1 nil) ++ cons l2 nil) ++
      cons l3 nil)
    (length prefix + 3)
    (length prefix + 0)
    (Imp A (Imp A A))
    (Imp A A)).
  2: exact H3.
  2: exact H0.
  regulator_theory_deduction_cbn.
  reflexivity.
Qed.

Lemma deduction_assumption_lift_block_check_lemma :
  forall R Gamma prefix A C,
    ctx_mem_bool C Gamma = true ->
    proof_script_check_from_bool R Gamma prefix
      (deduction_assumption_lift_block_from (length prefix) A C) = true.
Proof.
  intros R Gamma prefix A C Hmem.
  unfold deduction_assumption_lift_block_from.
  regulator_theory_deduction_cbn.
  rewrite Hmem.
  rewrite available_axiom_bool_k_formula_lemma.
  set (l0 := pl_assumption C).
  set (l1 := pl_axiom (k_axiom_formula C A)).
  assert (H0 :
    nth_formula ((prefix ++ cons l0 nil) ++ cons l1 nil)
      (length prefix + 0) =
    Some C).
  {
    subst l0 l1.
    repeat rewrite <- app_assoc.
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  assert (H1 :
    nth_formula ((prefix ++ cons l0 nil) ++ cons l1 nil)
      (length prefix + 1) =
    Some (k_axiom_formula C A)).
  {
    subst l0 l1.
    repeat rewrite <- app_assoc.
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  rewrite (nth_formula_some_ltb_lemma _ _ _ H0).
  rewrite (nth_formula_some_ltb_lemma _ _ _ H1).
  rewrite (mp_valid_bool_direct_lemma
    ((prefix ++ cons l0 nil) ++ cons l1 nil)
    (length prefix + 0)
    (length prefix + 1)
    C
    (Imp A C)).
  2: exact H0.
  2: exact H1.
  regulator_theory_deduction_cbn.
  reflexivity.
Qed.

Lemma deduction_axiom_lift_block_check_lemma :
  forall R Gamma prefix A C,
    available_axiom_bool R C = true ->
    proof_script_check_from_bool R Gamma prefix
      (deduction_axiom_lift_block_from (length prefix) A C) = true.
Proof.
  intros R Gamma prefix A C Haxiom.
  unfold deduction_axiom_lift_block_from.
  regulator_theory_deduction_cbn.
  rewrite Haxiom.
  rewrite available_axiom_bool_k_formula_lemma.
  set (l0 := pl_axiom C).
  set (l1 := pl_axiom (k_axiom_formula C A)).
  assert (H0 :
    nth_formula ((prefix ++ cons l0 nil) ++ cons l1 nil)
      (length prefix + 0) =
    Some C).
  {
    subst l0 l1.
    repeat rewrite <- app_assoc.
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  assert (H1 :
    nth_formula ((prefix ++ cons l0 nil) ++ cons l1 nil)
      (length prefix + 1) =
    Some (k_axiom_formula C A)).
  {
    subst l0 l1.
    repeat rewrite <- app_assoc.
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  rewrite (nth_formula_some_ltb_lemma _ _ _ H0).
  rewrite (nth_formula_some_ltb_lemma _ _ _ H1).
  rewrite (mp_valid_bool_direct_lemma
    ((prefix ++ cons l0 nil) ++ cons l1 nil)
    (length prefix + 0)
    (length prefix + 1)
    C
    (Imp A C)).
  2: exact H0.
  2: exact H1.
  regulator_theory_deduction_cbn.
  reflexivity.
Qed.

Lemma deduction_mp_lift_block_check_lemma :
  forall R Gamma prefix A C B idx_imp idx_arg,
    nth_formula prefix idx_imp = Some (Imp A (Imp C B)) ->
    nth_formula prefix idx_arg = Some (Imp A C) ->
    proof_script_check_from_bool R Gamma prefix
      (deduction_mp_lift_block_from
        (length prefix) A C B idx_imp idx_arg) = true.
Proof.
  intros R Gamma prefix A C B idx_imp idx_arg Himp Harg.
  unfold deduction_mp_lift_block_from.
  regulator_theory_deduction_cbn.
  rewrite available_axiom_bool_s_formula_lemma.
  assert (HS :
    nth_formula
      (prefix ++ cons (pl_axiom (s_axiom_formula A C B)) nil)
      (length prefix + 0) =
    Some (s_axiom_formula A C B)).
  {
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  pose proof (nth_formula_app_left_lemma
    prefix (cons (pl_axiom (s_axiom_formula A C B)) nil)
    idx_imp (Imp A (Imp C B)) Himp) as Himp1.
  rewrite (nth_formula_some_ltb_lemma _ _ _ HS).
  rewrite (nth_formula_some_ltb_lemma _ _ _ Himp1).
  rewrite (mp_valid_bool_reverse_lemma
    (prefix ++ cons (pl_axiom (s_axiom_formula A C B)) nil)
    (length prefix + 0)
    idx_imp
    (Imp A (Imp C B))
    (Imp (Imp A C) (Imp A B))).
  2: exact HS.
  2: exact Himp1.
  regulator_theory_deduction_cbn.
  set (l1 := pl_mp
    (Imp (Imp A C) (Imp A B))
    (length prefix + 0)
    idx_imp).
  assert (Hmid :
    nth_formula
      ((prefix ++ cons (pl_axiom (s_axiom_formula A C B)) nil) ++
        cons l1 nil)
      (length prefix + 1) =
    Some (Imp (Imp A C) (Imp A B))).
  {
    subst l1.
    repeat rewrite <- app_assoc.
    rewrite nth_formula_app_length_plus_lemma.
    reflexivity.
  }
  pose proof (nth_formula_app_left_lemma
    prefix (cons (pl_axiom (s_axiom_formula A C B)) nil)
    idx_arg (Imp A C) Harg) as Harg1.
  pose proof (nth_formula_app_left_lemma
    (prefix ++ cons (pl_axiom (s_axiom_formula A C B)) nil)
    (cons l1 nil)
    idx_arg (Imp A C) Harg1) as Harg2.
  rewrite (nth_formula_some_ltb_lemma _ _ _ Hmid).
  rewrite (nth_formula_some_ltb_lemma _ _ _ Harg2).
  rewrite (mp_valid_bool_reverse_lemma
    ((prefix ++ cons (pl_axiom (s_axiom_formula A C B)) nil) ++ cons l1 nil)
    (length prefix + 1)
    idx_arg
    (Imp A C)
    (Imp A B)).
  2: exact Hmid.
  2: exact Harg2.
  regulator_theory_deduction_cbn.
  reflexivity.
Qed.

(*
│
│          The four `*_block_final` lemmas read off the formula at the
│          *final* line of each generated block. Together with the
│          `*_block_check` lemmas above they exhaust what the rest of
│          this file needs to know about block shapes: block checking
│          gives `proof_script_check_from_bool`, finality gives
│          `nth_formula` at the final-offset position, and the
│          `last_formula_*` lemmas below extend that to the proof's
│          last line.
│
*)

Lemma deduction_identity_block_final_lemma :
  forall output A,
    nth_formula
      (output ++ deduction_identity_block_from (length output) A)
      (length output + 4) =
    Some (Imp A A).
Proof.
  intros output A.
  rewrite nth_formula_app_length_plus_lemma.
  reflexivity.
Qed.

Lemma deduction_assumption_lift_block_final_lemma :
  forall output A C,
    nth_formula
      (output ++ deduction_assumption_lift_block_from (length output) A C)
      (length output + 2) =
    Some (Imp A C).
Proof.
  intros output A C.
  rewrite nth_formula_app_length_plus_lemma.
  reflexivity.
Qed.

Lemma deduction_axiom_lift_block_final_lemma :
  forall output A C,
    nth_formula
      (output ++ deduction_axiom_lift_block_from (length output) A C)
      (length output + 2) =
    Some (Imp A C).
Proof.
  intros output A C.
  rewrite nth_formula_app_length_plus_lemma.
  reflexivity.
Qed.

Lemma deduction_mp_lift_block_final_lemma :
  forall output A C B idx_imp idx_arg,
    nth_formula
      (output ++
        deduction_mp_lift_block_from
          (length output) A C B idx_imp idx_arg)
      (length output + 2) =
    Some (Imp A B).
Proof.
  intros output A C B idx_imp idx_arg.
  rewrite nth_formula_app_length_plus_lemma.
  reflexivity.
Qed.

(*
│
│          `last_formula_app_nonempty_lemma` extends a non-empty
│          suffix's final formula through a left prefix. The
│          append-state proofs use it directly for the generated
│          Hilbert blocks, avoiding separate one-use wrapper lemmas
│          for each block shape.
│
*)

Lemma last_formula_app_nonempty_lemma :
  forall p q F,
    last_formula q = Some F ->
    last_formula (p ++ q) = Some F.
Proof.
  induction p as [|line p IH]; intros q F Hlast.
  - exact Hlast.
  - destruct p as [|line' p'].
    + destruct q as [|qline q'].
      * discriminate Hlast.
      * simpl.
        exact Hlast.
    + simpl.
      apply IH.
      exact Hlast.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          DEDUCTION STATE INVARIANTS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `deduction_index_map_verified` is the structural invariant
│          relating the source prefix already consumed to the index
│          map already recorded. For each source line at position `i`,
│          the map's `i`-th entry must be an output index `k` such
│          that the output's `k`-th line carries formula `A → φ_i`.
│          The inductive shape — co-traversal of `source` and
│          `index_map` — is what makes the four
│          `deduction_state_append_*_verified` proofs go through with
│          a single extension step each.
│
*)

(* deduction_index_map_verified(A, source, output, idx) ⇔ ∀ i, source_i = φ ⇒ *)
(*                           output_idx_i = (A → φ)                           *)

Fixpoint deduction_index_map_verified
    (A : Formula)
    (source : list ProofLine)
    (output : Proof)
    (index_map : list nat) : Prop :=
  match source, index_map with
  | nil, nil => True
  | cons line source', cons k index_map' =>
      nth_formula output k = Some (Imp A line.(line_formula)) /\
      deduction_index_map_verified A source' output index_map'
  | _, _ => False
  end.

(*
│
│          `deduction_last_formula_verified` is the per-call invariant
│          on the proof's last line: whenever the source has a final
│          formula `B`, the output has final formula `A → B`. We
│          separate it from the index-map invariant because the
│          deduction theorem's final rewrite needs only this one fact
│          about the last line, not the full per-position
│          correspondence.
│
*)

Definition deduction_last_formula_verified
    (A : Formula)
    (source : list ProofLine)
    (output : Proof) : Prop :=
  match last_formula source with
  | Some B => last_formula output = Some (Imp A B)
  | None => last_formula output = None
  end.

(*
│
│          `deduction_state_verified` is the conjunction the
│          transformer maintains across every
│          `deduction_transform_line` step: the output is checked, the
│          index map is consistent with the source consumed so far,
│          and the last lines correspond. Bundling the three as a
│          record lets the four `deduction_state_append_*_verified`
│          lemmas below state preservation as a single
│          hypothesis-and-conclusion shape.
│
*)

(*verified(st) ≔ checked(output(st)) ∧ idx-correct(st) ∧ last(output(st)) = A *)
(*                               → last(source)                               *)

Record deduction_state_verified
    (R : RegulatorTheory)
    (Gamma : Context)
    (A : Formula)
    (source : list ProofLine)
    (st : DeductionState) : Prop := mk_deduction_state_verified {
  deduction_state_checked :
    proof_script_check_from_bool R Gamma nil st.(deduction_state_output) = true;
  deduction_state_index_map_verified :
    deduction_index_map_verified A source st.(deduction_state_output) st.(deduction_state_index_map);
  deduction_state_last_formula_verified :
    deduction_last_formula_verified A source st.(deduction_state_output)
}.

(*
│
│          `deduction_index_map_verified_app_output_lemma` says
│          appending lines to the output preserves the invariant — the
│          entries already recorded still point at the same formulas.
│          `deduction_index_map_verified_extend_lemma` adds a fresh
│          source line together with a fresh map entry.
│          `deduction_index_map_verified_nth_formula_lemma` reads an
│          output index back out for any source position, and is the
│          lookup the MP case of
│          `deduction_transform_line_verified_lemma` uses.
│
*)

Lemma deduction_index_map_verified_app_output_lemma :
  forall A source output index_map suffix,
    deduction_index_map_verified A source output index_map ->
    deduction_index_map_verified A source (output ++ suffix) index_map.
Proof.
  induction source as [|line source IH];
    intros output index_map suffix Hok;
    destruct index_map as [|k index_map'];
    simpl in *; try contradiction; try exact I.
  destruct Hok as [Hhead Htail].
  split.
  - exact (nth_formula_app_left_lemma output suffix k
      (Imp A (line_formula line)) Hhead).
  - exact (IH output index_map' suffix Htail).
Qed.

Lemma deduction_index_map_verified_extend_lemma :
  forall A source output index_map suffix line k,
    deduction_index_map_verified A source output index_map ->
    nth_formula (output ++ suffix) k =
      Some (Imp A line.(line_formula)) ->
    deduction_index_map_verified A
      (source ++ cons line nil)
      (output ++ suffix)
      (index_map ++ cons k nil).
Proof.
  induction source as [|head source IH];
    intros output index_map suffix line k Hok Hnew;
    destruct index_map as [|k0 index_map'];
    simpl in *; try contradiction.
  - split.
    + exact Hnew.
    + exact I.
  - destruct Hok as [Hhead Htail].
    split.
    + exact (nth_formula_app_left_lemma output suffix k0
        (Imp A (line_formula head)) Hhead).
    + exact (IH output index_map' suffix line k Htail Hnew).
Qed.

Lemma deduction_index_map_verified_nth_formula_lemma :
  forall A source output index_map i C,
    deduction_index_map_verified A source output index_map ->
    nth_formula source i = Some C ->
    exists k,
      nth_error index_map i = Some k /\
      nth_formula output k = Some (Imp A C).
Proof.
  induction source as [|line source IH];
    intros output index_map i C Hok Hnth;
    destruct index_map as [|k index_map'];
    simpl in *; try contradiction.
  - destruct i; discriminate Hnth.
  - destruct Hok as [Hhead Htail].
    destruct i as [|i'].
    + simpl in Hnth.
      inversion Hnth; subst C.
      exists k.
      split.
      * reflexivity.
      * exact Hhead.
    + exact (IH output index_map' i' C Htail Hnth).
Qed.

(*
│
│          `last_formula_app_single_lemma` is the elementary fact that
│          consing a single line on the right of a finite list moves
│          the last-line accessor onto that line. The four
│          `deduction_state_append_*_verified` proofs all use it to
│          reduce `last_formula (source ++ cons line nil)` to
│          `line.(line_formula)`.
│
*)

Lemma last_formula_app_single_lemma :
  forall source line,
    last_formula (source ++ cons line nil) =
    Some line.(line_formula).
Proof.
  induction source as [|head source IH]; intro line.
  - reflexivity.
  - destruct source as [|head' source'].
    + reflexivity.
    + simpl.
      exact (IH line).
Qed.

(*
│
│          The four `deduction_state_append_*_verified` lemmas are the
│          per-block preservation steps. Each says: starting from a
│          state that satisfies `deduction_state_verified` for the
│          prefix already consumed, appending the corresponding block
│          produces a state that satisfies `deduction_state_verified`
│          for the prefix extended with one more source line. They are
│          the only place this file uses the block-checking and
│          block-final lemmas together; downstream proofs go through
│          `deduction_transform_line_verified_lemma` and never
│          re-examine block shape.
│
*)

Lemma deduction_state_append_identity_verified_lemma :
  forall R Gamma A source st line,
    deduction_state_verified R Gamma A source st ->
    line.(line_formula) = A ->
    deduction_state_verified R Gamma A
      (source ++ cons line nil)
      (deduction_state_append_identity A st).
Proof.
  intros R Gamma A source st line Hst Hline.
  destruct Hst as [Hchecked Hmap Hlast].
  unfold deduction_state_append_identity, deduction_state_append_block, deduction_state_next_index.
  constructor.
  - apply proof_script_check_append_true_lemma.
    + exact Hchecked.
    + apply deduction_identity_block_check_lemma.
  - apply deduction_index_map_verified_extend_lemma.
    + exact Hmap.
    + rewrite Hline.
      apply deduction_identity_block_final_lemma.
  - unfold deduction_last_formula_verified.
    rewrite last_formula_app_single_lemma.
    rewrite Hline.
    apply last_formula_app_nonempty_lemma.
    reflexivity.
Qed.

Lemma deduction_state_append_assumption_lift_verified_lemma :
  forall R Gamma A source st line,
    deduction_state_verified R Gamma A source st ->
    ctx_mem_bool line.(line_formula) Gamma = true ->
    deduction_state_verified R Gamma A
      (source ++ cons line nil)
      (deduction_state_append_assumption_lift A line.(line_formula) st).
Proof.
  intros R Gamma A source st line Hst Hmem.
  destruct Hst as [Hchecked Hmap Hlast].
  unfold deduction_state_append_assumption_lift, deduction_state_append_block, deduction_state_next_index.
  constructor.
  - apply proof_script_check_append_true_lemma.
    + exact Hchecked.
    + apply deduction_assumption_lift_block_check_lemma.
      exact Hmem.
  - apply deduction_index_map_verified_extend_lemma.
    + exact Hmap.
    + apply deduction_assumption_lift_block_final_lemma.
  - unfold deduction_last_formula_verified.
    rewrite last_formula_app_single_lemma.
    apply last_formula_app_nonempty_lemma.
    reflexivity.
Qed.

Lemma deduction_state_append_axiom_lift_verified_lemma :
  forall R Gamma A source st line,
    deduction_state_verified R Gamma A source st ->
    available_axiom_bool R line.(line_formula) = true ->
    deduction_state_verified R Gamma A
      (source ++ cons line nil)
      (deduction_state_append_axiom_lift A line.(line_formula) st).
Proof.
  intros R Gamma A source st line Hst Haxiom.
  destruct Hst as [Hchecked Hmap Hlast].
  unfold deduction_state_append_axiom_lift, deduction_state_append_block, deduction_state_next_index.
  constructor.
  - apply proof_script_check_append_true_lemma.
    + exact Hchecked.
    + apply deduction_axiom_lift_block_check_lemma.
      exact Haxiom.
  - apply deduction_index_map_verified_extend_lemma.
    + exact Hmap.
    + apply deduction_axiom_lift_block_final_lemma.
  - unfold deduction_last_formula_verified.
    rewrite last_formula_app_single_lemma.
    apply last_formula_app_nonempty_lemma.
    reflexivity.
Qed.

Lemma deduction_state_append_mp_lift_verified_lemma :
  forall R Gamma A source st line C B idx_imp idx_arg,
    deduction_state_verified R Gamma A source st ->
    line.(line_formula) = B ->
    nth_formula st.(deduction_state_output) idx_imp = Some (Imp A (Imp C B)) ->
    nth_formula st.(deduction_state_output) idx_arg = Some (Imp A C) ->
    deduction_state_verified R Gamma A
      (source ++ cons line nil)
      (deduction_state_append_mp_lift A C B idx_imp idx_arg st).
Proof.
  intros R Gamma A source st line C B idx_imp idx_arg
    Hst Hline Himp Harg.
  destruct Hst as [Hchecked Hmap Hlast].
  unfold deduction_state_append_mp_lift, deduction_state_append_block, deduction_state_next_index.
  constructor.
  - apply proof_script_check_append_true_lemma.
    + exact Hchecked.
    + apply deduction_mp_lift_block_check_lemma; assumption.
  - apply deduction_index_map_verified_extend_lemma.
    + exact Hmap.
    + rewrite Hline.
      apply deduction_mp_lift_block_final_lemma.
  - unfold deduction_last_formula_verified.
    rewrite last_formula_app_single_lemma.
    rewrite Hline.
    apply last_formula_app_nonempty_lemma.
    reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       DEDUCTION TRANSFORM PRESERVATION                       │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `mp_orientation_left_formula_lemma` and
│          `mp_orientation_right_formula_lemma` invert the two
│          MP-orientation predicates of `M001_01`. They convert a
│          successful Boolean orientation check into the equality the
│          MP case of `deduction_transform_line_verified_lemma` needs
│          to substitute for the source formulas before applying
│          `deduction_state_append_mp_lift_verified_lemma`.
│
*)

Lemma mp_orientation_left_formula_lemma :
  forall Fi Fj target,
    mp_orientation_left_bool Fi Fj target = true ->
    Fj = Imp Fi target.
Proof.
  intros Fi Fj target H.
  unfold mp_orientation_left_bool in H.
  destruct Fj as [|C B]; try discriminate.
  apply bool_and_true_left_lemma in H as HC.
  apply bool_and_true_right_lemma in H as HB.
  apply formula_eq_bool_true_lemma in HC.
  apply formula_eq_bool_true_lemma in HB.
  subst.
  reflexivity.
Qed.

Lemma mp_orientation_right_formula_lemma :
  forall Fi Fj target,
    mp_orientation_right_bool Fi Fj target = true ->
    Fi = Imp Fj target.
Proof.
  intros Fi Fj target H.
  unfold mp_orientation_right_bool in H.
  destruct Fi as [|C B]; try discriminate.
  apply bool_and_true_left_lemma in H as HC.
  apply bool_and_true_right_lemma in H as HB.
  apply formula_eq_bool_true_lemma in HC.
  apply formula_eq_bool_true_lemma in HB.
  subst.
  reflexivity.
Qed.

(*
│
│          `deduction_transform_line_verified_lemma` is the one-step
│          preservation lemma for the transformer: a
│          `deduction_state_verified` for the prefix already consumed,
│          together with a `proof_line_valid_bool` for the next source
│          line, yields a `deduction_state_verified` for the prefix
│          extended by that line. The proof follows the three source
│          justifications, with the assumption case splitting into
│          discharged and inherited assumptions. The MP case is the
│          only one that consumes the index-map lookup:
│          `deduction_index_map_verified_nth_formula_lemma` recovers
│          the output positions of the implication and antecedent from
│          the source MP indices, after which the orientation lemmas
│          align the formulas.
│
*)

(*  verified(st,source) ∧ valid(line) ⇒ verified(transform_line(A,line,st),   *)
(*                              source ⧺ [line])                              *)

Lemma deduction_transform_line_verified_lemma :
  forall R Gamma A source_prefix line st,
    deduction_state_verified R Gamma A source_prefix st ->
    proof_line_valid_bool R (ctx_extend A Gamma) source_prefix line = true ->
    deduction_state_verified R Gamma A
      (source_prefix ++ cons line nil)
      (deduction_transform_line A source_prefix line st).
Proof.
  intros R Gamma A source_prefix line st Hst Hline.
  destruct line as [phi just].
  simpl in *.
  destruct just as [| |i j].
  - unfold deduction_transform_line.
    simpl.
    unfold proof_line_valid_bool in Hline.
    simpl in Hline.
    unfold ctx_extend in Hline.
    simpl in Hline.
    destruct (formula_eq_bool phi A) eqn:Heq.
    + apply formula_eq_bool_true_lemma in Heq.
      exact (deduction_state_append_identity_verified_lemma
        R Gamma A source_prefix st
        {| line_formula := phi; line_justification := J_Assumption |}
        Hst Heq).
    + exact (deduction_state_append_assumption_lift_verified_lemma
        R Gamma A source_prefix st
        {| line_formula := phi; line_justification := J_Assumption |}
        Hst Hline).
  - unfold deduction_transform_line.
    simpl.
    unfold proof_line_valid_bool in Hline.
    simpl in Hline.
    exact (deduction_state_append_axiom_lift_verified_lemma
      R Gamma A source_prefix st
      {| line_formula := phi; line_justification := J_Axiom |}
      Hst Hline).
  - unfold proof_line_valid_bool in Hline.
    simpl in Hline.
    pose proof (bool_and_true_right_lemma _ _ Hline) as Hvalid.
    unfold deduction_transform_line, deduction_transform_mp_line.
    simpl.
    destruct Hst as [Hchecked Hmap Hlast].
    destruct (nth_formula source_prefix i) as [Fi|] eqn:Hi.
    2:{
      unfold mp_valid_bool in Hvalid.
      rewrite Hi in Hvalid.
      discriminate Hvalid.
    }
    destruct (nth_formula source_prefix j) as [Fj|] eqn:Hj.
    2:{
      unfold mp_valid_bool in Hvalid.
      rewrite Hi, Hj in Hvalid.
      discriminate Hvalid.
    }
    destruct
      (deduction_index_map_verified_nth_formula_lemma A source_prefix (deduction_state_output st)
        (deduction_state_index_map st) i Fi Hmap Hi)
      as [idx_i [Hidx_i Hout_i]].
    destruct
      (deduction_index_map_verified_nth_formula_lemma A source_prefix (deduction_state_output st)
        (deduction_state_index_map st) j Fj Hmap Hj)
      as [idx_j [Hidx_j Hout_j]].
    rewrite Hidx_i, Hidx_j.
    destruct (mp_orientation_left_bool Fi Fj phi) eqn:Horient1.
    + pose proof (mp_orientation_left_formula_lemma Fi Fj phi Horient1) as HFj.
      subst Fj.
      apply (deduction_state_append_mp_lift_verified_lemma
        R Gamma A source_prefix st
        {| line_formula := phi; line_justification := J_MP i j |}
        Fi phi idx_j idx_i).
      * constructor; assumption.
      * reflexivity.
      * exact Hout_j.
      * exact Hout_i.
    + destruct (mp_orientation_right_bool Fi Fj phi) eqn:Horient2.
      * pose proof (mp_orientation_right_formula_lemma Fi Fj phi Horient2) as HFi.
        subst Fi.
        apply (deduction_state_append_mp_lift_verified_lemma
          R Gamma A source_prefix st
          {| line_formula := phi; line_justification := J_MP i j |}
          Fj phi idx_i idx_j).
        -- constructor; assumption.
        -- reflexivity.
        -- exact Hout_i.
        -- exact Hout_j.
      * unfold mp_valid_bool in Hvalid.
        rewrite Hi, Hj in Hvalid.
        rewrite Horient1, Horient2 in Hvalid.
        discriminate Hvalid.
Qed.

(*
│
│          `deduction_transform_lines_verified_lemma` is the iterated
│          form: starting from a `deduction_state_verified` for any
│          source prefix and any checked todo, the transformer's final
│          state satisfies `deduction_state_verified` for the
│          concatenation. The proof is a straightforward induction on
│          `todo` that reuses
│          `deduction_transform_line_verified_lemma` at every step.
│
*)

Lemma deduction_transform_lines_verified_lemma :
  forall R Gamma A source_prefix todo st,
    deduction_state_verified R Gamma A source_prefix st ->
    proof_script_check_from_bool R (ctx_extend A Gamma) source_prefix todo = true ->
    deduction_state_verified R Gamma A
      (source_prefix ++ todo)
      (deduction_transform_lines A source_prefix todo st).
Proof.
  intros R Gamma A source_prefix todo.
  revert source_prefix.
  induction todo as [|line rest IH]; intros source_prefix st Hst Hcheck.
  - simpl in Hcheck.
    rewrite app_nil_r.
    exact Hst.
  - simpl in Hcheck.
    pose proof (bool_and_true_left_lemma _ _ Hcheck) as Hline.
    pose proof (bool_and_true_right_lemma _ _ Hcheck) as Hrest.
    simpl.
    pose proof
      (deduction_transform_line_verified_lemma R Gamma A source_prefix line st Hst Hline)
      as Hst_line.
    specialize (IH (source_prefix ++ cons line nil)
      (deduction_transform_line A source_prefix line st)
      Hst_line Hrest).
    rewrite <- app_assoc in IH.
    simpl in IH.
    exact IH.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          CHECKED DEDUCTION THEOREM                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `regulator_theory_deduction_checked` is the checker-level
│          deduction theorem and the primary user-facing export of
│          this file: from a checked script for `B` under `A :: Γ`,
│          the transformer computes a checked script for `A → B` under
│          `Γ`. The proof packages
│          `deduction_transform_lines_verified_lemma` against the
│          empty initial state and rewrites the
│          `deduction_last_formula_verified` invariant against the
│          source's claimed conclusion, which `M001_01`'s
│          `regulator_theory_check_true_last_lemma` recovers from the
│          input regulator_theory_check_bool.
│
*)

(*     R; A::Γ ⊢check[p] B ⇒ R; Γ ⊢check[deduction_transform(A,p)] A → B      *)

Theorem regulator_theory_deduction_checked :
  forall R Gamma A B p,
    regulator_theory_check_bool R (ctx_extend A Gamma) p B = true ->
    regulator_theory_check_bool R Gamma (regulator_theory_deduction_transform A p) (Imp A B) = true.
Proof.
  intros R Gamma A B p Hcheck.
  pose proof (regulator_theory_check_true_lines_lemma R (ctx_extend A Gamma) p B Hcheck)
    as Hlines.
  pose proof (regulator_theory_check_true_last_lemma R (ctx_extend A Gamma) p B Hcheck)
    as Hlast_source.
  unfold regulator_theory_deduction_transform.
  pose proof
    (deduction_transform_lines_verified_lemma R Gamma A nil p deduction_state_empty)
    as Htrans.
  simpl in Htrans.
  assert (Hinitial :
    deduction_state_verified R Gamma A nil deduction_state_empty).
  {
    constructor; simpl; reflexivity.
  }
  specialize (Htrans Hinitial Hlines).
  simpl in Htrans.
  destruct Htrans as [Hchecked Hmap Hlast].
  unfold regulator_theory_check_bool.
  rewrite Hchecked.
  simpl.
  unfold deduction_last_formula_verified in Hlast.
  rewrite Hlast_source in Hlast.
  rewrite Hlast.
  rewrite formula_eq_bool_refl_lemma.
  reflexivity.
Qed.

(*
│
│          `regulator_theory_deduction_minimal_checked` is the
│          EFQ-free specialisation of
│          `regulator_theory_deduction_checked`. The transformer is
│          regulator-profile uniform — the K/S blocks contain no EFQ —
│          so the specialisation is immediate through
│          `regulator_theory_check_minimal_bool`. We expose it as a
│          named theorem because later layers often state EFQ-free
│          facts directly against the minimal checker; those layers
│          should chain through this checked minimal form rather than
│          restating the proof.
│
*)

(* T; A::Γ ⊢check_min[p] B ⇒ T; Γ ⊢check_min[deduction_transform(A,p)] A → B  *)

Theorem regulator_theory_deduction_minimal_checked :
  forall T Gamma A B p,
    regulator_theory_check_minimal_bool T (ctx_extend A Gamma) p B = true ->
    regulator_theory_check_minimal_bool T Gamma (regulator_theory_deduction_transform A p) (Imp A B) = true.
Proof.
  intros T Gamma A B p Hcheck.
  exact (regulator_theory_deduction_checked
    (regulator_theory_with_axiom_set regulator_profile_minimal T)
    Gamma A B p Hcheck).
Qed.
