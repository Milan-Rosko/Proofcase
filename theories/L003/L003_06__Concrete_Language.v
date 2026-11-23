(*L003_06__Concrete_Language.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                    Proofcase / L003_06__Concrete_Language                    │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  The concrete language over bit streams, relativized to an arbitrary oracle.
  Terms are built from constants, input bits, the Boolean connectives,
  duplication, projection, and an oracle node querying the input at a finite
  list of positions. Semantics is proposition-valued and respects pointwise
  equality of streams.

  Quotation is a prefix-free serialization, and the level of a term is the
  length of its serialization. Negation, duplication, and projection each
  cost exactly three bits, so the concrete language is a graded certification
  structure for every oracle.

*)

(*
│
│          `Lists.List` supplies serializations, oracle queries, and
│          enumerations.
│
*)

From Stdlib Require Export Lists.List.
Export ListNotations.

From L003 Require Export L003_05__Internal_Certification.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              TERMS AND STREAMS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Inductive ConcreteTerm : Type :=
| TConst : bool -> ConcreteTerm
| TBit : nat -> ConcreteTerm
| TNot : ConcreteTerm -> ConcreteTerm
| TAnd : ConcreteTerm -> ConcreteTerm -> ConcreteTerm
| TOr : ConcreteTerm -> ConcreteTerm -> ConcreteTerm
| TDup : ConcreteTerm -> ConcreteTerm
| TProj : ConcreteTerm -> ConcreteTerm
| TOracle : list nat -> ConcreteTerm.

(*
│
│          Data are infinite bit streams; pairing interleaves even and
│          odd positions.
│
*)

Definition BitStream : Type := nat -> bool.

Definition stream_pair (x y : BitStream) : BitStream :=
  fun i => if Nat.even i then x (Nat.div2 i) else y (Nat.div2 i).

Lemma even_double :
  forall n, Nat.even (2 * n) = true.
Proof.
  induction n as [| n IH]; [reflexivity |].
  replace (2 * S n) with (S (S (2 * n))) by lia.
  exact IH.
Qed.

Lemma even_succ_double :
  forall n, Nat.even (S (2 * n)) = false.
Proof.
  induction n as [| n IH]; [reflexivity |].
  replace (S (2 * S n)) with (S (S (S (2 * n)))) by lia.
  exact IH.
Qed.

Lemma stream_pair_even :
  forall x y n, stream_pair x y (2 * n) = x n.
Proof.
  intros x y n.
  unfold stream_pair.
  rewrite even_double, Nat.div2_double.
  reflexivity.
Qed.

Lemma stream_pair_odd :
  forall x y n, stream_pair x y (S (2 * n)) = y n.
Proof.
  intros x y n.
  unfold stream_pair.
  rewrite even_succ_double, Nat.div2_succ_double.
  reflexivity.
Qed.

Lemma stream_pair_ext :
  forall x x' y y',
    (forall i, x i = x' i) ->
    (forall i, y i = y' i) ->
    forall i, stream_pair x y i = stream_pair x' y' i.
Proof.
  intros x x' y y' Hx Hy i.
  unfold stream_pair.
  destruct (Nat.even i); [apply Hx | apply Hy].
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            RELATIVIZED SEMANTICS                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          An oracle is an arbitrary predicate on finite bit lists.
│          `TOracle l` asks the oracle about the input bits at the
│          positions `l`. Projection is an unbounded existential over
│          witness streams; neither it nor the oracle is decidable in
│          general.
│
*)

Definition Oracle : Type := list bool -> Prop.

Fixpoint term_sem (O : Oracle) (t : ConcreteTerm) (x : BitStream) : Prop :=
  match t with
  | TConst b => b = true
  | TBit i => x i = true
  | TNot s => ~ term_sem O s x
  | TAnd s u => term_sem O s x /\ term_sem O u x
  | TOr s u => term_sem O s x \/ term_sem O u x
  | TDup s => term_sem O s (stream_pair x x)
  | TProj s => exists w : BitStream, term_sem O s (stream_pair x w)
  | TOracle l => O (map x l)
  end.

(*
│
│          The unrelativized language consults the empty oracle.
│
*)

Definition empty_oracle : Oracle := fun _ => False.

(*
│
│          Semantics respects pointwise equality of streams. No
│          function extensionality is used.
│
*)

Lemma term_sem_ext :
  forall O t x y,
    (forall i, x i = y i) ->
    term_sem O t x <-> term_sem O t y.
Proof.
  intros O t.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intros x y Hxy.
  - reflexivity.
  - rewrite Hxy. reflexivity.
  - rewrite (IH x y Hxy). reflexivity.
  - rewrite (IHs x y Hxy), (IHu x y Hxy). reflexivity.
  - rewrite (IHs x y Hxy), (IHu x y Hxy). reflexivity.
  - apply IH.
    apply stream_pair_ext; exact Hxy.
  - split; intros [w Hw]; exists w.
    + apply (IH (stream_pair x w)); [| exact Hw].
      apply stream_pair_ext; [exact Hxy | reflexivity].
    + apply (IH _ (stream_pair y w)); [| exact Hw].
      apply stream_pair_ext; [exact Hxy | reflexivity].
  - rewrite (map_ext x y Hxy l).
    reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                SERIALIZATION                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Naturals are written in unary with a terminating `false`;
│          position lists are written element by element, each
│          preceded by `true`, and closed by `false`. Every
│          constructor has a three-bit tag.
│
*)

Fixpoint unary_bits (n : nat) : list bool :=
  match n with
  | O => [false]
  | S m => true :: unary_bits m
  end.

Fixpoint list_bits (l : list nat) : list bool :=
  match l with
  | [] => [false]
  | i :: l' => true :: unary_bits i ++ list_bits l'
  end.

Fixpoint term_serialize (t : ConcreteTerm) : list bool :=
  match t with
  | TConst b => [false; false; false; b]
  | TBit i => [false; false; true] ++ unary_bits i
  | TNot s => [false; true; false] ++ term_serialize s
  | TAnd s u => [false; true; true] ++ term_serialize s ++ term_serialize u
  | TOr s u => [true; false; false] ++ term_serialize s ++ term_serialize u
  | TDup s => [true; false; true] ++ term_serialize s
  | TProj s => [true; true; false] ++ term_serialize s
  | TOracle l => [true; true; true] ++ list_bits l
  end.

(*
│
│          Quotation reads the serialization as a stream padded with
│          `false`.
│
*)

Definition term_code (t : ConcreteTerm) : BitStream :=
  fun i => nth i (term_serialize t) false.

(*
│
│          Unique parsing: a serialization followed by any suffix
│          determines both the term and the suffix. In particular the
│          serialization is injective and prefix-free.
│
*)

Lemma unary_bits_unique :
  forall i j s s',
    unary_bits i ++ s = unary_bits j ++ s' ->
    i = j /\ s = s'.
Proof.
  induction i as [| i IH]; destruct j as [| j]; simpl; intros s s' H;
    inversion H as [[Htail]].
  - split; reflexivity.
  - destruct (IH j s s' Htail) as [-> ->].
    split; reflexivity.
Qed.

Lemma list_bits_unique :
  forall l l' s s',
    list_bits l ++ s = list_bits l' ++ s' ->
    l = l' /\ s = s'.
Proof.
  induction l as [| i l IH]; destruct l' as [| j l']; simpl; intros s s' H;
    inversion H as [[Htail]].
  - split; reflexivity.
  - rewrite <- !app_assoc in Htail.
    destruct (unary_bits_unique i j _ _ Htail) as [-> Hrest].
    destruct (IH l' s s' Hrest) as [-> ->].
    split; reflexivity.
Qed.

Theorem serialize_unique :
  forall t t' s s',
    term_serialize t ++ s = term_serialize t' ++ s' ->
    t = t' /\ s = s'.
Proof.
  induction t as [b | i | a IH | a IHa c IHc | a IHa c IHc | a IH | a IH | l];
    destruct t' as [b' | i' | a' | a' c' | a' c' | a' | a' | l'];
    intros s s' H; simpl in H; rewrite <- ?app_assoc in H;
    inversion H as [Htail]; clear H.
  - split; reflexivity.
  - destruct (unary_bits_unique i i' s s' Htail) as [-> ->].
    split; reflexivity.
  - destruct (IH a' s s' Htail) as [-> ->].
    split; reflexivity.
  - destruct (IHa a' _ _ Htail) as [-> Hrest].
    destruct (IHc c' s s' Hrest) as [-> ->].
    split; reflexivity.
  - destruct (IHa a' _ _ Htail) as [-> Hrest].
    destruct (IHc c' s s' Hrest) as [-> ->].
    split; reflexivity.
  - destruct (IH a' s s' Htail) as [-> ->].
    split; reflexivity.
  - destruct (IH a' s s' Htail) as [-> ->].
    split; reflexivity.
  - destruct (list_bits_unique l l' s s' Htail) as [-> ->].
    split; reflexivity.
Qed.

Corollary serialize_injective :
  forall t t',
    term_serialize t = term_serialize t' ->
    t = t'.
Proof.
  intros t t' H.
  apply (serialize_unique t t' [] []).
  rewrite H.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                   GRADING                                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The level of a term is the length of its serialization.
│
*)

Definition term_level (t : ConcreteTerm) : nat :=
  length (term_serialize t).

Lemma term_level_tag :
  forall s,
    term_level (TNot s) = 3 + term_level s /\
    term_level (TDup s) = 3 + term_level s /\
    term_level (TProj s) = 3 + term_level s.
Proof.
  intro s.
  unfold term_level.
  simpl.
  split; [reflexivity |].
  split; reflexivity.
Qed.

Lemma term_level_binary :
  forall s u,
    term_level (TAnd s u) = 3 + term_level s + term_level u /\
    term_level (TOr s u) = 3 + term_level s + term_level u.
Proof.
  intros s u.
  unfold term_level.
  simpl.
  rewrite length_app.
  split; lia.
Qed.

Lemma term_level_positive :
  forall t, 3 < term_level t.
Proof.
  unfold term_level.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; rewrite ?length_app; try lia.
  - destruct i; simpl; lia.
  - destruct l; simpl; lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       CONCRETE CERTIFICATION STRUCTURE                       │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          For every oracle the concrete language is a graded
│          certification structure. Witnesses are bit streams encoded
│          by the identity; all three formation costs are three.
│
*)

Definition concrete_diagonal (O : Oracle) : DiagonalStructure.
Proof.
  refine
    {| ds_expr := ConcreteTerm;
       ds_data := BitStream;
       ds_sem := term_sem O;
       ds_code := term_code;
       ds_pair := stream_pair;
       ds_level := term_level;
       ds_neg := TNot;
       ds_dup := TDup;
       ds_neg_cost := 3;
       ds_dup_cost := 3 |}.
  - intros e x. reflexivity.
  - intros e y. reflexivity.
  - intro e. rewrite (proj1 (term_level_tag e)). lia.
  - intro e. rewrite (proj1 (proj2 (term_level_tag e))). lia.
Defined.

Definition concrete_structure (O : Oracle) : CertificationStructure.
Proof.
  refine
    {| cs_base := concrete_diagonal O;
       cs_witness := BitStream;
       cs_wit := fun w => w;
       cs_proj := TProj;
       cs_proj_cost := 3 |}.
  - intros e z. reflexivity.
  - intro e.
    change (term_level (TProj e) <= term_level e + 3).
    rewrite (proj2 (proj2 (term_level_tag e))).
    lia.
Defined.

(*
│
│          The size-free view of the same language.
│
*)

Definition concrete_language (O : Oracle) : SizeFreeLanguage :=
  forget_levels (concrete_structure O).

(*
│
│          Under the serialization grading, negation and duplication
│          strictly raise levels, so every diagonal-closed concrete
│          level is empty: conditions phrased through diagonal-closed
│          levels say nothing about concrete terms.
│
*)

Theorem concrete_diagonal_closed_level_empty :
  forall O n,
    DiagonalClosed (concrete_structure O) n ->
    forall e, n < term_level e.
Proof.
  intros O n Hclosed e.
  apply (diagonal_closed_level_empty (concrete_structure O) n).
  - intro e'.
    change (term_level e' < term_level (TNot e')).
    rewrite (proj1 (term_level_tag e')).
    lia.
  - intro e'.
    change (term_level e' < term_level (TDup e')).
    rewrite (proj1 (proj2 (term_level_tag e'))).
    lia.
  - exact Hclosed.
Qed.

(*
│
│          Consequently the local no-evaluator statement is vacuous in
│          the concrete language: a diagonal-closed level contains no
│          term, so no evaluator lies inside it.
│          `closed_level_has_no_internal_evaluator` is abstract-only.
│
*)

Corollary concrete_closed_level_vacuous :
  forall O n,
    DiagonalClosed (concrete_structure O) n ->
    ~ exists e, term_level e <= n.
Proof.
  intros O n Hclosed [e He].
  pose proof (concrete_diagonal_closed_level_empty O n Hclosed e).
  lia.
Qed.

(*
│
│          The node count of a term.
│
*)

Fixpoint term_size (t : ConcreteTerm) : nat :=
  match t with
  | TConst _ | TBit _ | TOracle _ => 1
  | TNot s | TDup s | TProj s => 1 + term_size s
  | TAnd s u | TOr s u => 1 + term_size s + term_size u
  end.

(*
│
│          One size measure: every constructor tag costs at least
│          three bits and every leaf at least four, so three times the
│          node count is bounded by the level.
│
*)

Lemma term_size_level :
  forall t, 3 * term_size t <= term_level t.
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l].
  - unfold term_level. simpl. lia.
  - unfold term_level. simpl. lia.
  - rewrite (proj1 (term_level_tag s)). simpl. lia.
  - rewrite (proj1 (term_level_binary s u)). simpl. lia.
  - rewrite (proj2 (term_level_binary s u)). simpl. lia.
  - rewrite (proj1 (proj2 (term_level_tag s))). simpl. lia.
  - rewrite (proj2 (proj2 (term_level_tag s))). simpl. lia.
  - unfold term_level. simpl. destruct l; simpl; lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CONCRETE DIAGONAL                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition diagonal_term (v : ConcreteTerm) : ConcreteTerm :=
  TNot (TDup (TProj v)).

Definition ConcreteDiagonalClaim (O : Oracle) (v : ConcreteTerm) : Prop :=
  term_sem O (diagonal_term v) (term_code (diagonal_term v)).

Definition ConcreteAccepted (O : Oracle) (v : ConcreteTerm) : Prop :=
  exists w : BitStream,
    term_sem O v
      (stream_pair
        (stream_pair (term_code (diagonal_term v)) (term_code (diagonal_term v)))
        w).

Lemma concrete_diagonal_is_abstract :
  forall O v,
    diagonal_sentence (concrete_structure O) v = diagonal_term v /\
    (ConcreteDiagonalClaim O v <-> DiagonalClaim (concrete_structure O) v) /\
    (ConcreteAccepted O v <-> DiagonalAccepted (concrete_structure O) v) /\
    (ConcreteDiagonalClaim O v <-> SizeFreeDiagonalClaim (concrete_language O) v) /\
    (ConcreteAccepted O v <-> SizeFreeDiagonalAccepted (concrete_language O) v).
Proof.
  intros O v.
  repeat split; intro H; exact H.
Qed.

(*
│
│          The concrete diagonal term lies exactly nine bits above its
│          verifier, and the serialization grading has exact costs.
│
*)

Lemma diagonal_term_level :
  forall v, term_level (diagonal_term v) = term_level v + 9.
Proof.
  intro v.
  unfold diagonal_term, term_level.
  simpl.
  lia.
Qed.

Lemma concrete_exact_costs :
  forall O, ExactCosts (concrete_structure O).
Proof.
  intro O.
  split; [| split]; intro e.
  - change (term_level (TNot e) = term_level e + 3).
    rewrite (proj1 (term_level_tag e)). lia.
  - change (term_level (TDup e) = term_level e + 3).
    rewrite (proj1 (proj2 (term_level_tag e))). lia.
  - change (term_level (TProj e) = term_level e + 3).
    rewrite (proj2 (proj2 (term_level_tag e))). lia.
Qed.

(*
│
│          The coding-free identity in the concrete language: at every
│          stream `x`, by unfolding alone.
│
*)

Theorem concrete_coding_free_identity :
  forall O v x,
    term_sem O (diagonal_term v) x <->
    ~ exists w, term_sem O v (stream_pair (stream_pair x x) w).
Proof.
  intros O v x.
  reflexivity.
Qed.

Theorem concrete_fixed_point :
  forall O v,
    ConcreteDiagonalClaim O v <-> ~ ConcreteAccepted O v.
Proof.
  intros O v.
  exact (certification_fixed_point (concrete_structure O) v).
Qed.
