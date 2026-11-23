(*L003_11__Evaluator_Lower_Bound.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                  Proofcase / L003_11__Evaluator_Lower_Bound                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  A quadratic lower bound for every internal evaluator of the concrete
  language. A term can depend only on the input positions it reads, and
  reading position `j` costs at least `j + 1` bits. The quotations of `TBit
  i` and `TBit (i + 1)` differ at exactly one bit, so an evaluator of level
  `n` must read every even input position `2 (i + 3)` with `i + 5 <= n`.
  Summing these costs gives `(n - 4) (n + 2) <= lvl u`.

  The bound depends on the encoding: indices are written in unary, so reading
  a far position is expensive. Under a binary index encoding the same
  argument gives a much weaker bound.

*)

From L003 Require Export L003_10__Coding_Sensitivity.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                READ POSITIONS                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The outer input positions a term inspects, with
│          multiplicity. Duplication halves positions; projection
│          keeps only the even, outer positions and halves them.
│
*)

Fixpoint reads (t : ConcreteTerm) : list nat :=
  match t with
  | TConst _ => []
  | TBit i => [i]
  | TNot s => reads s
  | TAnd s u | TOr s u => reads s ++ reads u
  | TDup s => map Nat.div2 (reads s)
  | TProj s => map Nat.div2 (filter Nat.even (reads s))
  | TOracle l => l
  end.

(*
│
│          A term holds at two streams equally when they agree on its
│          read positions.
│
*)

Theorem reads_ext :
  forall O t x y,
    (forall j, In j (reads t) -> x j = y j) ->
    term_sem O t x <-> term_sem O t y.
Proof.
  intros O t.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intros x y Hxy.
  - reflexivity.
  - rewrite (Hxy i (or_introl eq_refl)). reflexivity.
  - rewrite (IH x y Hxy). reflexivity.
  - assert (Hs : term_sem O s x <-> term_sem O s y).
    { apply IHs. intros j Hj. apply Hxy. apply in_or_app. left. exact Hj. }
    assert (Hu : term_sem O u x <-> term_sem O u y).
    { apply IHu. intros j Hj. apply Hxy. apply in_or_app. right. exact Hj. }
    rewrite Hs, Hu. reflexivity.
  - assert (Hs : term_sem O s x <-> term_sem O s y).
    { apply IHs. intros j Hj. apply Hxy. apply in_or_app. left. exact Hj. }
    assert (Hu : term_sem O u x <-> term_sem O u y).
    { apply IHu. intros j Hj. apply Hxy. apply in_or_app. right. exact Hj. }
    rewrite Hs, Hu. reflexivity.
  - apply IH.
    intros j Hj.
    unfold stream_pair.
    destruct (Nat.even j); apply Hxy; apply in_map; exact Hj.
  - assert (Hagree :
      forall w j, In j (reads s) -> stream_pair x w j = stream_pair y w j).
    { intros w j Hj.
      unfold stream_pair.
      destruct (Nat.even j) eqn:Heven; [| reflexivity].
      apply Hxy.
      apply in_map.
      apply filter_In.
      split; assumption. }
    split; intros [w Hw]; exists w.
    + exact (proj1 (IH _ _ (Hagree w)) Hw).
    + exact (proj2 (IH _ _ (Hagree w)) Hw).
  - rewrite (map_ext_in x y l Hxy).
    reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               COST OF READING                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Reading position `j` is charged `j + 1`.
│
*)

Fixpoint position_cost (l : list nat) : nat :=
  match l with
  | [] => 0
  | j :: l' => S j + position_cost l'
  end.

Lemma position_cost_app :
  forall l1 l2,
    position_cost (l1 ++ l2) = position_cost l1 + position_cost l2.
Proof.
  induction l1 as [| j l1 IH]; intro l2; simpl; [reflexivity |].
  rewrite IH. lia.
Qed.

Lemma div2_le :
  forall j, Nat.div2 j <= j.
Proof.
  intro j.
  pose proof (Nat.div2_odd j).
  destruct (Nat.odd j); simpl in *; lia.
Qed.

Lemma position_cost_div2 :
  forall l, position_cost (map Nat.div2 l) <= position_cost l.
Proof.
  induction l as [| j l IH]; simpl; [lia |].
  pose proof (div2_le j). lia.
Qed.

Lemma position_cost_filter :
  forall (p : nat -> bool) l,
    position_cost (filter p l) <= position_cost l.
Proof.
  intro p.
  induction l as [| j l IH]; simpl; [lia |].
  destruct (p j); simpl; lia.
Qed.

Lemma list_bits_cost :
  forall l, position_cost l < length (list_bits l).
Proof.
  induction l as [| j l IH]; simpl; [lia |].
  rewrite length_app, length_unary_bits.
  lia.
Qed.

(*
│
│          Every read costs at least its position plus one bit in the
│          serialization.
│
*)

Theorem reads_cost :
  forall t, position_cost (reads t) <= term_level t.
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l].
  - unfold term_level. simpl. lia.
  - unfold term_level. simpl. rewrite length_unary_bits. lia.
  - rewrite (proj1 (term_level_tag s)). simpl. lia.
  - rewrite (proj1 (term_level_binary s u)). simpl.
    rewrite position_cost_app. lia.
  - rewrite (proj2 (term_level_binary s u)). simpl.
    rewrite position_cost_app. lia.
  - rewrite (proj1 (proj2 (term_level_tag s))). simpl.
    pose proof (position_cost_div2 (reads s)). lia.
  - rewrite (proj2 (proj2 (term_level_tag s))). simpl.
    pose proof (position_cost_div2 (filter Nat.even (reads s))).
    pose proof (position_cost_filter Nat.even (reads s)).
    lia.
  - unfold term_level. simpl.
    pose proof (list_bits_cost l). lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                ONE-BIT PAIRS                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Lemma unary_bits_nth :
  forall i j, nth j (unary_bits i) false = (j <? i).
Proof.
  induction i as [| i IH]; intro j.
  - destruct j as [| [| j]]; reflexivity.
  - destruct j as [| j]; [reflexivity |].
    simpl. rewrite IH. reflexivity.
Qed.

(*
│
│          The quotations of `TBit i` and `TBit (i + 1)` agree
│          everywhere except at position `i + 3`.
│
*)

Lemma one_bit_pair :
  forall i k,
    k <> i + 3 ->
    term_code (TBit i) k = term_code (TBit (S i)) k.
Proof.
  intros i k Hk.
  destruct k as [| [| [| j]]]; try reflexivity.
  change (nth j (unary_bits i) false = nth j (unary_bits (S i)) false).
  rewrite !unary_bits_nth.
  destruct (Nat.ltb_spec j i), (Nat.ltb_spec j (S i));
    try reflexivity; lia.
Qed.

Lemma one_bit_pair_differs :
  forall i,
    term_code (TBit i) (i + 3) = false /\
    term_code (TBit (S i)) (i + 3) = true.
Proof.
  intro i.
  replace (i + 3) with (S (S (S i))) by lia.
  change (nth i (unary_bits i) false = false /\
          nth i (unary_bits (S i)) false = true).
  rewrite !unary_bits_nth.
  split.
  - apply Nat.ltb_irrefl.
  - apply Nat.ltb_lt. lia.
Qed.

Lemma bit_reader_level :
  forall i, term_level (TBit i) = 4 + i.
Proof.
  intro i.
  unfold term_level.
  simpl.
  rewrite length_unary_bits.
  lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                     EVALUATORS READ EVERY CODE POSITION                      │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          An evaluator of level `n` reads input position `2 (i + 3)`
│          whenever `TBit (i + 1)` lies in its domain. Otherwise it
│          could not separate `TBit i` from `TBit (i + 1)` on a stream
│          where only bit `i` is set.
│
*)

Theorem evaluator_reads :
  forall O u n i,
    Evaluates (concrete_structure O) u n ->
    i + 5 <= n ->
    In (2 * (i + 3)) (reads u).
Proof.
  intros O u n i Hev Hi.
  destruct (in_dec Nat.eq_dec (2 * (i + 3)) (reads u)) as [Hin | Hout];
    [exact Hin | exfalso].
  set (x := fun j => Nat.eqb j i).
  pose proof (Hev (TBit i) ltac:(change (term_level (TBit i) <= n);
                                  rewrite bit_reader_level; lia) x) as H1.
  pose proof (Hev (TBit (S i)) ltac:(change (term_level (TBit (S i)) <= n);
                                      rewrite bit_reader_level; lia) x) as H2.
  change (term_sem O u (stream_pair (term_code (TBit i)) x) <->
          term_sem O (TBit i) x) in H1.
  change (term_sem O u (stream_pair (term_code (TBit (S i))) x) <->
          term_sem O (TBit (S i)) x) in H2.
  assert (Hsame :
    term_sem O u (stream_pair (term_code (TBit i)) x) <->
    term_sem O u (stream_pair (term_code (TBit (S i))) x)).
  { apply reads_ext.
    intros j Hj.
    unfold stream_pair.
    destruct (Nat.even j) eqn:Heven; [| reflexivity].
    apply one_bit_pair.
    intro Hdiv.
    apply Hout.
    pose proof (Nat.div2_odd j) as Hj2.
    rewrite <- Nat.negb_even, Heven in Hj2.
    simpl in Hj2.
    replace (2 * (i + 3)) with j by lia.
    exact Hj. }
  assert (Htrue : term_sem O (TBit i) x).
  { simpl. unfold x. apply Nat.eqb_refl. }
  assert (Hfalse : ~ term_sem O (TBit (S i)) x).
  { simpl. unfold x. rewrite (proj2 (Nat.eqb_neq (S i) i) ltac:(lia)).
    discriminate. }
  apply Hfalse.
  apply H2.
  apply Hsame.
  apply H1.
  exact Htrue.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          SUMMING DISTINCT POSITIONS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Lemma position_cost_remove_le :
  forall a l, position_cost (remove Nat.eq_dec a l) <= position_cost l.
Proof.
  intro a.
  induction l as [| b l IH]; simpl; [lia |].
  destruct (Nat.eq_dec a b); simpl; lia.
Qed.

Lemma position_cost_remove :
  forall a l,
    In a l ->
    S a + position_cost (remove Nat.eq_dec a l) <= position_cost l.
Proof.
  intro a.
  induction l as [| b l IH]; intro Hin; [destruct Hin |].
  simpl.
  destruct (Nat.eq_dec a b) as [Hab | Hab].
  - subst b.
    pose proof (position_cost_remove_le a l). lia.
  - destruct Hin as [Hba | Hin]; [congruence |].
    simpl.
    pose proof (IH Hin). lia.
Qed.

(*
│
│          A duplicate-free list contained in another costs no more
│          than it.
│
*)

Lemma position_cost_sublist :
  forall P L,
    NoDup P ->
    (forall j, In j P -> In j L) ->
    position_cost P <= position_cost L.
Proof.
  induction P as [| a P IH]; intros L Hnodup Hincl; simpl; [lia |].
  inversion Hnodup as [| a' P' Hnotin Hnodup']; subst.
  assert (Ha : In a L) by (apply Hincl; left; reflexivity).
  pose proof (position_cost_remove a L Ha).
  assert (HP : position_cost P <= position_cost (remove Nat.eq_dec a L)).
  { apply IH; [exact Hnodup' |].
    intros j Hj.
    apply in_in_remove.
    - intro Hja. subst j. contradiction.
    - apply Hincl. right. exact Hj. }
  lia.
Qed.

Definition code_positions (k : nat) : list nat :=
  map (fun i => 2 * (i + 3)) (seq 0 k).

Lemma code_positions_nodup :
  forall k, NoDup (code_positions k).
Proof.
  intro k.
  unfold code_positions.
  generalize (seq_NoDup k 0).
  generalize (seq 0 k).
  induction l as [| a l IH]; intro Hnodup; simpl; [constructor |].
  inversion Hnodup as [| a' l' Hnotin Hnodup']; subst.
  constructor.
  - intro Hin.
    apply in_map_iff in Hin as [b [Hb Hbl]].
    assert (b = a) by lia.
    subst b. contradiction.
  - apply IH. exact Hnodup'.
Qed.

Lemma code_positions_cost :
  forall k, position_cost (code_positions k) = k * (k + 6).
Proof.
  induction k as [| k IH]; [reflexivity |].
  unfold code_positions in *.
  rewrite seq_S, map_app, position_cost_app, IH.
  simpl.
  nia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            QUADRATIC LOWER BOUND                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Every internal evaluator of level `n` has level at least
│          `(n - 4) (n + 2)`. Brute force, at least `3^(n+1) - 3`,
│          lies above it; whether a polynomial-size evaluator exists
│          is open.
│
*)

Theorem evaluator_quadratic_lower_bound :
  forall O u n,
    Evaluates (concrete_structure O) u n ->
    (n - 4) * (n + 2) <= term_level u.
Proof.
  intros O u n Hev.
  destruct (Nat.lt_ge_cases n 4) as [Hsmall | Hlarge].
  - replace (n - 4) with 0 by lia. lia.
  - assert (Hincl :
      forall j, In j (code_positions (n - 4)) -> In j (reads u)).
    { intros j Hj.
      unfold code_positions in Hj.
      apply in_map_iff in Hj as [i [Hij Hi]].
      apply in_seq in Hi.
      subst j.
      apply (evaluator_reads O u n i Hev).
      lia. }
    pose proof (position_cost_sublist _ _ (code_positions_nodup (n - 4)) Hincl).
    pose proof (code_positions_cost (n - 4)).
    pose proof (reads_cost u).
    replace (n + 2) with (n - 4 + 6) by lia.
    lia.
Qed.

(*
│
│          In particular `BF_n` itself satisfies the quadratic bound,
│          and the exponential bound lies above it.
│
*)

Corollary brute_force_between_bounds :
  forall n,
    (n - 4) * (n + 2) <= term_level (brute_force n) /\
    3 ^ S n <= term_level (brute_force n) + 3.
Proof.
  intro n.
  split.
  - exact (evaluator_quadratic_lower_bound empty_oracle _ n
             (brute_force_evaluates empty_oracle n)).
  - exact (brute_force_growth n).
Qed.
