(*L003_07__Exhaustive_Evaluation.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                  Proofcase / L003_07__Exhaustive_Evaluation                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Brute force inside the concrete language. `BF_n` is the disjunction, over
  every term `e` of level at most `n`, of a test that the even input bits
  spell the serialization of `e` and a copy of `e` reading the odd input
  bits. Unique parsing makes exactly one disjunct fire on the quotation of
  `e`, so `BF_n` evaluates level `n`, and reading the claim half of a
  certification datum turns it into a sound and complete certifier for level
  `n`.

  The family is uniform in the oracle. The ascent hierarchy and proliferation
  therefore hold unconditionally in the concrete language and relative to
  every oracle, while the oracle genuinely changes the semantics.

*)

From L003 Require Export L003_06__Concrete_Language.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                  REINDEXING                                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Under projection, even positions are the outer input and
│          odd positions the fresh witness. Reindexing through a
│          projection moves the outer reads and leaves witness reads
│          in place.
│
*)

Definition proj_shift (f : nat -> nat) : nat -> nat :=
  fun j => if Nat.even j then 2 * f (Nat.div2 j) else j.

(*
│
│          `reindex e f` reads input bit `f i` wherever `e` reads bit
│          `i`. Duplication is absorbed into the index map; projection
│          keeps its node and shifts the map.
│
*)

Fixpoint reindex (t : ConcreteTerm) (f : nat -> nat) : ConcreteTerm :=
  match t with
  | TConst b => TConst b
  | TBit i => TBit (f i)
  | TNot s => TNot (reindex s f)
  | TAnd s u => TAnd (reindex s f) (reindex u f)
  | TOr s u => TOr (reindex s f) (reindex u f)
  | TDup s => reindex s (fun j => f (Nat.div2 j))
  | TProj s => TProj (reindex s (proj_shift f))
  | TOracle l => TOracle (map f l)
  end.

Lemma proj_shift_pair :
  forall (f : nat -> nat) (z w : BitStream) j,
    stream_pair z w (proj_shift f j) = stream_pair (fun i => z (f i)) w j.
Proof.
  intros f z w j.
  unfold proj_shift.
  destruct (Nat.even j) eqn:Heven.
  - rewrite stream_pair_even.
    unfold stream_pair.
    rewrite Heven.
    reflexivity.
  - unfold stream_pair.
    rewrite Heven.
    reflexivity.
Qed.

Theorem reindex_sem :
  forall O t f z,
    term_sem O (reindex t f) z <-> term_sem O t (fun j => z (f j)).
Proof.
  intros O t.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    intros f z; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IHs, IHu. reflexivity.
  - rewrite IHs, IHu. reflexivity.
  - rewrite IH.
    apply term_sem_ext.
    intro j.
    unfold stream_pair.
    destruct (Nat.even j); reflexivity.
  - split; intros [w Hw]; exists w.
    + apply IH in Hw.
      exact (proj1 (term_sem_ext O s _ _ (proj_shift_pair f z w)) Hw).
    + apply IH.
      exact (proj2 (term_sem_ext O s _ _ (proj_shift_pair f z w)) Hw).
  - rewrite map_map.
    reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             MATCHING A QUOTATION                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition bit_literal (b : bool) (i : nat) : ConcreteTerm :=
  if b then TBit i else TNot (TBit i).

(*
│
│          `match_bits c k` tests that the even positions from `2k` on
│          spell the bit list `c`.
│
*)

Fixpoint match_bits (c : list bool) (k : nat) : ConcreteTerm :=
  match c with
  | [] => TConst true
  | b :: c' => TAnd (bit_literal b (2 * k)) (match_bits c' (S k))
  end.

Lemma bit_literal_sem :
  forall O b i z,
    term_sem O (bit_literal b i) z <-> z i = b.
Proof.
  intros O b i z.
  unfold bit_literal.
  destruct b; simpl; destruct (z i).
  - tauto.
  - tauto.
  - split; [intro H; exfalso; apply H; reflexivity | intro H; discriminate H].
  - split; [intros _; reflexivity | intros _ H; discriminate H].
Qed.

Lemma match_bits_sem :
  forall O c k z,
    term_sem O (match_bits c k) z <->
    forall i, i < length c -> z (2 * (k + i)) = nth i c false.
Proof.
  intros O c.
  induction c as [| b c IH]; intros k z; simpl.
  - split.
    + intros _ i Hi. lia.
    + intros _. reflexivity.
  - rewrite bit_literal_sem, IH.
    split.
    + intros [Hb Hrest] i Hi.
      destruct i as [| i].
      * rewrite Nat.add_0_r. exact Hb.
      * replace (k + S i) with (S k + i) by lia.
        apply Hrest.
        lia.
    + intro H.
      split.
      * pose proof (H 0 ltac:(lia)) as H0.
        rewrite Nat.add_0_r in H0.
        exact H0.
      * intros i Hi.
        pose proof (H (S i) ltac:(lia)) as Hs.
        replace (k + S i) with (S k + i) in Hs by lia.
        exact Hs.
Qed.

(*
│
│          A list that agrees with `c'` on all positions of `c'`,
│          after padding with `false`, has `c'` as a prefix.
│
*)

Lemma nth_prefix_pad :
  forall c' c k,
    length c' <= k ->
    (forall i, i < length c' -> nth i c false = nth i c' false) ->
    exists rest, c ++ repeat false k = c' ++ rest.
Proof.
  induction c' as [| b c' IH]; intros c k Hk H.
  - exists (c ++ repeat false k). reflexivity.
  - destruct k as [| k]; [simpl in Hk; lia |].
    destruct c as [| a c].
    + pose proof (H 0 ltac:(simpl; lia)) as Hb.
      simpl in Hb.
      destruct (IH [] k ltac:(simpl in Hk; lia)) as [rest Hrest].
      { intros i Hi.
        pose proof (H (S i) ltac:(simpl; lia)) as Hs.
        simpl in Hs.
        destruct i; exact Hs. }
      exists rest.
      simpl in Hrest |- *.
      rewrite <- Hb, Hrest.
      reflexivity.
    + pose proof (H 0 ltac:(simpl; lia)) as Hab.
      simpl in Hab.
      destruct (IH c (S k) ltac:(simpl in Hk; lia)) as [rest Hrest].
      { intros i Hi.
        exact (H (S i) ltac:(simpl; lia)). }
      exists rest.
      rewrite <- !app_comm_cons.
      rewrite Hab, Hrest.
      reflexivity.
Qed.

(*
│
│          If the quotation of `e` spells the serialization of `e'` on
│          its positions, then `e'` is `e`. This is where unique
│          parsing is used.
│
*)

Lemma code_match_unique :
  forall e e',
    (forall i, i < length (term_serialize e') ->
               term_code e i = nth i (term_serialize e') false) ->
    e' = e.
Proof.
  intros e e' H.
  destruct (nth_prefix_pad (term_serialize e') (term_serialize e)
              (length (term_serialize e')) (le_n _) H) as [rest Hrest].
  destruct (serialize_unique e e' _ _ Hrest) as [He _].
  symmetry.
  exact He.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            BRUTE-FORCE EVALUATOR                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition even_position (j : nat) : nat := 2 * j.
Definition odd_position (j : nat) : nat := S (2 * j).

(*
│
│          One disjunct of `BF_n`: the even bits spell `e`, and `e`
│          holds of the odd bits.
│
*)

Definition brute_force_entry (e : ConcreteTerm) : ConcreteTerm :=
  TAnd (match_bits (term_serialize e) 0) (reindex e odd_position).

Fixpoint brute_force_list (L : list ConcreteTerm) : ConcreteTerm :=
  match L with
  | [] => TConst false
  | e :: L' => TOr (brute_force_entry e) (brute_force_list L')
  end.

Lemma brute_force_entry_sem :
  forall O e' e x,
    term_sem O (brute_force_entry e') (stream_pair (term_code e) x) <->
    e' = e /\ term_sem O e x.
Proof.
  intros O e' e x.
  unfold brute_force_entry.
  simpl.
  rewrite match_bits_sem, reindex_sem.
  assert (Hodd :
    forall j, stream_pair (term_code e) x (odd_position j) = x j).
  { intro j. apply stream_pair_odd. }
  rewrite (term_sem_ext O e' _ _ Hodd).
  split.
  - intros [Hmatch Hsem].
    assert (He : e' = e).
    { apply code_match_unique.
      intros i Hi.
      pose proof (Hmatch i Hi) as Hm.
      rewrite Nat.add_0_l, stream_pair_even in Hm.
      exact Hm. }
    subst e'.
    split; [reflexivity | exact Hsem].
  - intros [He Hsem].
    subst e'.
    split; [| exact Hsem].
    intros i _.
    rewrite Nat.add_0_l, stream_pair_even.
    reflexivity.
Qed.

Theorem brute_force_list_sem :
  forall O L e x,
    term_sem O (brute_force_list L) (stream_pair (term_code e) x) <->
    In e L /\ term_sem O e x.
Proof.
  intros O L e x.
  induction L as [| e' L IH]; cbn [brute_force_list term_sem In].
  - split.
    + intro H. discriminate H.
    + intros [[] _].
  - rewrite brute_force_entry_sem, IH.
    tauto.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                 ENUMERATION                                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `bounded_lists b k` lists every position list of length at
│          most `k` with entries below `b`.
│
*)

Fixpoint bounded_lists (b k : nat) : list (list nat) :=
  match k with
  | O => [[]]
  | S k' => [] :: flat_map (fun i => map (cons i) (bounded_lists b k')) (seq 0 b)
  end.

Lemma bounded_lists_complete :
  forall b k l,
    length l <= k ->
    (forall i, In i l -> i < b) ->
    In l (bounded_lists b k).
Proof.
  intros b k.
  induction k as [| k IH]; intros l Hlen Hbound.
  - destruct l; [left; reflexivity | simpl in Hlen; lia].
  - destruct l as [| i l]; [left; reflexivity |].
    right.
    apply in_flat_map.
    exists i.
    split.
    + apply in_seq.
      pose proof (Hbound i (or_introl eq_refl)).
      lia.
    + apply in_map.
      apply IH.
      * simpl in Hlen. lia.
      * intros j Hj. apply Hbound. right. exact Hj.
Qed.

(*
│
│          `terms_upto n` contains every term of level at most `n`; it
│          may contain more.
│
*)

Fixpoint terms_upto (n : nat) : list ConcreteTerm :=
  match n with
  | O => []
  | S m =>
      TConst false :: TConst true ::
      map TBit (seq 0 (S m)) ++
      map TOracle (bounded_lists (S m) (S m)) ++
      map TNot (terms_upto m) ++
      map TDup (terms_upto m) ++
      map TProj (terms_upto m) ++
      flat_map (fun a => map (TAnd a) (terms_upto m)) (terms_upto m) ++
      flat_map (fun a => map (TOr a) (terms_upto m)) (terms_upto m)
  end.

Lemma length_unary_bits :
  forall i, length (unary_bits i) = S i.
Proof.
  induction i as [| i IH]; simpl; lia.
Qed.

Lemma list_bits_bounds :
  forall l,
    length l < length (list_bits l) /\
    forall i, In i l -> S i < length (list_bits l).
Proof.
  induction l as [| j l [IHlen IHin]]; simpl.
  - split; [lia | intros i []].
  - rewrite length_app, length_unary_bits.
    split; [lia |].
    intros i [Hi | Hi].
    + subst. lia.
    + pose proof (IHin i Hi). lia.
Qed.

Theorem terms_upto_complete :
  forall t n,
    term_level t <= n ->
    In t (terms_upto n).
Proof.
  intros t.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    intros n Hn;
    (destruct n as [| m];
     [match type of Hn with
      | term_level ?t <= _ => pose proof (term_level_positive t); lia
      end |]);
    cbn [terms_upto];
    [| right; right; rewrite !in_app_iff ..].
  - destruct b; [right; left | left]; reflexivity.
  - left.
    apply in_map, in_seq.
    unfold term_level in Hn.
    simpl in Hn.
    rewrite length_unary_bits in Hn.
    lia.
  - do 2 right. left.
    apply in_map, IH.
    rewrite (proj1 (term_level_tag s)) in Hn.
    lia.
  - do 5 right. left.
    apply in_flat_map.
    exists s.
    destruct (term_level_binary s u) as [Hlev _].
    rewrite Hlev in Hn.
    split; [apply IHs; lia |].
    apply in_map, IHu.
    lia.
  - do 6 right.
    apply in_flat_map.
    exists s.
    destruct (term_level_binary s u) as [_ Hlev].
    rewrite Hlev in Hn.
    split; [apply IHs; lia |].
    apply in_map, IHu.
    lia.
  - do 3 right. left.
    apply in_map, IH.
    rewrite (proj1 (proj2 (term_level_tag s))) in Hn.
    lia.
  - do 4 right. left.
    apply in_map, IH.
    rewrite (proj2 (proj2 (term_level_tag s))) in Hn.
    lia.
  - right. left.
    apply in_map.
    unfold term_level in Hn.
    simpl in Hn.
    destruct (list_bits_bounds l) as [Hlen Hin].
    apply bounded_lists_complete.
    + lia.
    + intros i Hi.
      pose proof (Hin i Hi).
      lia.
Qed.

(*
│
│          `BF_n`: exhaustive evaluation of level `n` as one term of
│          the language.
│
*)

Definition brute_force (n : nat) : ConcreteTerm :=
  brute_force_list (terms_upto n).

Theorem brute_force_evaluates :
  forall O n,
    Evaluates (concrete_structure O) (brute_force n) n.
Proof.
  intros O n e He x.
  change (term_sem O (brute_force n) (stream_pair (term_code e) x) <->
          term_sem O e x).
  unfold brute_force.
  rewrite brute_force_list_sem.
  split.
  - intros [_ H]. exact H.
  - intro H.
    split; [apply terms_upto_complete; exact He | exact H].
Qed.

(*
│
│          Growth: every level enumerates at least three times the
│          previous one, and each disjunct of `BF_n` costs at least
│          three bits, so `BF_n` has level at least `3^(n+1) - 3`.
│          Evaluator Ascent bounds every evaluator of level `n` only
│          by `n - 6` from below; the gap between the two is open.
│
*)

Lemma terms_upto_length :
  forall n, 3 ^ n <= S (length (terms_upto n)).
Proof.
  induction n as [| m IH].
  - simpl. lia.
  - cbn [terms_upto length].
    rewrite !length_app, !length_map.
    rewrite Nat.pow_succ_r'.
    lia.
Qed.

Lemma brute_force_list_level :
  forall L, 3 * length L <= term_level (brute_force_list L).
Proof.
  induction L as [| e L IH].
  - simpl. lia.
  - cbn [brute_force_list length].
    rewrite (proj2 (term_level_binary _ _)).
    lia.
Qed.

Theorem brute_force_growth :
  forall n, 3 ^ S n <= term_level (brute_force n) + 3.
Proof.
  intro n.
  pose proof (terms_upto_length n).
  pose proof (brute_force_list_level (terms_upto n)).
  unfold brute_force.
  rewrite Nat.pow_succ_r'.
  lia.
Qed.

(*
│
│          Brute force is ascent, concretely: `BF_n` evaluates level
│          `n`, and every evaluator of level `n`, `BF_n` included, has
│          level above `n - 6`.
│
*)

Theorem brute_force_is_ascent :
  forall O n,
    Evaluates (concrete_structure O) (brute_force n) n /\
    (forall B,
       Evaluates (concrete_structure O) B n ->
       n < term_level B + 6).
Proof.
  intros O n.
  split; [apply brute_force_evaluates |].
  intros B HB.
  pose proof (evaluator_ascent (concrete_structure O) B n HB) as H.
  cbn in H.
  lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            BRUTE-FORCE CERTIFIER                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The certifier reads only the claim half of a certification
│          datum and ignores the witness.
│
*)

Definition concrete_certifier (n : nat) : ConcreteTerm :=
  reindex (brute_force n) even_position.

Lemma concrete_certifier_accepts :
  forall O n e x,
    Accepts (concrete_structure O) (concrete_certifier n) e x <->
    term_sem O (brute_force n) (stream_pair (term_code e) x).
Proof.
  intros O n e x.
  assert (Hclaim :
    forall w j,
      stream_pair (stream_pair (term_code e) x) w (even_position j) =
      stream_pair (term_code e) x j).
  { intros w j. apply stream_pair_even. }
  split.
  - intros [w Hw].
    change (term_sem O (concrete_certifier n)
              (stream_pair (stream_pair (term_code e) x) w)) in Hw.
    unfold concrete_certifier in Hw.
    rewrite reindex_sem, (term_sem_ext O _ _ _ (Hclaim w)) in Hw.
    exact Hw.
  - intro H.
    exists (fun _ => false).
    change (term_sem O (concrete_certifier n)
              (stream_pair (stream_pair (term_code e) x) (fun _ => false))).
    unfold concrete_certifier.
    rewrite reindex_sem, (term_sem_ext O _ _ _ (Hclaim (fun _ => false))).
    exact H.
Qed.

(*
│
│          The concrete bounded certification family, for every
│          oracle.
│
*)

Theorem concrete_certification_family :
  forall O,
    BoundedCertificationFamily (concrete_structure O) concrete_certifier.
Proof.
  intros O n.
  split.
  - intros e He x HA.
    apply (concrete_certifier_accepts O n e x) in HA.
    exact (proj1 (brute_force_evaluates O n e He x) HA).
  - intros e He x Htrue.
    apply (concrete_certifier_accepts O n e x).
    exact (proj2 (brute_force_evaluates O n e He x) Htrue).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               CERTIFIER LEVEL                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A term is duplication-free when it has no duplication node.
│          Reindexing always produces duplication-free terms, so
│          `BF_n` is duplication-free.
│
*)

Fixpoint DupFree (t : ConcreteTerm) : Prop :=
  match t with
  | TConst _ | TBit _ | TOracle _ => True
  | TNot s | TProj s => DupFree s
  | TAnd s u | TOr s u => DupFree s /\ DupFree u
  | TDup _ => False
  end.

Lemma reindex_dup_free :
  forall t f, DupFree (reindex t f).
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    intro f; simpl; try split; auto.
Qed.

Lemma match_bits_dup_free :
  forall c k, DupFree (match_bits c k).
Proof.
  induction c as [| b c IH]; intro k; simpl; [exact I |].
  split; [destruct b; simpl; exact I | apply IH].
Qed.

Lemma brute_force_dup_free :
  forall n, DupFree (brute_force n).
Proof.
  intro n.
  unfold brute_force.
  induction (terms_upto n) as [| e L IH]; simpl; [exact I |].
  split; [split; [apply match_bits_dup_free | apply reindex_dup_free] | exact IH].
Qed.

(*
│
│          Reindexing a duplication-free term through a non-decreasing
│          index map cannot lower its level: bit indices and oracle
│          positions only grow, and every other node keeps its tag.
│
*)

Lemma list_bits_map_level :
  forall (f : nat -> nat) l,
    (forall i, i <= f i) ->
    length (list_bits l) <= length (list_bits (map f l)).
Proof.
  intros f l Hf.
  induction l as [| i l IH]; simpl; [lia |].
  rewrite !length_app, !length_unary_bits.
  pose proof (Hf i).
  lia.
Qed.

Lemma proj_shift_grows :
  forall f, (forall i, i <= f i) -> forall j, j <= proj_shift f j.
Proof.
  intros f Hf j.
  unfold proj_shift.
  destruct (Nat.even j) eqn:Heven; [| lia].
  pose proof (Nat.div2_odd j) as Hdiv.
  rewrite <- Nat.negb_even, Heven in Hdiv.
  simpl in Hdiv.
  pose proof (Hf (Nat.div2 j)).
  lia.
Qed.

Lemma reindex_level_mono :
  forall t f,
    DupFree t ->
    (forall i, i <= f i) ->
    term_level t <= term_level (reindex t f).
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    intros f Hfree Hf; simpl in Hfree.
  - reflexivity.
  - unfold term_level. simpl.
    rewrite !length_unary_bits.
    pose proof (Hf i). lia.
  - change (term_level (TNot s) <= term_level (TNot (reindex s f))).
    rewrite !(proj1 (term_level_tag _)).
    pose proof (IH f Hfree Hf). lia.
  - change (term_level (TAnd s u) <=
            term_level (TAnd (reindex s f) (reindex u f))).
    rewrite !(proj1 (term_level_binary _ _)).
    pose proof (IHs f (proj1 Hfree) Hf).
    pose proof (IHu f (proj2 Hfree) Hf). lia.
  - change (term_level (TOr s u) <=
            term_level (TOr (reindex s f) (reindex u f))).
    rewrite !(proj2 (term_level_binary _ _)).
    pose proof (IHs f (proj1 Hfree) Hf).
    pose proof (IHu f (proj2 Hfree) Hf). lia.
  - contradiction.
  - change (term_level (TProj s) <=
            term_level (TProj (reindex s (proj_shift f)))).
    rewrite !(proj2 (proj2 (term_level_tag _))).
    pose proof (IH (proj_shift f) Hfree (proj_shift_grows f Hf)). lia.
  - unfold term_level. simpl.
    pose proof (list_bits_map_level f l Hf). lia.
Qed.

(*
│
│          The certifier is no smaller than `BF_n`, hence at least
│          `3^(n+1) - 3`.
│
*)

Theorem concrete_certifier_level :
  forall n,
    term_level (brute_force n) <= term_level (concrete_certifier n) /\
    3 ^ S n <= term_level (concrete_certifier n) + 3.
Proof.
  intro n.
  assert (Hmono :
    term_level (brute_force n) <= term_level (concrete_certifier n)).
  { apply reindex_level_mono.
    - apply brute_force_dup_free.
    - intro i. unfold even_position. lia. }
  split; [exact Hmono |].
  pose proof (brute_force_growth n).
  lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CONCRETE HIERARCHY                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The ascent hierarchy, its exact step, and proliferation
│          hold in the concrete language without any hypothesis. Each
│          step rises exactly by the level of the current certifier
│          plus nine.
│
*)

Theorem concrete_ascent_hierarchy :
  forall O n0 k,
    ascent_levels (concrete_structure O) concrete_certifier n0 k <
      ascent_levels (concrete_structure O) concrete_certifier n0 (S k) /\
    ascent_levels (concrete_structure O) concrete_certifier n0 (S k) =
      term_level
        (concrete_certifier
          (ascent_levels (concrete_structure O) concrete_certifier n0 k)) + 9 /\
    ~ (DiagonalAccepted (concrete_structure O)
         (concrete_certifier
           (ascent_levels (concrete_structure O) concrete_certifier n0 k)) <->
       DiagonalClaim (concrete_structure O)
         (concrete_certifier
           (ascent_levels (concrete_structure O) concrete_certifier n0 k))) /\
    (Accepts (concrete_structure O)
       (concrete_certifier
         (ascent_levels (concrete_structure O) concrete_certifier n0 (S k)))
       (diagonal_term
         (concrete_certifier
           (ascent_levels (concrete_structure O) concrete_certifier n0 k)))
       (term_code
         (diagonal_term
           (concrete_certifier
             (ascent_levels (concrete_structure O) concrete_certifier n0 k))))
     <->
     DiagonalClaim (concrete_structure O)
       (concrete_certifier
         (ascent_levels (concrete_structure O) concrete_certifier n0 k))).
Proof.
  intros O n0 k.
  pose proof (concrete_certification_family O) as HV.
  destruct (ascent_hierarchy _ _ n0 HV k) as [Hlt [Hinc Hnext]].
  split; [exact Hlt |].
  split.
  { simpl.
    exact (diagonal_term_level _). }
  split; [exact Hinc | exact Hnext].
Qed.

(*
│
│          Growth of the concrete hierarchy: each level is at least
│          exponential in the previous one, so the ascent levels grow
│          at least as fast as a tower of threes.
│
*)

Theorem concrete_hierarchy_growth :
  forall O n0 k,
    3 ^ S (ascent_levels (concrete_structure O) concrete_certifier n0 k) + 6 <=
    ascent_levels (concrete_structure O) concrete_certifier n0 (S k).
Proof.
  intros O n0 k.
  destruct (concrete_ascent_hierarchy O n0 k) as [_ [Hstep _]].
  rewrite Hstep.
  pose proof (proj2 (concrete_certifier_level
                       (ascent_levels (concrete_structure O) concrete_certifier n0 k))).
  lia.
Qed.

Theorem concrete_proliferation :
  forall O n0 i j,
    diagonal_term
      (concrete_certifier
        (ascent_levels (concrete_structure O) concrete_certifier n0 i)) =
    diagonal_term
      (concrete_certifier
        (ascent_levels (concrete_structure O) concrete_certifier n0 j)) ->
    i = j.
Proof.
  intros O n0 i j.
  exact (proliferation _ _ n0 (concrete_certification_family O) i j).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                RELATIVIZATION                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A term is oracle-free when it contains no oracle node; its
│          meaning does not depend on the oracle.
│
*)

Fixpoint OracleFree (t : ConcreteTerm) : Prop :=
  match t with
  | TConst _ | TBit _ => True
  | TNot s | TDup s | TProj s => OracleFree s
  | TAnd s u | TOr s u => OracleFree s /\ OracleFree u
  | TOracle _ => False
  end.

Lemma oracle_free_sem :
  forall t,
    OracleFree t ->
    forall O O' x, term_sem O t x <-> term_sem O' t x.
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intros Hfree O O' x.
  - reflexivity.
  - reflexivity.
  - rewrite (IH Hfree O O' x). reflexivity.
  - rewrite (IHs (proj1 Hfree) O O' x), (IHu (proj2 Hfree) O O' x).
    reflexivity.
  - rewrite (IHs (proj1 Hfree) O O' x), (IHu (proj2 Hfree) O O' x).
    reflexivity.
  - apply IH. exact Hfree.
  - split; intros [w Hw]; exists w;
      [apply (IH Hfree O O') | apply (IH Hfree O' O)]; exact Hw.
  - contradiction.
Qed.

(*
│
│          Relativization. For every oracle, the concrete language is
│          a graded certification structure whose quotation, formation
│          operations, brute-force evaluators, and certifiers are the
│          same terms; the fixed point, the bounded family, and
│          brute-force ascent hold uniformly. The oracle is not idle:
│          two oracles give the same term different truth values,
│          while oracle-free terms keep their meaning.
│
*)

Theorem relativization :
  (forall O : Oracle,
     (forall v, ConcreteDiagonalClaim O v <-> ~ ConcreteAccepted O v) /\
     (forall n, Evaluates (concrete_structure O) (brute_force n) n) /\
     BoundedCertificationFamily (concrete_structure O) concrete_certifier /\
     (forall v, diagonal_sentence (concrete_structure O) v = diagonal_term v)) /\
  (forall t, OracleFree t -> forall O O' x, term_sem O t x <-> term_sem O' t x) /\
  (term_sem (fun _ => True) (TOracle []) (fun _ => false) /\
   ~ term_sem empty_oracle (TOracle []) (fun _ => false)).
Proof.
  split.
  - intro O.
    split; [exact (concrete_fixed_point O) |].
    split; [exact (brute_force_evaluates O) |].
    split; [exact (concrete_certification_family O) |].
    intro v. reflexivity.
  - split; [exact oracle_free_sem |].
    split.
    + exact I.
    + intro H. exact H.
Qed.
