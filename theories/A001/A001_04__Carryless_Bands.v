(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Carryless band layer for A001. We establish that the even and odd Fibonacci-support bands are separated, remain Zeckendorf-valid under concatenation, and can be recovered from the canonical support of a paired code.]]@*)

(*@head.end@*)

From A001 Require Export A001_03__Zeckendorf_Correctness.

(*@section@[[EVEN AND ODD BAND SEPARATION]]@*)

Lemma two_S : forall n, two (S n) = S (S (two n)).
Proof.
  intro n.
  unfold two.
  simpl.
  rewrite Nat.add_succ_r.
  reflexivity.
Qed.

Lemma even_two : forall n, Nat.even (two n) = true.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite two_S. rewrite Nat.even_succ_succ. exact IH.
Qed.

Lemma odd_S_two : forall n, Nat.even (S (two n)) = false.
Proof.
  intro n. rewrite Nat.even_succ. rewrite <- Nat.negb_even.
  rewrite even_two. reflexivity.
Qed.

Lemma two_j_minus1_formula :
  forall j, two_j_minus1 j = 2 * j - 1.
Proof.
  intro j.
  unfold two_j_minus1.
  rewrite <- Nat.sub_1_r.
  unfold two.
  lia.
Qed.

Lemma two_j_minus1_lt :
  forall a b, b < a -> two_j_minus1 b < two_j_minus1 a.
Proof.
  intros a b Hlt.
  repeat rewrite two_j_minus1_formula.
  lia.
Qed.

Lemma two_j_minus1_gap2 :
  forall a b, a >= b + 2 -> two_j_minus1 a >= two_j_minus1 b + 2.
Proof.
  intros a b Hgap.
  repeat rewrite two_j_minus1_formula.
  lia.
Qed.

Lemma two_j_minus1_ge_1 :
  forall j, 1 <= j -> 1 <= two_j_minus1 j.
Proof.
  intros j Hj.
  rewrite two_j_minus1_formula.
  lia.
Qed.

Lemma even_two_plus :
  forall a n, Nat.even (two a + n) = Nat.even n.
Proof.
  induction a as [|a IH]; intro n.
  - reflexivity.
  - rewrite two_S. cbn [plus]. rewrite Nat.even_succ_succ. apply IH.
Qed.

Lemma even_double_plus :
  forall a n, Nat.even (2 * a + n) = Nat.even n.
Proof. intros. replace (2 * a) with (two a) by (unfold two; lia). apply even_two_plus. Qed.

Lemma odd_two_j_minus1 :
  forall j, 1 <= j -> Nat.even (two_j_minus1 j) = false.
Proof.
  intros j Hj. destruct j as [|j']; [lia|].
  unfold two_j_minus1. rewrite two_S. apply odd_S_two.
Qed.

Lemma strictly_decreasing_map_two :
  forall xs, strictly_decreasing xs -> strictly_decreasing (map two xs).
Proof.
  induction xs as [|a xs IH]; intro Hdec; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hdec as [Hab Htail].
  split.
  - unfold two. lia.
  - apply IH. exact Htail.
Qed.

Lemma no_adjacent_map_two :
  forall xs, no_adjacent xs -> no_adjacent (map two xs).
Proof.
  induction xs as [|a xs IH]; intro Hadj; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hadj as [Hab Htail].
  split.
  - unfold two. lia.
  - apply IH. exact Htail.
Qed.

Lemma all_ge_2_map_two :
  forall xs, all_ge_2 xs -> all_ge_2 (map two xs).
Proof.
  induction xs as [|a xs IH]; intro Hge; simpl; auto.
  destruct Hge as [Ha Htail].
  split.
  - unfold two. lia.
  - apply IH. exact Htail.
Qed.

Lemma strictly_decreasing_map_odd :
  forall Bx xs,
    strictly_decreasing xs ->
    strictly_decreasing (map (fun j => Bx + two_j_minus1 j) xs).
Proof.
  intros Bx xs Hdec.
  revert Bx Hdec.
  induction xs as [|a xs IH]; intros Bx Hdec; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hdec as [Hab Htail].
  split.
  - apply Nat.add_lt_mono_l. apply two_j_minus1_lt. exact Hab.
  - apply IH. exact Htail.
Qed.

Lemma no_adjacent_map_odd :
  forall Bx xs,
    no_adjacent xs ->
    no_adjacent (map (fun j => Bx + two_j_minus1 j) xs).
Proof.
  intros Bx xs Hadj.
  revert Bx Hadj.
  induction xs as [|a xs IH]; intros Bx Hadj; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hadj as [Hab Htail].
  split.
  - assert (Hgap : two_j_minus1 a >= two_j_minus1 b + 2).
    + apply two_j_minus1_gap2. exact Hab.
    + lia.
  - apply IH. exact Htail.
Qed.

Lemma all_ge_2_map_odd :
  forall Bx xs,
    all_ge_2 xs ->
    all_ge_2 (map (fun j => Bx + two_j_minus1 j) xs).
Proof.
  intros Bx xs Hge.
  revert Bx Hge.
  induction xs as [|a xs IH]; intros Bx Hge; simpl; auto.
  destruct Hge as [Ha Htail].
  split.
  - rewrite two_j_minus1_formula.
    lia.
  - apply IH. exact Htail.
Qed.

(*@inline@[[The next block transports Zeckendorf admissibility through the even and odd embedding maps that together define the pairing support.]]@*)

Lemma even_band_valid :
  forall x, zeck_valid (even_band base_params x).
Proof.
  intro x.
  unfold even_band, base_params.
  pose proof (Z0_valid x) as [Hdec [Hadj Hge]].
  split.
  - apply strictly_decreasing_map_two. exact Hdec.
  - split.
    + apply no_adjacent_map_two. exact Hadj.
    + apply all_ge_2_map_two. exact Hge.
Qed.

Lemma odd_band_valid :
  forall x y, zeck_valid (odd_band base_params x y).
Proof.
  intros x y.
  unfold odd_band, base_params.
  pose proof (Z0_valid y) as [Hdec [Hadj Hge]].
  split.
  - apply strictly_decreasing_map_odd. exact Hdec.
  - split.
    + apply no_adjacent_map_odd. exact Hadj.
    + apply all_ge_2_map_odd. exact Hge.
Qed.

(*@unicodemath@[[∀ x e, e ∈ even_band(x) ⇒ e < B(x).]]@*)

Lemma even_band_lt_B :
  forall x e, In e (even_band base_params x) -> e < B base_params x.
Proof.
  intros x e Hin.
  unfold even_band, base_params in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [He Hj]].
  subst e.
  assert (Hjlt : j < r0 x).
  - apply Z0_indices_below_r0. exact Hj.
  - unfold base_params.
    unfold B.
    unfold two.
    simpl.
    replace (2 * r0 x) with (r0 x + r0 x) by lia.
    lia.
Qed.

(*@unicodemath@[[∀ x y o, o ∈ odd_band(x, y) ⇒ B(x) + 1 ≤ o.]]@*)

Lemma odd_band_ge_B1 :
  forall x y o, In o (odd_band base_params x y) -> S (B base_params x) <= o.
Proof.
  intros x y o Hin.
  unfold odd_band, base_params in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [Ho Hj]].
  subst o.
  assert (Hj2 : 2 <= j).
  - apply all_ge_2_in with (xs:=Z0 y); [|exact Hj].
    destruct (Z0_valid y) as [_ [_ Hge]]; exact Hge.
  - assert (Hj1 : 1 <= j) by lia.
    assert (Hodd1 : 1 <= two_j_minus1 j) by (apply two_j_minus1_ge_1; exact Hj1).
    unfold B.
    unfold base_params.
    simpl.
    lia.
Qed.

(*@inline@[[The odd band lies strictly above the even band: every odd-band index dominates every even-band index attached to the same left coordinate.]]@*)

Lemma odd_band_gt_even_band :
  forall x y o e,
    In o (odd_band base_params x y) ->
    In e (even_band base_params x) ->
    o > e.
Proof.
  intros x y o e Ho He.
  pose proof (odd_band_ge_B1 x y o Ho) as Hob.
  pose proof (even_band_lt_B x e He) as Heb.
  lia.
Qed.

Lemma odd_band_gap_even_band :
  forall x y o e,
    In o (odd_band base_params x y) ->
    In e (even_band base_params x) ->
    o >= e + 2.
Proof.
  intros x y o e Ho He.
  pose proof (odd_band_ge_B1 x y o Ho) as Hob.
  pose proof (even_band_lt_B x e He) as Heb.
  lia.
Qed.

Lemma all_ge_2_app :
  forall xs ys, all_ge_2 xs -> all_ge_2 ys -> all_ge_2 (xs ++ ys).
Proof.
  induction xs as [|a xs IH]; intros ys Hx Hy; simpl.
  - exact Hy.
  - destruct Hx as [Ha Hxs]. split; [exact Ha|]. apply IH; assumption.
Qed.

Lemma strictly_decreasing_app :
  forall xs ys,
    strictly_decreasing xs ->
    strictly_decreasing ys ->
    (forall x y, In x xs -> In y ys -> x > y) ->
    strictly_decreasing (xs ++ ys).
Proof.
  induction xs as [|a xs IH]; intros ys Hx Hy Hcross; simpl.
  - exact Hy.
  - destruct xs as [|b xs'].
    + simpl.
      destruct ys as [|y ys'].
      * simpl. exact I.
      * simpl. split.
        -- apply Hcross; simpl; auto.
        -- exact Hy.
    + simpl in Hx.
      destruct Hx as [Hab Htail].
      simpl.
      split; [exact Hab|].
      apply IH; try assumption.
      intros x y Hinx Hiny.
      apply Hcross; simpl; auto.
Qed.

Lemma no_adjacent_app :
  forall xs ys,
    no_adjacent xs ->
    no_adjacent ys ->
    (forall x y, In x xs -> In y ys -> x >= y + 2) ->
    no_adjacent (xs ++ ys).
Proof.
  induction xs as [|a xs IH]; intros ys Hx Hy Hcross; simpl.
  - exact Hy.
  - destruct xs as [|b xs'].
    + simpl.
      destruct ys as [|y ys'].
      * simpl. exact I.
      * simpl. split.
        -- apply Hcross; simpl; auto.
        -- exact Hy.
    + simpl in Hx.
      destruct Hx as [Hab Htail].
      simpl.
      split; [exact Hab|].
      apply IH; try assumption.
      intros x y Hinx Hiny.
      apply Hcross; simpl; auto.
Qed.

(*@inline@[[`odd_even_concat_valid` is the structural compatibility lemma for pairing: the two bands remain sufficiently separated that their concatenation is again a valid Zeckendorf support.]]@*)

Lemma odd_even_concat_valid :
  forall x y,
    zeck_valid (odd_band base_params x y ++ even_band base_params x).
Proof.
  intros x y.
  pose proof (odd_band_valid x y) as [Hdec_o [Hadj_o Hge_o]].
  pose proof (even_band_valid x) as [Hdec_e [Hadj_e Hge_e]].
  split.
  - eapply strictly_decreasing_app; eauto.
    intros o e Ho He.
    apply odd_band_gt_even_band with (x:=x) (y:=y); assumption.
  - split.
    + eapply no_adjacent_app; eauto.
      intros o e Ho He.
      apply odd_band_gap_even_band with (x:=x) (y:=y); assumption.
    + apply all_ge_2_app; assumption.
Qed.

Lemma pair_base_as_odd_even_sum :
  forall x y,
    pair base_params x y =
    sum_fib (odd_band base_params x y ++ even_band base_params x).
Proof.
  intros x y.
  unfold pair.
  rewrite !sum_fib_app.
  lia.
Qed.

(*@inline@[[The carryless code therefore admits a canonical odd/even support decomposition.]]@*)

(*@unicodemath@[[Z0(pair(x, y)) = odd_band(x, y) ⧺ even_band(x).]]@*)

Theorem Z0_pair_is_concat :
  forall x y,
    Z0 (pair base_params x y) =
    odd_band base_params x y ++ even_band base_params x.
Proof.
  intros x y.
  rewrite pair_base_as_odd_even_sum.
  apply Z0_of_sum_fib.
  apply odd_even_concat_valid.
Qed.

(*@section@[[SUPPORT SPLITTING]]@*)

Lemma even_band_even :
  forall x k,
    In k (even_band base_params x) ->
    Nat.even k = true.
Proof.
  intros x k Hin.
  unfold even_band, base_params in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [e [He _]].
  subst k.
  apply even_two.
Qed.

Lemma odd_band_even_false :
  forall x y k,
    In k (odd_band base_params x y) ->
    Nat.even k = false.
Proof.
  intros x y k Hin.
  unfold odd_band, base_params in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [Hk Hj]].
  subst k.
  assert (Hj2 : 2 <= j).
  - apply all_ge_2_in with (xs:=Z0 y); [|exact Hj].
    destruct (Z0_valid y) as [_ [_ Hge]]; exact Hge.
  - assert (Hj1 : 1 <= j) by lia.
    unfold B.
    rewrite even_double_plus.
    apply odd_two_j_minus1. exact Hj1.
Qed.

Lemma odd_band_odd_ge_B1_true :
  forall x y k,
    In k (odd_band base_params x y) ->
    odd_ge_B1 (B base_params x) k = true.
Proof.
  intros x y k Hin.
  unfold odd_ge_B1. rewrite <- Nat.negb_even.
  rewrite (odd_band_even_false x y k Hin). cbn [negb andb].
  apply Nat.leb_le. apply (odd_band_ge_B1 x y k). exact Hin.
Qed.

Lemma even_band_odd_ge_B1_false :
  forall x k,
    In k (even_band base_params x) ->
    odd_ge_B1 (B base_params x) k = false.
Proof.
  intros x k Hin.
  unfold odd_ge_B1. rewrite <- Nat.negb_even.
  rewrite (even_band_even x k Hin). reflexivity.
Qed.

Lemma filter_false_nil :
  forall (A : Type) (p : A -> bool) (xs : list A),
    (forall a, In a xs -> p a = false) ->
    filter p xs = [].
Proof.
  intros A p xs Hp.
  induction xs as [|a xs IH]; simpl.
  - reflexivity.
  - assert (Ha : p a = false) by (apply Hp; simpl; auto).
    rewrite Ha.
    apply IH.
    intros b Hb.
    apply Hp.
    simpl; auto.
Qed.

Lemma filter_true_id :
  forall (A : Type) (p : A -> bool) (xs : list A),
    (forall a, In a xs -> p a = true) ->
    filter p xs = xs.
Proof.
  intros A p xs Hp.
  induction xs as [|a xs IH]; simpl.
  - reflexivity.
  - assert (Ha : p a = true) by (apply Hp; simpl; auto).
    rewrite Ha.
    simpl.
    f_equal.
    apply IH.
    intros b Hb.
    apply Hp.
    simpl; auto.
Qed.

(*@inline@[[The final filtering corollaries recover both pairing bands directly from the canonical support of a paired code.]]@*)

(*@unicodemath@[[∀ x y, { e ∈ Z0(pair(x, y)) ∣ 2 ∣ e } = even_band(x).]]@*)

Corollary Z0_even_split :
  forall x y,
    filter Nat.even (Z0 (pair base_params x y)) = even_band base_params x.
Proof.
  intros x y.
  rewrite Z0_pair_is_concat.
  rewrite filter_app.
  assert (Hodd_nil : filter Nat.even (odd_band base_params x y) = []).
  - apply filter_false_nil. intros a Ha. apply (odd_band_even_false x y a); exact Ha.
  - assert (Heven_id :
      filter Nat.even (even_band base_params x) = even_band base_params x).
    + apply filter_true_id. intros a Ha. apply (even_band_even x a); exact Ha.
    + rewrite Hodd_nil, Heven_id. reflexivity.
Qed.

(*@unicodemath@[[∀ x y, { k ∈ Z0(pair(x, y)) ∣ 2 ∤ k ∧ B(x) + 1 ≤ k }]][[= odd_band(x, y).]]@*)

Corollary Z0_odd_split :
  forall x y,
    filter (odd_ge_B1 (B base_params x))
      (Z0 (pair base_params x y)) =
    odd_band base_params x y.
Proof.
  intros x y.
  rewrite Z0_pair_is_concat.
  rewrite filter_app.
  assert (Hodd_id :
    filter (odd_ge_B1 (B base_params x))
      (odd_band base_params x y) =
    odd_band base_params x y).
  - apply filter_true_id. intros a Ha. apply (odd_band_odd_ge_B1_true x y a); exact Ha.
  - assert (Heven_nil :
      filter (odd_ge_B1 (B base_params x)) (even_band base_params x) = []).
    + apply filter_false_nil. intros a Ha. apply (even_band_odd_ge_B1_false x a); exact Ha.
    + rewrite Hodd_id, Heven_nil.
      rewrite app_nil_r.
      reflexivity.
Qed.
