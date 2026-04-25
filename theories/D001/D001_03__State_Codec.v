(*D001_03__State_Codec.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / D001_03__State_Codec                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  In this file we implement the carryless state codec of the Iterant Machine.

  We encode a machine state as a triple `(IP, R1, R2)`, place its three
  payloads into the fixed disjoint bands constructed in `D001_02`, and then
  read the resulting global support as one Zeckendorf numeral. We also show
  that decoding recovers exactly the bounded states and normalizes arbitrary
  raw codes into that image.

*)

From D001 Require Export D001_02__Carryless_Bands.

Record IterantState : Type := Build_IterantState
{
  state_ip : nat;
  state_r1 : nat;
  state_r2 : nat
}.

(*
│
│          `IterantState` is the bare semantic payload of the machine
│          before any encoding is applied. We keep it as a simple
│          record of three naturals so that all representational
│          discipline is carried by the later well-formedness
│          predicate rather than baked into the datatype itself.
│
*)

(*  st = (ip, r1, r2) ∈ ℕ³, state_well_formed(st) supplies the band bounds.   *)

(*
│
│          `state_well_formed` is the static range discipline of the
│          machine state: each component must fit inside the Fibonacci
│          window reserved for its band.
│
*)

(*    state_well_formed(ip, r1, r2) ≔ ip < ip_limit ∧ r1 < r1_limit ∧ r2 <    *)
(*                                 r2_limit.                                  *)

Definition state_well_formed (st : IterantState) : Prop :=
  state_ip st < ip_limit /\
  state_r1 st < r1_limit /\
  state_r2 st < r2_limit.

(*
│
│          `state_support` concatenates the three band supports in
│          descending-band order, and `encode_state` reads that
│          combined support as a single natural number.
│
*)

Definition state_support (st : IterantState) : list nat :=
  r2_support (state_r2 st) ++
  r1_support (state_r1 st) ++
  ip_support (state_ip st).

(*               encode_state(st) = sum_fib(state_support(st))                *)
(*      = sum_fib(r2_support(state_r2(st)) ⧺ r1_support(state_r1(st)) ⧺       *)
(*                         ip_support(state_ip(st))).                         *)

Definition encode_state (st : IterantState) : nat :=
  sum_fib (state_support st).

(*
│
│          The three auxiliary decoders first work at the level of
│          supports. Each one filters a global support down to one
│          machine band, subtracts the corresponding offset, and then
│          reassembles the recovered local support by `sum_fib`.
│
*)

(*  decode_ip_from_support(zn) = sum_fib(band_indices(IP_offset, K_IP, zn))   *)
(*  decode_r1_from_support(zn) = sum_fib(band_indices(R1_offset, K_R1, zn))   *)
(*  decode_r2_from_support(zn) = sum_fib(band_indices(R2_offset, K_R2, zn)).  *)

Definition decode_ip_from_support (zn : list nat) : nat :=
  sum_fib (band_indices IP_offset K_IP zn).

Definition decode_r1_from_support (zn : list nat) : nat :=
  sum_fib (band_indices R1_offset K_R1 zn).

Definition decode_r2_from_support (zn : list nat) : nat :=
  sum_fib (band_indices R2_offset K_R2 zn).

Definition decode_ip (s : nat) : nat :=
  decode_ip_from_support (Z0 s).

Definition decode_r1 (s : nat) : nat :=
  decode_r1_from_support (Z0 s).

Definition decode_r2 (s : nat) : nat :=
  decode_r2_from_support (Z0 s).

(*
│
│          `decode_state` computes the canonical support `Z0(s)` once
│          and reuses it across the three band decoders. In this way,
│          the greedy Zeckendorf extraction is performed only once
│          rather than separately for each register projection.
│
*)

(*
│
│          `decode_state_from_support` slices a canonical support into
│          the `IP`, `R1`, and `R2` windows and reconstructs the
│          corresponding machine state. The resulting `decode_state`
│          is total on all naturals, but it is a projection into the
│          bounded state image rather than a global inverse of
│          `encode_state` on arbitrary codes.
│
*)

Definition decode_state_from_support (zn : list nat) : IterantState :=
  Build_IterantState
    (decode_ip_from_support zn)
    (decode_r1_from_support zn)
    (decode_r2_from_support zn).

Definition decode_state (s : nat) : IterantState :=
  decode_state_from_support (Z0 s).

(*          normalize_state_code(s) = encode_state(decode_state(s))           *)
(* valid_state_code(s) ≔ ∃ st, state_well_formed(st) ∧ s = encode_state(st).  *)

Definition normalize_state_code (s : nat) : nat :=
  encode_state (decode_state s).

Definition valid_state_code (s : nat) : Prop :=
  exists st,
    state_well_formed st /\
    s = encode_state st.

(*
│
│          `state_well_formed_build` is the canonical constructor
│          lemma for the state-range invariant. It lets later proofs
│          rebuild a well-formed state from its three component bounds
│          without reopening the conjunction structure by hand.
│
*)

Lemma state_well_formed_build :
  forall ip r1 r2,
    ip < ip_limit ->
    r1 < r1_limit ->
    r2 < r2_limit ->
    state_well_formed (Build_IterantState ip r1 r2).
Proof.
  intros ip r1 r2 Hip Hr1 Hr2.
  split.
  - exact Hip.
  - split.
    + exact Hr1.
    + exact Hr2.
Qed.

(*
│
│          The next two recursive predicates are local bookkeeping
│          devices for support arithmetic. `all_ge m xs` records that
│          every index of `xs` lies at or above `m`, while `all_lt m
│          xs` records that every index lies strictly below `m`.
│          Together they let us express window containment in a form
│          stable under filtering and offset subtraction.
│
*)

(*                      all_ge(m, xs) ≡ ∀ x ∈ xs, m ≤ x                       *)
(*                      all_lt(m, xs) ≡ ∀ x ∈ xs, x < m.                      *)

Fixpoint all_ge (m : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => m <= x /\ all_ge m xs'
  end.

Fixpoint all_lt (m : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => x < m /\ all_lt m xs'
  end.

Lemma all_ge_weaken :
  forall m n xs,
    all_ge m xs ->
    n <= m ->
    all_ge n xs.
Proof.
  induction xs as [|x xs IH]; intros Hge Hnm; simpl in *; auto.
  destruct Hge as [Hx Hxs].
  split.
  - lia.
  - apply IH; assumption.
Qed.

Lemma strictly_decreasing_head_gt_tail :
  forall a xs y,
    strictly_decreasing (a :: xs) ->
    In y xs ->
    a > y.
Proof.
  intros a xs y Hdec Hin.
  revert a y Hdec Hin.
  induction xs as [|b xs IH]; intros a y Hdec Hin.
  - contradiction.
  - simpl in Hdec.
    destruct Hdec as [Hab Htail].
    simpl in Hin.
    destruct Hin as [<-|Hin].
    + exact Hab.
    + pose proof (IH b y Htail Hin) as Hby.
      lia.
Qed.

Lemma no_adjacent_head_gap_tail :
  forall a xs y,
    no_adjacent (a :: xs) ->
    In y xs ->
    a >= y + 2.
Proof.
  intros a xs y Hadj Hin.
  revert a y Hadj Hin.
  induction xs as [|b xs IH]; intros a y Hadj Hin.
  - contradiction.
  - simpl in Hadj.
    destruct Hadj as [Hab Htail].
    simpl in Hin.
    destruct Hin as [<-|Hin].
    + exact Hab.
    + pose proof (IH b y Htail Hin) as Hby.
      lia.
Qed.

Lemma strictly_decreasing_filter :
  forall (p : nat -> bool) xs,
    strictly_decreasing xs ->
    strictly_decreasing (filter p xs).
Proof.
  intros p xs Hdec.
  induction xs as [|a xs IH]; simpl; auto.
  destruct xs as [|b xs']; simpl in *.
  - destruct (p a); simpl; auto.
  - destruct Hdec as [Hab Htail].
    destruct (p a) eqn:Hpa.
    + change (strictly_decreasing (a :: filter p (b :: xs'))).
      remember (filter p (b :: xs')) as zs eqn:Hzs.
      destruct zs as [|c ys].
      * simpl.
        exact I.
      * simpl.
        change (a > c /\ strictly_decreasing (c :: ys)).
        split.
        -- apply strictly_decreasing_head_gt_tail with (xs:=b :: xs').
           ++ split; assumption.
           ++ assert (Hin_filter : In c (filter p (b :: xs'))) by (rewrite <- Hzs; simpl; auto).
              apply filter_In in Hin_filter.
              tauto.
        -- rewrite Hzs.
           apply IH.
           exact Htail.
    + apply IH.
      exact Htail.
Qed.

Lemma no_adjacent_filter :
  forall (p : nat -> bool) xs,
    no_adjacent xs ->
    no_adjacent (filter p xs).
Proof.
  intros p xs Hadj.
  induction xs as [|a xs IH]; simpl; auto.
  destruct xs as [|b xs']; simpl in *.
  - destruct (p a); simpl; auto.
  - destruct Hadj as [Hab Htail].
    destruct (p a) eqn:Hpa.
    + change (no_adjacent (a :: filter p (b :: xs'))).
      remember (filter p (b :: xs')) as zs eqn:Hzs.
      destruct zs as [|c ys].
      * simpl.
        exact I.
      * simpl.
        change (a >= c + 2 /\ no_adjacent (c :: ys)).
        split.
        -- apply no_adjacent_head_gap_tail with (xs:=b :: xs').
           ++ split; assumption.
           ++ assert (Hin_filter : In c (filter p (b :: xs'))) by (rewrite <- Hzs; simpl; auto).
              apply filter_In in Hin_filter.
              tauto.
        -- rewrite Hzs.
           apply IH.
           exact Htail.
    + apply IH.
      exact Htail.
Qed.

Lemma band_pred_true_bounds :
  forall offset K k,
    band_pred offset K k = true ->
    offset + 2 <= k /\ k < offset + K.
Proof.
  intros offset K k Hpred.
  unfold band_pred in Hpred.
  apply andb_true_iff in Hpred.
  destruct Hpred as [Hlow Hhigh].
  split.
  - apply Nat.leb_le. exact Hlow.
  - apply Nat.ltb_lt. exact Hhigh.
Qed.

Lemma all_ge_filter_band_pred :
  forall offset K zn,
    all_ge (offset + 2) (filter (band_pred offset K) zn).
Proof.
  intros offset K zn.
  induction zn as [|a zn IH]; simpl; auto.
  destruct (band_pred offset K a) eqn:Ha; simpl.
  - destruct (band_pred_true_bounds offset K a Ha) as [Hlow _].
    split; [exact Hlow|exact IH].
  - exact IH.
Qed.

Lemma all_lt_filter_band_pred :
  forall offset K zn,
    all_lt (offset + K) (filter (band_pred offset K) zn).
Proof.
  intros offset K zn.
  induction zn as [|a zn IH]; simpl; auto.
  destruct (band_pred offset K a) eqn:Ha; simpl.
  - destruct (band_pred_true_bounds offset K a Ha) as [_ Hhigh].
    split; [exact Hhigh|exact IH].
  - exact IH.
Qed.

Lemma strictly_decreasing_map_sub :
  forall offset xs,
    strictly_decreasing xs ->
    all_ge offset xs ->
    strictly_decreasing (map (fun k => k - offset) xs).
Proof.
  intros offset xs Hdec Hall.
  induction xs as [|a xs IH]; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hdec as [Hab Htail].
  destruct Hall as [Ha Hall].
  destruct Hall as [Hb Hall'].
  split.
  - lia.
  - apply IH.
    + exact Htail.
    + split; assumption.
Qed.

Lemma no_adjacent_map_sub :
  forall offset xs,
    no_adjacent xs ->
    all_ge offset xs ->
    no_adjacent (map (fun k => k - offset) xs).
Proof.
  intros offset xs Hadj Hall.
  induction xs as [|a xs IH]; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hadj as [Hab Htail].
  destruct Hall as [Ha Hall].
  destruct Hall as [Hb Hall'].
  split.
  - lia.
  - apply IH.
    + exact Htail.
    + split; assumption.
Qed.

Lemma all_ge_2_map_sub :
  forall offset xs,
    all_ge (offset + 2) xs ->
    all_ge_2 (map (fun k => k - offset) xs).
Proof.
  intros offset xs Hge.
  induction xs as [|a xs IH]; simpl; auto.
  destruct Hge as [Ha Hxs].
  split.
  - lia.
  - apply IH.
    exact Hxs.
Qed.

Lemma all_lt_map_sub :
  forall offset K xs,
    all_ge offset xs ->
    all_lt (offset + K) xs ->
    all_lt K (map (fun k => k - offset) xs).
Proof.
  intros offset K xs Hge Hlt.
  induction xs as [|a xs IH]; simpl; auto.
  destruct Hge as [Ha Hge'].
  destruct Hlt as [Ha' Hlt'].
  split.
  - lia.
  - apply IH; assumption.
Qed.

(*
│
│          At this point we have the abstract projection calculus for
│          supports. Filtering by a band predicate preserves
│          Zeckendorf validity, subtracting the offset restores local
│          coordinates, and the resulting local support remains
│          strictly below the band width `K`.
│
*)

(*          zeck_valid(zn) ⇒ zeck_valid(band_indices(offset, K, zn))          *)
(*                   all_lt(K, band_indices(offset, K, zn))                   *)
(* band_indices = filter by the band window, then translate back by −offset.  *)

Lemma band_indices_valid :
  forall offset K zn,
    zeck_valid zn ->
    zeck_valid (band_indices offset K zn).
Proof.
  intros offset K zn [Hdec [Hadj Hge]].
  unfold band_indices.
  split.
  - apply strictly_decreasing_map_sub.
    + apply strictly_decreasing_filter. exact Hdec.
    + apply all_ge_weaken with (m:=offset + 2).
      * apply all_ge_filter_band_pred.
      * lia.
  - split.
    + apply no_adjacent_map_sub.
      * apply no_adjacent_filter. exact Hadj.
      * apply all_ge_weaken with (m:=offset + 2).
        -- apply all_ge_filter_band_pred.
        -- lia.
    + apply all_ge_2_map_sub.
      apply all_ge_filter_band_pred.
Qed.

Lemma band_indices_all_lt :
  forall offset K zn,
    all_lt K (band_indices offset K zn).
Proof.
  intros offset K zn.
  unfold band_indices.
  apply all_lt_map_sub.
  - apply all_ge_weaken with (m:=offset + 2).
    + apply all_ge_filter_band_pred.
    + lia.
  - apply all_lt_filter_band_pred.
Qed.

Lemma sum_fib_lt_fib_of_valid_all_lt :
  forall xs K,
    zeck_valid xs ->
    all_lt K xs ->
    2 <= K ->
    sum_fib xs < fib K.
Proof.
  intros xs K Hvalid Hlt HK.
  destruct xs as [|k xs'].
  - simpl.
    assert (Hpos : fib K >= 1) by (apply fib_pos; lia).
    lia.
  - simpl in Hlt.
    destruct Hlt as [Hk _].
    eapply Nat.lt_le_trans.
    + apply sum_fib_lt_next_of_valid.
      exact Hvalid.
    + apply fib_le_of_le.
      lia.
Qed.

Lemma r1_ip_support_valid :
  forall ip r1,
    ip < ip_limit ->
    r1 < r1_limit ->
    zeck_valid (r1_support r1 ++ ip_support ip).
Proof.
  intros ip r1 Hip Hr1.
  pose proof (band_support_valid R1_offset r1) as Hr1v.
  pose proof (band_support_valid IP_offset ip) as Hipv.
  destruct Hr1v as [Hdec1 [Hadj1 Hge1]].
  destruct Hipv as [Hdec0 [Hadj0 Hge0]].
  split.
  - apply strictly_decreasing_app.
    + exact Hdec1.
    + exact Hdec0.
    + intros x y Hx Hy.
      apply r1_support_gt_ip_support with (r1:=r1) (ip:=ip); assumption.
  - split.
    + apply no_adjacent_app.
      * exact Hadj1.
      * exact Hadj0.
      * intros x y Hx Hy.
        apply r1_support_gap_ip_support with (r1:=r1) (ip:=ip); assumption.
    + apply all_ge_2_app; assumption.
Qed.

Lemma r2_support_gt_r1_ip_support :
  forall ip r1 r2 x y,
    ip < ip_limit ->
    r1 < r1_limit ->
    r2 < r2_limit ->
    In x (r2_support r2) ->
    In y (r1_support r1 ++ ip_support ip) ->
    x > y.
Proof.
  intros ip r1 r2 x y Hip Hr1 Hr2 Hx Hy.
  apply in_app_or in Hy.
  destruct Hy as [Hy|Hy].
  - exact (r2_support_gt_r1_support r2 r1 x y Hr2 Hr1 Hx Hy).
  - exact (r2_support_gt_ip_support r2 ip x y Hr2 Hip Hx Hy).
Qed.

Lemma r2_support_gap_r1_ip_support :
  forall ip r1 r2 x y,
    ip < ip_limit ->
    r1 < r1_limit ->
    r2 < r2_limit ->
    In x (r2_support r2) ->
    In y (r1_support r1 ++ ip_support ip) ->
    x >= y + 2.
Proof.
  intros ip r1 r2 x y Hip Hr1 Hr2 Hx Hy.
  apply in_app_or in Hy.
  destruct Hy as [Hy|Hy].
  - exact (r2_support_gap_r1_support r2 r1 x y Hr2 Hr1 Hx Hy).
  - exact (r2_support_gap_ip_support r2 ip x y Hr2 Hip Hx Hy).
Qed.

(*
│
│          We can now reassemble the three machine bands into one
│          global Zeckendorf support. The crucial point is geometric:
│          `R1` lies safely above `IP`, and `R2` lies safely above
│          both, so concatenation preserves strict decrease and the
│          non-adjacency gap.
│
*)

(*state_well_formed(ip, r1, r2) ⇒ zeck_valid(r2_support(r2) ++ r1_support(r1) *)
(*                            ++ ip_support(ip)).                             *)

Theorem state_support_valid :
  forall st,
    state_well_formed st ->
    zeck_valid (state_support st).
Proof.
  intros [ip r1 r2] [Hip [Hr1 Hr2]].
  unfold state_support.
  pose proof (band_support_valid R2_offset r2) as Hr2v.
  pose proof (r1_ip_support_valid ip r1 Hip Hr1) as H10v.
  destruct Hr2v as [Hdec2 [Hadj2 Hge2]].
  destruct H10v as [Hdec10 [Hadj10 Hge10]].
  split.
  - apply strictly_decreasing_app.
    + exact Hdec2.
    + exact Hdec10.
    + intros x y Hx Hy.
      exact (r2_support_gt_r1_ip_support ip r1 r2 x y Hip Hr1 Hr2 Hx Hy).
  - split.
    + apply no_adjacent_app.
      * exact Hadj2.
      * exact Hadj10.
      * intros x y Hx Hy.
        exact (r2_support_gap_r1_ip_support ip r1 r2 x y Hip Hr1 Hr2 Hx Hy).
    + apply all_ge_2_app; assumption.
Qed.

(*
│
│          `encode_state_support` identifies the canonical support of
│          an encoded state with the intended three-band support
│          decomposition. It is the exact bridge from the numeric code
│          back to the geometric band layout.
│
*)

(*     state_well_formed(st) ⇒ Z0(encode_state(st)) = state_support(st).      *)

Theorem encode_state_support :
  forall st,
    state_well_formed st ->
    Z0 (encode_state st) = state_support st.
Proof.
  intros st Hwf.
  unfold encode_state.
  apply Z0_of_sum_fib.
  apply state_support_valid.
  exact Hwf.
Qed.

(*
│
│          `encode_state_as_components` exposes the state code as the
│          sum of three independent band codes. This additive
│          decomposition is the algebraic bridge used later in the
│          arithmetization layer.
│
*)

Theorem encode_state_as_components :
  forall st,
    encode_state st =
    r2_code (state_r2 st) +
    r1_code (state_r1 st) +
    ip_code (state_ip st).
Proof.
  intros [ip r1 r2].
  unfold encode_state, state_support, r2_code, r1_code, ip_code, band_code.
  repeat rewrite sum_fib_app.
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

(*
│
│          `filter_state_support` is the bookkeeping lemma behind the
│          projection corollaries: filtering a full state support is
│          the same as filtering each band separately and preserving
│          their concatenation order.
│
*)

Lemma filter_state_support :
  forall (p : nat -> bool) ip r1 r2,
    filter p (state_support (Build_IterantState ip r1 r2)) =
    ((filter p (r2_support r2) ++ filter p (r1_support r1)) ++
     filter p (ip_support ip)).
Proof.
  intros p ip r1 r2.
  unfold state_support.
  repeat rewrite filter_app.
  rewrite app_assoc.
  reflexivity.
Qed.

(*
│
│          We now read the global support back through the three band
│          predicates. Because each predicate is true on its own band
│          and false on the two foreign bands, filtering
│          `Z0(encode_state(st))` by that predicate isolates exactly
│          one component support and deletes the other two.
│
*)

(*      filter(ip_pred, Z0(encode_state(st))) = ip_support(state_ip(st))      *)
(*      filter(r1_pred, Z0(encode_state(st))) = r1_support(state_r1(st))      *)
(*     filter(r2_pred, Z0(encode_state(st))) = r2_support(state_r2(st)).      *)

Corollary ip_support_split :
  forall st,
    state_well_formed st ->
    filter ip_pred (Z0 (encode_state st)) = ip_support (state_ip st).
Proof.
  intros [ip r1 r2] [Hip [Hr1 Hr2]].
  rewrite encode_state_support by (repeat split; assumption).
  replace
    (filter ip_pred (state_support (Build_IterantState ip r1 r2)))
    with
    ((filter ip_pred (r2_support r2) ++ filter ip_pred (r1_support r1)) ++
     filter ip_pred (ip_support ip)).
  2:{
    unfold state_support.
    repeat rewrite filter_app.
    rewrite app_assoc.
    reflexivity.
  }
  assert (Hr2_nil : filter ip_pred (r2_support r2) = []).
  - apply filter_false_nil.
    intros a Ha.
    exact (ip_pred_false_on_r2_support r2 a Hr2 Ha).
  - assert (Hr1_nil : filter ip_pred (r1_support r1) = []).
    + apply filter_false_nil.
      intros a Ha.
      exact (ip_pred_false_on_r1_support r1 a Hr1 Ha).
    + assert (Hip_id : filter ip_pred (ip_support ip) = ip_support ip).
      * apply filter_true_id.
        intros a Ha.
        exact (ip_pred_true_on_ip_support ip a Hip Ha).
      * rewrite Hr2_nil, Hr1_nil, Hip_id.
        simpl.
        reflexivity.
Qed.

Corollary r1_support_split :
  forall st,
    state_well_formed st ->
    filter r1_pred (Z0 (encode_state st)) = r1_support (state_r1 st).
Proof.
  intros [ip r1 r2] [Hip [Hr1 Hr2]].
  rewrite encode_state_support by (repeat split; assumption).
  replace
    (filter r1_pred (state_support (Build_IterantState ip r1 r2)))
    with
    ((filter r1_pred (r2_support r2) ++ filter r1_pred (r1_support r1)) ++
     filter r1_pred (ip_support ip)).
  2:{
    unfold state_support.
    repeat rewrite filter_app.
    rewrite app_assoc.
    reflexivity.
  }
  assert (Hr2_nil : filter r1_pred (r2_support r2) = []).
  - apply filter_false_nil.
    intros a Ha.
    exact (r1_pred_false_on_r2_support r2 a Hr2 Ha).
  - assert (Hr1_id : filter r1_pred (r1_support r1) = r1_support r1).
    + apply filter_true_id.
      intros a Ha.
      exact (r1_pred_true_on_r1_support r1 a Hr1 Ha).
    + assert (Hip_nil : filter r1_pred (ip_support ip) = []).
      * apply filter_false_nil.
        intros a Ha.
        exact (r1_pred_false_on_ip_support ip a Hip Ha).
      * rewrite Hr2_nil, Hr1_id, Hip_nil.
        simpl.
        rewrite app_nil_r.
        reflexivity.
Qed.

Corollary r2_support_split :
  forall st,
    state_well_formed st ->
    filter r2_pred (Z0 (encode_state st)) = r2_support (state_r2 st).
Proof.
  intros [ip r1 r2] [Hip [Hr1 Hr2]].
  rewrite encode_state_support by (repeat split; assumption).
  replace
    (filter r2_pred (state_support (Build_IterantState ip r1 r2)))
    with
    ((filter r2_pred (r2_support r2) ++ filter r2_pred (r1_support r1)) ++
     filter r2_pred (ip_support ip)).
  2:{
    unfold state_support.
    repeat rewrite filter_app.
    rewrite app_assoc.
    reflexivity.
  }
  assert (Hr2_id : filter r2_pred (r2_support r2) = r2_support r2).
  - apply filter_true_id.
    intros a Ha.
    exact (r2_pred_true_on_r2_support r2 a Hr2 Ha).
  - assert (Hr1_nil : filter r2_pred (r1_support r1) = []).
    + apply filter_false_nil.
      intros a Ha.
      exact (r2_pred_false_on_r1_support r1 a Hr1 Ha).
    + assert (Hip_nil : filter r2_pred (ip_support ip) = []).
      * apply filter_false_nil.
        intros a Ha.
        exact (r2_pred_false_on_ip_support ip a Hip Ha).
      * rewrite Hr2_id, Hr1_nil, Hip_nil.
        simpl.
        repeat rewrite app_nil_r.
        reflexivity.
Qed.

(*
│
│          The three component roundtrip lemmas are now immediate:
│          isolate the relevant support, subtract back the band
│          offset, and appeal to `Z0_sound` to reconstruct the
│          original payload.
│
*)

(*     state_well_formed(st) ⇒ decode_ip(encode_state(st)) = state_ip(st)     *)
(*     state_well_formed(st) ⇒ decode_r1(encode_state(st)) = state_r1(st)     *)
(*    state_well_formed(st) ⇒ decode_r2(encode_state(st)) = state_r2(st).     *)

Lemma decode_ip_encode_state :
  forall st,
    state_well_formed st ->
    decode_ip (encode_state st) = state_ip st.
Proof.
  intros st Hwf.
  unfold decode_ip, decode_ip_from_support, band_indices.
  rewrite ip_support_split by exact Hwf.
  rewrite map_sub_band_support.
  apply Z0_sound.
Qed.

Lemma decode_r1_encode_state :
  forall st,
    state_well_formed st ->
    decode_r1 (encode_state st) = state_r1 st.
Proof.
  intros st Hwf.
  unfold decode_r1, decode_r1_from_support, band_indices.
  rewrite r1_support_split by exact Hwf.
  rewrite map_sub_band_support.
  apply Z0_sound.
Qed.

Lemma decode_r2_encode_state :
  forall st,
    state_well_formed st ->
    decode_r2 (encode_state st) = state_r2 st.
Proof.
  intros st Hwf.
  unfold decode_r2, decode_r2_from_support, band_indices.
  rewrite r2_support_split by exact Hwf.
  rewrite map_sub_band_support.
  apply Z0_sound.
Qed.

(*
│
│          `decode_state_encode_state` is the roundtrip theorem for
│          the concrete state codec: every well-formed state is
│          recovered exactly after encoding and then decoding.
│
*)

(*        state_well_formed(st) ⇒ decode_state(encode_state(st)) = st.        *)

Theorem decode_state_encode_state :
  forall st,
    state_well_formed st ->
    decode_state (encode_state st) = st.
Proof.
  intros [ip r1 r2] Hwf.
  change
    (Build_IterantState
       (decode_ip (encode_state (Build_IterantState ip r1 r2)))
       (decode_r1 (encode_state (Build_IterantState ip r1 r2)))
       (decode_r2 (encode_state (Build_IterantState ip r1 r2))) =
     Build_IterantState ip r1 r2).
  rewrite (decode_ip_encode_state (Build_IterantState ip r1 r2) Hwf).
  rewrite (decode_r1_encode_state (Build_IterantState ip r1 r2) Hwf).
  rewrite (decode_r2_encode_state (Build_IterantState ip r1 r2) Hwf).
  reflexivity.
Qed.

Lemma decode_ip_lt_limit :
  forall s, decode_ip s < ip_limit.
Proof.
  intro s.
  unfold decode_ip, decode_ip_from_support, ip_limit.
  apply sum_fib_lt_fib_of_valid_all_lt.
  - apply band_indices_valid.
    apply Z0_valid.
  - apply band_indices_all_lt.
  - unfold K_IP.
    lia.
Qed.

Lemma decode_r1_lt_limit :
  forall s, decode_r1 s < r1_limit.
Proof.
  intro s.
  unfold decode_r1, decode_r1_from_support, r1_limit.
  apply sum_fib_lt_fib_of_valid_all_lt.
  - apply band_indices_valid.
    apply Z0_valid.
  - apply band_indices_all_lt.
  - unfold K_R1.
    lia.
Qed.

Lemma decode_r2_lt_limit :
  forall s, decode_r2 s < r2_limit.
Proof.
  intro s.
  unfold decode_r2, decode_r2_from_support, r2_limit.
  apply sum_fib_lt_fib_of_valid_all_lt.
  - apply band_indices_valid.
    apply Z0_valid.
  - apply band_indices_all_lt.
  - unfold K_R2.
    lia.
Qed.

(*
│
│          `decode_state_well_formed` makes the projection semantics
│          explicit: every raw natural code decodes to a bounded
│          machine state, even when the code was not originally
│          produced by `encode_state`.
│
*)

(*
│
│          The three preceding limit lemmas are the reason this total
│          decoder lands back in the state space. Each projected local
│          support is valid and remains strictly below its Fibonacci
│          cutoff, so decoding cannot produce an out-of-range register
│          value.
│
*)

(* decode_ip(s) < ip_limit, decode_r1(s) < r1_limit, decode_r2(s) < r2_limit. *)

Theorem decode_state_well_formed :
  forall s, state_well_formed (decode_state s).
Proof.
  intro s.
  unfold decode_state, decode_state_from_support.
  apply state_well_formed_build.
  - apply decode_ip_lt_limit.
  - apply decode_r1_lt_limit.
  - apply decode_r2_lt_limit.
Qed.

Lemma valid_state_code_encode :
  forall st,
    state_well_formed st ->
    valid_state_code (encode_state st).
Proof.
  intros st Hwf.
  exists st.
  split.
  - exact Hwf.
  - reflexivity.
Qed.

Lemma encode_state_decode_state_if_valid :
  forall s,
    valid_state_code s ->
    normalize_state_code s = s.
Proof.
  intros s [st [Hwf Hcode]].
  unfold normalize_state_code.
  subst s.
  rewrite (decode_state_encode_state st Hwf).
  reflexivity.
Qed.

(*
│
│          `valid_state_code_iff_fixed` characterizes the exact image
│          of the codec: a natural number is an actual encoded machine
│          state precisely when decode-then-encode leaves it
│          unchanged.
│
*)

(*             valid_state_code(s) ⇔ normalize_state_code(s) = s.             *)

Theorem valid_state_code_iff_fixed :
  forall s,
    valid_state_code s <->
    normalize_state_code s = s.
Proof.
  intro s.
  split.
  - apply encode_state_decode_state_if_valid.
  - intro Hfixed.
    exists (decode_state s).
    split.
    + apply decode_state_well_formed.
    + symmetry.
      exact Hfixed.
Qed.

(*
│
│          Injectivity is now conceptually simple. Two bounded states
│          with the same code decode to the same normalized state, and
│          the roundtrip theorem then identifies the original states
│          componentwise.
│
*)

(*   state_well_formed(st₁) ∧ state_well_formed(st₂) ∧ encode_state(st₁) =    *)
(*                       encode_state(st₂) ⇒ st₁ = st₂.                       *)

Theorem encode_state_injective :
  forall st1 st2,
    state_well_formed st1 ->
    state_well_formed st2 ->
    encode_state st1 = encode_state st2 ->
    st1 = st2.
Proof.
  intros st1 st2 Hw1 Hw2 Hcode.
  apply (f_equal decode_state) in Hcode.
  rewrite (decode_state_encode_state st1 Hw1) in Hcode.
  rewrite (decode_state_encode_state st2 Hw2) in Hcode.
  exact Hcode.
Qed.

Corollary state_ip_roundtrip :
  forall st,
    state_well_formed st ->
    state_ip (decode_state (encode_state st)) = state_ip st.
Proof.
  intros st Hwf.
  rewrite decode_state_encode_state by exact Hwf.
  reflexivity.
Qed.

Corollary state_r1_roundtrip :
  forall st,
    state_well_formed st ->
    state_r1 (decode_state (encode_state st)) = state_r1 st.
Proof.
  intros st Hwf.
  rewrite decode_state_encode_state by exact Hwf.
  reflexivity.
Qed.

Corollary state_r2_roundtrip :
  forall st,
    state_well_formed st ->
    state_r2 (decode_state (encode_state st)) = state_r2 st.
Proof.
  intros st Hwf.
  rewrite decode_state_encode_state by exact Hwf.
  reflexivity.
Qed.

Theorem r1_increment_preserves_ip :
  forall st,
    state_well_formed st ->
    S (state_r1 st) < r1_limit ->
    state_ip
      (decode_state
        (encode_state
          (Build_IterantState (state_ip st) (S (state_r1 st)) (state_r2 st)))) =
    state_ip st.
Proof.
  intros [ip r1 r2] [Hip [Hr1 Hr2]] Hr1S.
  pose proof (state_well_formed_build ip (S r1) r2 Hip Hr1S Hr2) as Hwf'.
  simpl.
  change (decode_ip (encode_state (Build_IterantState ip (S r1) r2)) = ip).
  rewrite (decode_ip_encode_state (Build_IterantState ip (S r1) r2) Hwf').
  reflexivity.
Qed.

(*
│
│          The `_of` state codec is the parameterized counterpart of
│          the concrete one. It reuses the same `IterantState` record,
│          but interprets well-formedness, supports, and decoding
│          relative to an arbitrary `MachineLimits` package.
│
*)

(*     state_well_formed_of(L, (ip, r1, r2)) ≔ ip < ip_limit_of(L) ∧ r1 <     *)
(*                   r1_limit_of(L) ∧ r2 < r2_limit_of(L).                    *)
(*         encode_state_of(L, st) = sum_fib(state_support_of(L, st))          *)
(*= sum_fib(r2_support_of(L, state_r2(st)) ⧺ r1_support_of(L, state_r1(st)) ⧺ *)
(*                      ip_support_of(L, state_ip(st))).                      *)
(* normalize_state_code_of(L, s) = encode_state_of(L, decode_state_of(L, s))  *)
(*    valid_state_code_of(L, s) ≔ ∃ st, state_well_formed_of(L, st) ∧ s =     *)
(*                          encode_state_of(L, st).                           *)

Definition state_well_formed_of (L : MachineLimits) (st : IterantState) : Prop :=
  state_ip st < ip_limit_of L /\
  state_r1 st < r1_limit_of L /\
  state_r2 st < r2_limit_of L.

Definition state_support_of (L : MachineLimits) (st : IterantState) : list nat :=
  r2_support_of L (state_r2 st) ++
  r1_support_of L (state_r1 st) ++
  ip_support_of L (state_ip st).

Definition encode_state_of (L : MachineLimits) (st : IterantState) : nat :=
  sum_fib (state_support_of L st).

Definition decode_ip_from_support_of (L : MachineLimits) (zn : list nat) : nat :=
  sum_fib (band_indices (ml_IP_offset L) (ml_K_IP L) zn).

Definition decode_r1_from_support_of (L : MachineLimits) (zn : list nat) : nat :=
  sum_fib (band_indices (ml_R1_offset L) (ml_K_R1 L) zn).

Definition decode_r2_from_support_of (L : MachineLimits) (zn : list nat) : nat :=
  sum_fib (band_indices (ml_R2_offset L) (ml_K_R2 L) zn).

Definition decode_ip_of (L : MachineLimits) (s : nat) : nat :=
  decode_ip_from_support_of L (Z0 s).

Definition decode_r1_of (L : MachineLimits) (s : nat) : nat :=
  decode_r1_from_support_of L (Z0 s).

Definition decode_r2_of (L : MachineLimits) (s : nat) : nat :=
  decode_r2_from_support_of L (Z0 s).

Definition decode_state_from_support_of (L : MachineLimits) (zn : list nat) : IterantState :=
  Build_IterantState
    (decode_ip_from_support_of L zn)
    (decode_r1_from_support_of L zn)
    (decode_r2_from_support_of L zn).

Definition decode_state_of (L : MachineLimits) (s : nat) : IterantState :=
  decode_state_from_support_of L (Z0 s).

Definition normalize_state_code_of (L : MachineLimits) (s : nat) : nat :=
  encode_state_of L (decode_state_of L s).

Definition valid_state_code_of (L : MachineLimits) (s : nat) : Prop :=
  exists st,
    state_well_formed_of L st /\
    s = encode_state_of L st.

(*
│
│          From this point onward we replay the concrete codec
│          argument uniformly over an arbitrary package `L :
│          MachineLimits`. The proof shape is intentionally parallel
│          to the fixed case: first we establish support validity,
│          then exact splitting, then component roundtrips, then
│          boundedness of total decoding, and finally fixed-point
│          characterization and injectivity.
│
*)

Lemma state_well_formed_build_of :
  forall L ip r1 r2,
    ip < ip_limit_of L ->
    r1 < r1_limit_of L ->
    r2 < r2_limit_of L ->
    state_well_formed_of L (Build_IterantState ip r1 r2).
Proof.
  intros L ip r1 r2 Hip Hr1 Hr2.
  split.
  - exact Hip.
  - split.
    + exact Hr1.
    + exact Hr2.
Qed.

Lemma r1_ip_support_valid_of :
  forall L ip r1,
    ip < ip_limit_of L ->
    r1 < r1_limit_of L ->
    zeck_valid (r1_support_of L r1 ++ ip_support_of L ip).
Proof.
  intros L ip r1 Hip Hr1.
  pose proof (band_support_valid (ml_R1_offset L) r1) as Hr1v.
  pose proof (band_support_valid (ml_IP_offset L) ip) as Hipv.
  destruct Hr1v as [Hdec1 [Hadj1 Hge1]].
  destruct Hipv as [Hdec0 [Hadj0 Hge0]].
  split.
  - apply strictly_decreasing_app.
    + exact Hdec1.
    + exact Hdec0.
    + intros x y Hx Hy.
      apply r1_support_gt_ip_support_of with (L:=L) (r1:=r1) (ip:=ip); assumption.
  - split.
    + apply no_adjacent_app.
      * exact Hadj1.
      * exact Hadj0.
      * intros x y Hx Hy.
        apply r1_support_gap_ip_support_of with (L:=L) (r1:=r1) (ip:=ip); assumption.
    + apply all_ge_2_app; assumption.
Qed.

Lemma r2_support_gt_r1_ip_support_of :
  forall L ip r1 r2 x y,
    ip < ip_limit_of L ->
    r1 < r1_limit_of L ->
    r2 < r2_limit_of L ->
    In x (r2_support_of L r2) ->
    In y (r1_support_of L r1 ++ ip_support_of L ip) ->
    x > y.
Proof.
  intros L ip r1 r2 x y Hip Hr1 Hr2 Hx Hy.
  apply in_app_or in Hy.
  destruct Hy as [Hy|Hy].
  - exact (r2_support_gt_r1_support_of L r2 r1 x y Hr2 Hr1 Hx Hy).
  - exact (r2_support_gt_ip_support_of L r2 ip x y Hr2 Hip Hx Hy).
Qed.

Lemma r2_support_gap_r1_ip_support_of :
  forall L ip r1 r2 x y,
    ip < ip_limit_of L ->
    r1 < r1_limit_of L ->
    r2 < r2_limit_of L ->
    In x (r2_support_of L r2) ->
    In y (r1_support_of L r1 ++ ip_support_of L ip) ->
    x >= y + 2.
Proof.
  intros L ip r1 r2 x y Hip Hr1 Hr2 Hx Hy.
  apply in_app_or in Hy.
  destruct Hy as [Hy|Hy].
  - exact (r2_support_gap_r1_support_of L r2 r1 x y Hr2 Hr1 Hx Hy).
  - exact (r2_support_gap_ip_support_of L r2 ip x y Hr2 Hip Hx Hy).
Qed.

Theorem state_support_valid_of :
  forall L st,
    state_well_formed_of L st ->
    zeck_valid (state_support_of L st).
Proof.
  intros L [ip r1 r2] [Hip [Hr1 Hr2]].
  unfold state_support_of.
  pose proof (band_support_valid (ml_R2_offset L) r2) as Hr2v.
  pose proof (r1_ip_support_valid_of L ip r1 Hip Hr1) as H10v.
  destruct Hr2v as [Hdec2 [Hadj2 Hge2]].
  destruct H10v as [Hdec10 [Hadj10 Hge10]].
  split.
  - apply strictly_decreasing_app.
    + exact Hdec2.
    + exact Hdec10.
    + intros x y Hx Hy.
      exact (r2_support_gt_r1_ip_support_of L ip r1 r2 x y Hip Hr1 Hr2 Hx Hy).
  - split.
    + apply no_adjacent_app.
      * exact Hadj2.
      * exact Hadj10.
      * intros x y Hx Hy.
        exact (r2_support_gap_r1_ip_support_of L ip r1 r2 x y Hip Hr1 Hr2 Hx Hy).
    + apply all_ge_2_app; assumption.
Qed.

(*
│
│          Just as in the fixed layout, the parametric support proof
│          is governed entirely by the three separation inequalities
│          carried by `L`. Once those inequalities are available, the
│          concatenated support is again a valid global Zeckendorf
│          support.
│
*)

(*     state_well_formed_of(L, st) ⇒ zeck_valid(state_support_of(L, st)).     *)

(*
│
│          `encode_state_support_of` and
│          `encode_state_as_components_of` lift the concrete codec
│          bridge to an arbitrary limit package. These are the key
│          algebraic facts required once the later universality layer
│          begins to quantify over sufficiently large band layouts.
│
*)

(*         state_well_formed_of(L, st) ⇒ Z0(encode_state_of(L, st)) =         *)
(*                          state_support_of(L, st)                           *)
(*    encode_state_of(L, st) = r2_code_of(L, state_r2(st)) + r1_code_of(L,    *)
(*                state_r1(st)) + ip_code_of(L, state_ip(st)).                *)

Theorem encode_state_support_of :
  forall L st,
    state_well_formed_of L st ->
    Z0 (encode_state_of L st) = state_support_of L st.
Proof.
  intros L st Hwf.
  unfold encode_state_of.
  apply Z0_of_sum_fib.
  apply state_support_valid_of.
  exact Hwf.
Qed.

Theorem encode_state_as_components_of :
  forall L st,
    encode_state_of L st =
    r2_code_of L (state_r2 st) +
    r1_code_of L (state_r1 st) +
    ip_code_of L (state_ip st).
Proof.
  intros L [ip r1 r2].
  unfold encode_state_of, state_support_of, r2_code_of, r1_code_of, ip_code_of, band_code.
  repeat rewrite sum_fib_app.
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

(*
│
│          The parametric split lemmas say exactly the same thing as
│          their fixed counterparts: each band predicate deletes the
│          two foreign bands and preserves its own band verbatim.
│          These are the operational decoding lemmas for arbitrary
│          machine layouts.
│
*)

(*    filter(ip_pred_of(L), Z0(encode_state_of(L, st))) = ip_support_of(L,    *)
(*                               state_ip(st))                                *)
(*    filter(r1_pred_of(L), Z0(encode_state_of(L, st))) = r1_support_of(L,    *)
(*                               state_r1(st))                                *)
(*    filter(r2_pred_of(L), Z0(encode_state_of(L, st))) = r2_support_of(L,    *)
(*                               state_r2(st)).                               *)

Lemma filter_state_support_of :
  forall L (p : nat -> bool) ip r1 r2,
    filter p (state_support_of L (Build_IterantState ip r1 r2)) =
    ((filter p (r2_support_of L r2) ++ filter p (r1_support_of L r1)) ++
     filter p (ip_support_of L ip)).
Proof.
  intros L p ip r1 r2.
  unfold state_support_of.
  repeat rewrite filter_app.
  rewrite app_assoc.
  reflexivity.
Qed.

Corollary ip_support_split_of :
  forall L st,
    state_well_formed_of L st ->
    filter (ip_pred_of L) (Z0 (encode_state_of L st)) = ip_support_of L (state_ip st).
Proof.
  intros L [ip r1 r2] [Hip [Hr1 Hr2]].
  rewrite encode_state_support_of by (repeat split; assumption).
  rewrite (filter_state_support_of L (ip_pred_of L) ip r1 r2).
  assert (Hr2_nil : filter (ip_pred_of L) (r2_support_of L r2) = []).
  - apply filter_false_nil.
    intros a Ha.
    exact (ip_pred_false_on_r2_support_of L r2 a Hr2 Ha).
  - assert (Hr1_nil : filter (ip_pred_of L) (r1_support_of L r1) = []).
    + apply filter_false_nil.
      intros a Ha.
      exact (ip_pred_false_on_r1_support_of L r1 a Hr1 Ha).
    + assert (Hip_id : filter (ip_pred_of L) (ip_support_of L ip) = ip_support_of L ip).
      * apply filter_true_id.
        intros a Ha.
        exact (ip_pred_true_on_ip_support_of L ip a Hip Ha).
      * rewrite Hr2_nil, Hr1_nil, Hip_id.
        simpl.
        reflexivity.
Qed.

Corollary r1_support_split_of :
  forall L st,
    state_well_formed_of L st ->
    filter (r1_pred_of L) (Z0 (encode_state_of L st)) = r1_support_of L (state_r1 st).
Proof.
  intros L [ip r1 r2] [Hip [Hr1 Hr2]].
  rewrite encode_state_support_of by (repeat split; assumption).
  rewrite (filter_state_support_of L (r1_pred_of L) ip r1 r2).
  assert (Hr2_nil : filter (r1_pred_of L) (r2_support_of L r2) = []).
  - apply filter_false_nil.
    intros a Ha.
    exact (r1_pred_false_on_r2_support_of L r2 a Hr2 Ha).
  - assert (Hr1_id : filter (r1_pred_of L) (r1_support_of L r1) = r1_support_of L r1).
    + apply filter_true_id.
      intros a Ha.
      exact (r1_pred_true_on_r1_support_of L r1 a Hr1 Ha).
    + assert (Hip_nil : filter (r1_pred_of L) (ip_support_of L ip) = []).
      * apply filter_false_nil.
        intros a Ha.
        exact (r1_pred_false_on_ip_support_of L ip a Hip Ha).
      * rewrite Hr2_nil, Hr1_id, Hip_nil.
        simpl.
        rewrite app_nil_r.
        reflexivity.
Qed.

Corollary r2_support_split_of :
  forall L st,
    state_well_formed_of L st ->
    filter (r2_pred_of L) (Z0 (encode_state_of L st)) = r2_support_of L (state_r2 st).
Proof.
  intros L [ip r1 r2] [Hip [Hr1 Hr2]].
  rewrite encode_state_support_of by (repeat split; assumption).
  rewrite (filter_state_support_of L (r2_pred_of L) ip r1 r2).
  assert (Hr2_id : filter (r2_pred_of L) (r2_support_of L r2) = r2_support_of L r2).
  - apply filter_true_id.
    intros a Ha.
    exact (r2_pred_true_on_r2_support_of L r2 a Hr2 Ha).
  - assert (Hr1_nil : filter (r2_pred_of L) (r1_support_of L r1) = []).
    + apply filter_false_nil.
      intros a Ha.
      exact (r2_pred_false_on_r1_support_of L r1 a Hr1 Ha).
    + assert (Hip_nil : filter (r2_pred_of L) (ip_support_of L ip) = []).
      * apply filter_false_nil.
        intros a Ha.
        exact (r2_pred_false_on_ip_support_of L ip a Hip Ha).
      * rewrite Hr2_id, Hr1_nil, Hip_nil.
        simpl.
        repeat rewrite app_nil_r.
        reflexivity.
Qed.

(*
│
│          Accordingly, each parametric component decoder roundtrips
│          on encoded well-formed states by exactly the same two-step
│          argument: isolate the intended support and cancel the
│          offset translation.
│
*)

(*  state_well_formed_of(L, st) ⇒ decode_ip_of(L, encode_state_of(L, st)) =   *)
(*                                state_ip(st)                                *)
(*  state_well_formed_of(L, st) ⇒ decode_r1_of(L, encode_state_of(L, st)) =   *)
(*                                state_r1(st)                                *)
(*  state_well_formed_of(L, st) ⇒ decode_r2_of(L, encode_state_of(L, st)) =   *)
(*                               state_r2(st).                                *)

Lemma decode_ip_encode_state_of :
  forall L st,
    state_well_formed_of L st ->
    decode_ip_of L (encode_state_of L st) = state_ip st.
Proof.
  intros L st Hwf.
  unfold decode_ip_of, decode_ip_from_support_of, band_indices.
  change
    (sum_fib
       (map (fun k : nat => k - ml_IP_offset L)
          (filter (ip_pred_of L) (Z0 (encode_state_of L st)))) =
     state_ip st).
  rewrite ip_support_split_of by exact Hwf.
  unfold ip_support_of.
  rewrite map_sub_band_support.
  apply Z0_sound.
Qed.

Lemma decode_r1_encode_state_of :
  forall L st,
    state_well_formed_of L st ->
    decode_r1_of L (encode_state_of L st) = state_r1 st.
Proof.
  intros L st Hwf.
  unfold decode_r1_of, decode_r1_from_support_of, band_indices.
  change
    (sum_fib
       (map (fun k : nat => k - ml_R1_offset L)
          (filter (r1_pred_of L) (Z0 (encode_state_of L st)))) =
     state_r1 st).
  rewrite r1_support_split_of by exact Hwf.
  unfold r1_support_of.
  rewrite map_sub_band_support.
  apply Z0_sound.
Qed.

Lemma decode_r2_encode_state_of :
  forall L st,
    state_well_formed_of L st ->
    decode_r2_of L (encode_state_of L st) = state_r2 st.
Proof.
  intros L st Hwf.
  unfold decode_r2_of, decode_r2_from_support_of, band_indices.
  change
    (sum_fib
       (map (fun k : nat => k - ml_R2_offset L)
          (filter (r2_pred_of L) (Z0 (encode_state_of L st)))) =
     state_r2 st).
  rewrite r2_support_split_of by exact Hwf.
  unfold r2_support_of.
  rewrite map_sub_band_support.
  apply Z0_sound.
Qed.

Theorem decode_state_encode_state_of :
  forall L st,
    state_well_formed_of L st ->
    decode_state_of L (encode_state_of L st) = st.
Proof.
  intros L [ip r1 r2] Hwf.
  change
    (Build_IterantState
       (decode_ip_of L (encode_state_of L (Build_IterantState ip r1 r2)))
       (decode_r1_of L (encode_state_of L (Build_IterantState ip r1 r2)))
       (decode_r2_of L (encode_state_of L (Build_IterantState ip r1 r2))) =
     Build_IterantState ip r1 r2).
  rewrite (decode_ip_encode_state_of L (Build_IterantState ip r1 r2) Hwf).
  rewrite (decode_r1_encode_state_of L (Build_IterantState ip r1 r2) Hwf).
  rewrite (decode_r2_encode_state_of L (Build_IterantState ip r1 r2) Hwf).
  reflexivity.
Qed.

Lemma decode_ip_lt_limit_of :
  forall L s,
    2 <= ml_K_IP L ->
    decode_ip_of L s < ip_limit_of L.
Proof.
  intros L s HK.
  unfold decode_ip_of, decode_ip_from_support_of, ip_limit_of.
  apply sum_fib_lt_fib_of_valid_all_lt.
  - apply band_indices_valid.
    apply Z0_valid.
  - apply band_indices_all_lt.
  - exact HK.
Qed.

Lemma decode_r1_lt_limit_of :
  forall L s,
    2 <= ml_K_R1 L ->
    decode_r1_of L s < r1_limit_of L.
Proof.
  intros L s HK.
  unfold decode_r1_of, decode_r1_from_support_of, r1_limit_of.
  apply sum_fib_lt_fib_of_valid_all_lt.
  - apply band_indices_valid.
    apply Z0_valid.
  - apply band_indices_all_lt.
  - exact HK.
Qed.

Lemma decode_r2_lt_limit_of :
  forall L s,
    2 <= ml_K_R2 L ->
    decode_r2_of L s < r2_limit_of L.
Proof.
  intros L s HK.
  unfold decode_r2_of, decode_r2_from_support_of, r2_limit_of.
  apply sum_fib_lt_fib_of_valid_all_lt.
  - apply band_indices_valid.
    apply Z0_valid.
  - apply band_indices_all_lt.
  - exact HK.
Qed.

Theorem decode_state_well_formed_of :
  forall L s,
    2 <= ml_K_IP L ->
    2 <= ml_K_R1 L ->
    2 <= ml_K_R2 L ->
    state_well_formed_of L (decode_state_of L s).
Proof.
  intros L s HKip HKr1 HKr2.
  unfold decode_state_of, decode_state_from_support_of.
  apply state_well_formed_build_of.
  - apply decode_ip_lt_limit_of.
    exact HKip.
  - apply decode_r1_lt_limit_of.
    exact HKr1.
  - apply decode_r2_lt_limit_of.
    exact HKr2.
Qed.

(*
│
│          The parameterized decoder needs explicit hypotheses `2 <=
│          ml_K_* L` because the abstract family does not hard-wire
│          the concrete widths. Under those mild lower bounds, every
│          decoded component lies strictly below its corresponding
│          Fibonacci limit, so the total decoder again lands in the
│          bounded state space.
│
*)

(*            2 ≤ ml_K_IP(L) ⇒ decode_ip_of(L, s) < ip_limit_of(L)            *)
(*            2 ≤ ml_K_R1(L) ⇒ decode_r1_of(L, s) < r1_limit_of(L)            *)
(*           2 ≤ ml_K_R2(L) ⇒ decode_r2_of(L, s) < r2_limit_of(L).            *)

Lemma valid_state_code_encode_of :
  forall L st,
    state_well_formed_of L st ->
    valid_state_code_of L (encode_state_of L st).
Proof.
  intros L st Hwf.
  exists st.
  split.
  - exact Hwf.
  - reflexivity.
Qed.

Lemma encode_state_decode_state_if_valid_of :
  forall L s,
    valid_state_code_of L s ->
    normalize_state_code_of L s = s.
Proof.
  intros L s [st [Hwf Hcode]].
  unfold normalize_state_code_of.
  subst s.
  rewrite (decode_state_encode_state_of L st Hwf).
  reflexivity.
Qed.

Theorem valid_state_code_iff_fixed_of :
  forall L s,
    2 <= ml_K_IP L ->
    2 <= ml_K_R1 L ->
    2 <= ml_K_R2 L ->
    valid_state_code_of L s <->
    normalize_state_code_of L s = s.
Proof.
  intros L s HKip HKr1 HKr2.
  split.
  - apply encode_state_decode_state_if_valid_of.
  - intro Hfixed.
    exists (decode_state_of L s).
    split.
    + apply decode_state_well_formed_of; assumption.
    + symmetry.
      exact Hfixed.
Qed.

(*
│
│          Finally, the fixed-point and injectivity story is unchanged
│          in the abstract family. Valid codes are exactly the
│          decoder-encoder fixed points, and equality of encoded
│          well-formed states is reflected back to equality of states
│          by parametric roundtrip.
│
*)

(*       valid_state_code_of(L, s) ⇔ normalize_state_code_of(L, s) = s        *)
(* encode_state_of(L, st₁) = encode_state_of(L, st₂) ⇒ st₁ = st₂ for bounded  *)
(*                                 st₁, st₂.                                  *)

Theorem encode_state_injective_of :
  forall L st1 st2,
    state_well_formed_of L st1 ->
    state_well_formed_of L st2 ->
    encode_state_of L st1 = encode_state_of L st2 ->
    st1 = st2.
Proof.
  intros L st1 st2 Hw1 Hw2 Hcode.
  apply (f_equal (decode_state_of L)) in Hcode.
  rewrite (decode_state_encode_state_of L st1 Hw1) in Hcode.
  rewrite (decode_state_encode_state_of L st2 Hw2) in Hcode.
  exact Hcode.
Qed.

Corollary state_ip_roundtrip_of :
  forall L st,
    state_well_formed_of L st ->
    state_ip (decode_state_of L (encode_state_of L st)) = state_ip st.
Proof.
  intros L st Hwf.
  rewrite decode_state_encode_state_of by exact Hwf.
  reflexivity.
Qed.

Corollary state_r1_roundtrip_of :
  forall L st,
    state_well_formed_of L st ->
    state_r1 (decode_state_of L (encode_state_of L st)) = state_r1 st.
Proof.
  intros L st Hwf.
  rewrite decode_state_encode_state_of by exact Hwf.
  reflexivity.
Qed.

Corollary state_r2_roundtrip_of :
  forall L st,
    state_well_formed_of L st ->
    state_r2 (decode_state_of L (encode_state_of L st)) = state_r2 st.
Proof.
  intros L st Hwf.
  rewrite decode_state_encode_state_of by exact Hwf.
  reflexivity.
Qed.
