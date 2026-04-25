(*D001_02__Carryless_Bands.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                     Proofcase / D001_02__Carryless_Bands                     │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  In this file we fix the concrete carryless band layout of the Iterant
  Machine.

  Starting from the Zeckendorf substrate imported from `A001`, we place
  canonical supports into three disjoint windows for `IP`, `R1`, and `R2`,
  and we prove the separation facts that the later state-codec and machine
  layers reuse verbatim.

*)

From D001 Require Export D001_01__Arithmetic_Base.

Definition K_IP : nat := 13.
Definition K_R1 : nat := 53.
Definition K_R2 : nat := 65.

Definition IP_offset : nat := 0.
Definition R1_offset : nat := 12.
Definition R2_offset : nat := 64.

Definition guard_ip_r1 : nat := 13.
Definition guard_r1_r2 : nat := 65.

(*
│
│          `MachineLimits` packages the width, offset, separation, and
│          boundedness data required to instantiate the carryless band
│          calculus. It is the parameter block used later for
│          asymptotic and classical universality statements.
│
*)

(*         MachineLimits = (K_IP, K_R1, K_R2, off_IP, off_R1, off_R2)         *)
(*  off_IP + K_IP ≤ off_R1 + 1, off_R1 + K_R1 ≤ off_R2 + 1, off_IP + K_IP ≤   *)
(*                                 off_R2 + 1                                 *)
(*                       1 < fib(K_IP), 0 < fib(K_R2).                        *)

Record MachineLimits : Type := Build_MachineLimits
{
  ml_K_IP : nat;
  ml_K_R1 : nat;
  ml_K_R2 : nat;
  ml_IP_offset : nat;
  ml_R1_offset : nat;
  ml_R2_offset : nat;
  ml_sep_ip_r1 : ml_IP_offset + ml_K_IP <= ml_R1_offset + 1;
  ml_sep_r1_r2 : ml_R1_offset + ml_K_R1 <= ml_R2_offset + 1;
  ml_sep_ip_r2 : ml_IP_offset + ml_K_IP <= ml_R2_offset + 1;
  ml_initial_ip_bounded : 1 < fib ml_K_IP;
  ml_r2_limit_nonzero : 0 < fib ml_K_R2
}.

Definition fixed_limits : MachineLimits.
Proof.
  (* Keep this transparent: downstream fixed-instance lemmas project fields
     from `fixed_limits` directly. Sealing it would force extra transport
     lemmas just to recover the concrete fixed parameters. *)
  refine
    (Build_MachineLimits
       K_IP K_R1 K_R2
       IP_offset R1_offset R2_offset
       _ _ _ _ _).
  - unfold K_IP, IP_offset, R1_offset.
    lia.
  - unfold K_R1, R1_offset, R2_offset.
    lia.
  - unfold K_IP, IP_offset, R2_offset.
    lia.
  - unfold K_IP.
    vm_compute.
    lia.
  - unfold K_R2.
    assert (Hpos : fib 65 >= 1) by (apply fib_pos; lia).
    lia.
Defined.

(*
│
│          With `fixed_limits` we commit to one concrete three-band
│          geometry. We keep the generic `MachineLimits` record
│          because later files quantify over arbitrary packages, but
│          here we still want one named package from which the fixed
│          machine constants are specialized.
│
*)

(*                IP = [2, 13), R1 = [14, 65), R2 = [66, 129).                *)

(*
│
│          The three limits are the payload capacities of the fixed
│          `IP`, `R1`, and `R2` windows. Each is expressed as a
│          Fibonacci cutoff so that all later band arguments remain
│          inside the Zeckendorf arithmetic imported from `A001`.
│
*)

(*     ip_limit = fib(K_IP), r1_limit = fib(K_R1), r2_limit = fib(K_R2).      *)

Definition ip_limit : nat := fib K_IP.
Definition r1_limit : nat := fib K_R1.
Definition r2_limit : nat := fib K_R2.

(* Keep the large Fibonacci engine abstract inside this file only.
   Otherwise tactics such as lia may reify closed terms like fib 53/fib 65
   into enormous Peano numerals during preprocessing. *)
Local Opaque fib r0 Z0.

(*
│
│          `band_support` translates a canonical support by a fixed
│          offset, thereby placing the payload into one of the
│          reserved Fibonacci windows of the machine layout.
│
*)

Definition band_support (offset : nat) (x : nat) : list nat :=
  map (fun i => offset + i) (Z0 x).

Definition band_code (offset : nat) (x : nat) : nat :=
  sum_fib (band_support offset x).

(*       band_pred(offset, K, k) = true ⇔ offset + 2 ≤ k < offset + K.        *)

Definition band_pred (offset K k : nat) : bool :=
  Nat.leb (offset + 2) k && Nat.ltb k (offset + K).

(*
│
│          `band_indices` is the inverse window projection: it selects
│          the indices lying in the chosen band and subtracts the
│          offset in order to recover their local coordinates.
│
*)

Definition band_indices (offset K : nat) (zn : list nat) : list nat :=
  map (fun k => k - offset) (filter (band_pred offset K) zn).

(*
│
│          We now freeze the concrete specializations of the generic
│          translation primitives. The names `ip_support`,
│          `r1_support`, `r2_support` and their code/predicate
│          companions are the fixed-layout interface that the later
│          state codec reads.
│
*)

(*        ip_support(x) = band_support(IP_offset, x), r1_support(x) =         *)
(*  band_support(R1_offset, x), r2_support(x) = band_support(R2_offset, x).   *)

Definition ip_support : nat -> list nat := band_support IP_offset.
Definition r1_support : nat -> list nat := band_support R1_offset.
Definition r2_support : nat -> list nat := band_support R2_offset.

Definition ip_code : nat -> nat := band_code IP_offset.
Definition r1_code : nat -> nat := band_code R1_offset.
Definition r2_code : nat -> nat := band_code R2_offset.

Definition ip_pred (k : nat) : bool := band_pred IP_offset K_IP k.
Definition r1_pred (k : nat) : bool := band_pred R1_offset K_R1 k.
Definition r2_pred (k : nat) : bool := band_pred R2_offset K_R2 k.

(*
│
│          Before we reason about concrete windows, we isolate the
│          generic arithmetic facts that translation by a constant
│          offset preserves. The lemma `r0_le_of_lt_fib` turns an
│          external Fibonacci bound `x < fib(K)` into a bound on the
│          support-width parameter `r0(x)`, while the three map lemmas
│          show that offset translation preserves the Zeckendorf
│          admissibility data componentwise.
│
*)

(*                           x < fib(K) ⇒ r0(x) ≤ K                           *)
(*   strictly_decreasing(xs) ⇒ strictly_decreasing(map(i ↦ offset + i, xs))   *)
(*          no_adjacent(xs) ⇒ no_adjacent(map(i ↦ offset + i, xs)).           *)

Lemma r0_le_of_lt_fib :
  forall x K,
    x < fib K ->
    r0 x <= K.
Proof.
  intros x K Hlt.
  destruct (Nat.le_gt_cases (r0 x) K) as [Hle|Hgt].
  - exact Hle.
  - exfalso.
    assert (Hfib : fib K <= x).
    + apply r0_minimal.
      lia.
    + lia.
Qed.

Lemma strictly_decreasing_map_plus :
  forall offset xs,
    strictly_decreasing xs ->
    strictly_decreasing (map (fun i => offset + i) xs).
Proof.
  intros offset xs Hdec.
  revert offset Hdec.
  induction xs as [|a xs IH]; intros offset Hdec; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hdec as [Hab Htail].
  split.
  - lia.
  - apply IH.
    exact Htail.
Qed.

Lemma no_adjacent_map_plus :
  forall offset xs,
    no_adjacent xs ->
    no_adjacent (map (fun i => offset + i) xs).
Proof.
  intros offset xs Hadj.
  revert offset Hadj.
  induction xs as [|a xs IH]; intros offset Hadj; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hadj as [Hab Htail].
  split.
  - lia.
  - apply IH.
    exact Htail.
Qed.

Lemma all_ge_2_map_plus :
  forall offset xs,
    all_ge_2 xs ->
    all_ge_2 (map (fun i => offset + i) xs).
Proof.
  intros offset xs Hge.
  revert offset Hge.
  induction xs as [|a xs IH]; intros offset Hge; simpl; auto.
  destruct Hge as [Ha Htail].
  split.
  - lia.
  - apply IH.
    exact Htail.
Qed.

(*
│
│          `band_support_valid` shows that Zeckendorf admissibility is
│          preserved under translation by a fixed offset. In
│          particular, strict decrease and non-adjacency survive
│          unchanged, and all translated indices remain above the
│          forbidden positions `0` and `1`.
│
*)

(*          zeck_valid(Z0(x)) ⇒ zeck_valid(band_support(offset, x)).          *)

Lemma band_support_valid :
  forall offset x,
    zeck_valid (band_support offset x).
Proof.
  intros offset x.
  unfold band_support.
  pose proof (Z0_valid x) as [Hdec [Hadj Hge]].
  split.
  - apply strictly_decreasing_map_plus.
    exact Hdec.
  - split.
    + apply no_adjacent_map_plus.
      exact Hadj.
    + apply all_ge_2_map_plus.
      exact Hge.
Qed.

(*
│
│          `band_support_window` is the basic window-containment
│          lemma: whenever the payload satisfies `x < fib(K)`, every
│          occupied index of the translated support lies strictly
│          inside the band `[offset + 2, offset + K)`.
│
*)

(*  x < fib(K) ∧ i ∈ band_support(offset, x) ⇒ offset + 2 ≤ i < offset + K.   *)

Lemma band_support_window :
  forall offset K x i,
    x < fib K ->
    In i (band_support offset x) ->
    offset + 2 <= i /\ i < offset + K.
Proof.
  intros offset K x i Hx Hin.
  unfold band_support in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [Hi Hj]].
  subst i.
  assert (Hj2 : 2 <= j).
  - apply all_ge_2_in with (xs:=Z0 x); [|exact Hj].
    destruct (Z0_valid x) as [_ [_ Hge]].
    exact Hge.
  - assert (Hjr0 : j < r0 x).
    + apply Z0_indices_below_r0.
      exact Hj.
    + assert (Hr0 : r0 x <= K).
      * apply r0_le_of_lt_fib.
        exact Hx.
      * split; lia.
Qed.

Lemma band_support_lower_bound :
  forall offset K x i,
    x < fib K ->
    In i (band_support offset x) ->
    offset + 2 <= i.
Proof.
  intros offset K x i Hx Hin.
  exact (proj1 (band_support_window offset K x i Hx Hin)).
Qed.

(*
│
│          We now split the two-sided window-containment statement
│          into the one-sided projections that later proofs actually
│          consume. Lower-bound arguments appeal only to
│          `band_support_lower_bound`, upper-bound arguments only to
│          `band_support_upper_bound`.
│
*)

(*         x < fib(K) ∧ i ∈ band_support(offset, x) ⇒ offset + 2 ≤ i          *)
(*         x < fib(K) ∧ i ∈ band_support(offset, x) ⇒ i < offset + K.         *)

Lemma band_support_upper_bound :
  forall offset K x i,
    x < fib K ->
    In i (band_support offset x) ->
    i < offset + K.
Proof.
  intros offset K x i Hx Hin.
  exact (proj2 (band_support_window offset K x i Hx Hin)).
Qed.

(*
│
│          With the geometric window bounds in hand, we can now pass
│          from support membership to executable recognition. Any
│          index that genuinely comes from the translated support must
│          make the boolean band test succeed.
│
*)

(*       i ∈ band_support(offset, x) ⇒ band_pred(offset, K, i) = true.        *)

Lemma band_pred_true_on_support :
  forall offset K x i,
    x < fib K ->
    In i (band_support offset x) ->
    band_pred offset K i = true.
Proof.
  intros offset K x i Hx Hin.
  unfold band_pred.
  destruct (band_support_window offset K x i Hx Hin) as [Hlow Hhigh].
  apply andb_true_intro.
  split.
  - apply Nat.leb_le.
    exact Hlow.
  - apply Nat.ltb_lt.
    exact Hhigh.
Qed.

(*
│
│          Recognition is only half of the later decoding story. We
│          also need the complementary fact that once an index falls
│          outside the window, the same boolean test fails for the
│          corresponding geometric reason.
│
*)

Lemma band_pred_false_of_low :
  forall offset K k,
    k < offset + 2 ->
    band_pred offset K k = false.
Proof.
  intros offset K k Hlt.
  unfold band_pred.
  apply andb_false_intro1.
  apply Nat.leb_gt.
  exact Hlt.
Qed.

Lemma band_pred_false_of_high :
  forall offset K k,
    offset + K <= k ->
    band_pred offset K k = false.
Proof.
  intros offset K k Hge.
  unfold band_pred.
  apply andb_false_intro2.
  apply Nat.ltb_ge.
  exact Hge.
Qed.

(*
│
│          The next two exclusion lemmas isolate the two ways in which
│          a band test can fail. Either an index sits strictly below
│          the left edge of the window, or it sits at or beyond the
│          right edge. The support-exclusion lemmas below simply
│          combine these local failure modes with the window bounds
│          already established for translated supports.
│
*)

(*              k < offset + 2 ⇒ band_pred(offset, K, k) = false              *)
(*             offset + K ≤ k ⇒ band_pred(offset, K, k) = false.              *)

Lemma band_pred_false_on_support_above :
  forall offset K offset' K' x i,
    x < fib K' ->
    In i (band_support offset' x) ->
    offset + K <= offset' + 2 ->
    band_pred offset K i = false.
Proof.
  intros offset K offset' K' x i Hx Hin Hsep.
  apply band_pred_false_of_high.
  pose proof (band_support_lower_bound offset' K' x i Hx Hin) as Hlow.
  lia.
Qed.

Lemma band_pred_false_on_support_below :
  forall offset K offset' K' x i,
    x < fib K' ->
    In i (band_support offset' x) ->
    offset' + K' <= offset + 2 ->
    band_pred offset K i = false.
Proof.
  intros offset K offset' K' x i Hx Hin Hsep.
  apply band_pred_false_of_low.
  pose proof (band_support_upper_bound offset' K' x i Hx Hin) as Hhigh.
  lia.
Qed.

(*
│
│          The next helper lemmas package the generic
│          window-separation arguments. Once the relative position of
│          two bands has been fixed arithmetically, predicate
│          exclusion and pointwise index separation follow uniformly.
│
*)

(*            {k − offset ∣ k ∈ band_support(offset, x)} = Z0(x).             *)

Lemma map_sub_band_support :
  forall offset x,
    map (fun k => k - offset) (band_support offset x) = Z0 x.
Proof.
  intros offset x.
  unfold band_support.
  rewrite map_map.
  rewrite <- map_id.
  apply map_ext.
  intro a.
  lia.
Qed.

(*
│
│          So translation by a fixed offset is not merely injective on
│          support indices; it is literally reversible by subtraction.
│          We use this exact recovery fact later when we decode a
│          global state code back into local `IP`, `R1`, and `R2`
│          payloads.
│
*)

(*           map(k ↦ k − offset, band_support(offset, x)) = Z0(x).            *)

(*
│
│          We now specialize the generic window lemmas to the concrete
│          `IP`, `R1`, and `R2` bands. First we show that each
│          predicate recognizes its own support on valid payloads;
│          then we show that the foreign predicates are automatically
│          false on that same support.
│
*)

(*           ip < ip_limit ∧ i ∈ ip_support(ip) ⇒ ip_pred(i) = true           *)
(*           r1 < r1_limit ∧ i ∈ r1_support(r1) ⇒ r1_pred(i) = true           *)
(*          r2 < r2_limit ∧ i ∈ r2_support(r2) ⇒ r2_pred(i) = true.           *)

Lemma ip_pred_true_on_ip_support :
  forall ip i,
    ip < ip_limit ->
    In i (ip_support ip) ->
    ip_pred i = true.
Proof.
  intros ip i Hip Hin.
  unfold ip_pred, ip_support, ip_limit in *.
  exact (band_pred_true_on_support IP_offset K_IP ip i Hip Hin).
Qed.

Lemma r1_pred_true_on_r1_support :
  forall r1 i,
    r1 < r1_limit ->
    In i (r1_support r1) ->
    r1_pred i = true.
Proof.
  intros r1 i Hr1 Hin.
  unfold r1_pred, r1_support, r1_limit in *.
  exact (band_pred_true_on_support R1_offset K_R1 r1 i Hr1 Hin).
Qed.

Lemma r2_pred_true_on_r2_support :
  forall r2 i,
    r2 < r2_limit ->
    In i (r2_support r2) ->
    r2_pred i = true.
Proof.
  intros r2 i Hr2 Hin.
  unfold r2_pred, r2_support, r2_limit in *.
  exact (band_pred_true_on_support R2_offset K_R2 r2 i Hr2 Hin).
Qed.

(*
│
│          We now switch from recognition to exclusion in the concrete
│          layout. Because the three windows are disjoint and ordered,
│          an index recognized by one band is automatically rejected
│          by the other two predicates.
│
*)

(*          i ∈ ip_support ⇒ r1_pred(i) = false ∧ r2_pred(i) = false          *)
(*          i ∈ r1_support ⇒ ip_pred(i) = false ∧ r2_pred(i) = false          *)
(*         i ∈ r2_support ⇒ ip_pred(i) = false ∧ r1_pred(i) = false.          *)

Lemma ip_pred_false_on_r1_support :
  forall r1 i,
    r1 < r1_limit ->
    In i (r1_support r1) ->
    ip_pred i = false.
Proof.
  intros r1 i Hr1 Hin.
  unfold ip_pred.
  eapply band_pred_false_on_support_above.
  - exact Hr1.
  - exact Hin.
  - unfold IP_offset, K_IP, R1_offset.
    lia.
Qed.

Lemma ip_pred_false_on_r2_support :
  forall r2 i,
    r2 < r2_limit ->
    In i (r2_support r2) ->
    ip_pred i = false.
Proof.
  intros r2 i Hr2 Hin.
  unfold ip_pred.
  eapply band_pred_false_on_support_above.
  - exact Hr2.
  - exact Hin.
  - unfold IP_offset, K_IP, R2_offset.
    lia.
Qed.

Lemma r1_pred_false_on_ip_support :
  forall ip i,
    ip < ip_limit ->
    In i (ip_support ip) ->
    r1_pred i = false.
Proof.
  intros ip i Hip Hin.
  unfold r1_pred.
  eapply band_pred_false_on_support_below.
  - exact Hip.
  - exact Hin.
  - unfold IP_offset, K_IP, R1_offset, K_R1.
    lia.
Qed.

Lemma r1_pred_false_on_r2_support :
  forall r2 i,
    r2 < r2_limit ->
    In i (r2_support r2) ->
    r1_pred i = false.
Proof.
  intros r2 i Hr2 Hin.
  unfold r1_pred.
  eapply band_pred_false_on_support_above.
  - exact Hr2.
  - exact Hin.
  - unfold R1_offset, K_R1, R2_offset.
    lia.
Qed.

Lemma r2_pred_false_on_ip_support :
  forall ip i,
    ip < ip_limit ->
    In i (ip_support ip) ->
    r2_pred i = false.
Proof.
  intros ip i Hip Hin.
  unfold r2_pred.
  eapply band_pred_false_on_support_below.
  - exact Hip.
  - exact Hin.
  - unfold IP_offset, K_IP, R2_offset, K_R2.
    lia.
Qed.

Lemma r2_pred_false_on_r1_support :
  forall r1 i,
    r1 < r1_limit ->
    In i (r1_support r1) ->
    r2_pred i = false.
Proof.
  intros r1 i Hr1 Hin.
  unfold r2_pred.
  eapply band_pred_false_on_support_below.
  - exact Hr1.
  - exact Hin.
  - unfold R1_offset, K_R1, R2_offset, K_R2.
    lia.
Qed.

(*
│
│          Once predicate-level exclusion is settled, we can return to
│          the underlying occupied indices themselves. The next pair
│          of lemmas forget booleans entirely and express the same
│          separation directly as strict order and a two-step gap.
│
*)

(*                      separated windows ⇒ i_hi > i_lo                       *)
(*          separated windows with one-step slack ⇒ i_hi ≥ i_lo + 2.          *)

Lemma band_support_gt_of_separated_windows :
  forall offset_hi K_hi x i_hi offset_lo K_lo y i_lo,
    x < fib K_hi ->
    y < fib K_lo ->
    In i_hi (band_support offset_hi x) ->
    In i_lo (band_support offset_lo y) ->
    offset_lo + K_lo <= offset_hi + 2 ->
    i_hi > i_lo.
Proof.
  intros offset_hi K_hi x i_hi offset_lo K_lo y i_lo Hx Hy Hhi Hlo Hsep.
  pose proof (band_support_lower_bound offset_hi K_hi x i_hi Hx Hhi) as Hlow_hi.
  pose proof (band_support_upper_bound offset_lo K_lo y i_lo Hy Hlo) as Hhigh_lo.
  lia.
Qed.

Lemma band_support_gap_of_separated_windows :
  forall offset_hi K_hi x i_hi offset_lo K_lo y i_lo,
    x < fib K_hi ->
    y < fib K_lo ->
    In i_hi (band_support offset_hi x) ->
    In i_lo (band_support offset_lo y) ->
    offset_lo + K_lo <= offset_hi + 1 ->
    i_hi >= i_lo + 2.
Proof.
  intros offset_hi K_hi x i_hi offset_lo K_lo y i_lo Hx Hy Hhi Hlo Hsep.
  pose proof (band_support_lower_bound offset_hi K_hi x i_hi Hx Hhi) as Hlow_hi.
  pose proof (band_support_upper_bound offset_lo K_lo y i_lo Hy Hlo) as Hhigh_lo.
  lia.
Qed.

(*
│
│          Once we have fixed the relative position of two bands
│          arithmetically, we upgrade that information to pointwise
│          index separation. The two generic separation lemmas above
│          are the abstract geometric engine behind all later
│          isolation theorems for the fixed and parametric layouts.
│
*)

(*               offset_lo + K_lo ≤ offset_hi + 2 ⇒ i_hi > i_lo               *)
(*            offset_lo + K_lo ≤ offset_hi + 1 ⇒ i_hi ≥ i_lo + 2.             *)

(*
│
│          We now instantiate that abstract separation engine for the
│          three concrete windows of the fixed machine. This is the
│          direct geometric content of the layout: `R1` sits above
│          `IP`, `R2` sits above `R1`, and `R2` also sits above `IP`.
│
*)

(*          i₁ ∈ r1_support(r1) ∧ i₀ ∈ ip_support(ip) ⇒ i₁ ≥ i₀ + 2           *)
(*          i₂ ∈ r2_support(r2) ∧ i₁ ∈ r1_support(r1) ⇒ i₂ ≥ i₁ + 2           *)
(*          i₂ ∈ r2_support(r2) ∧ i₀ ∈ ip_support(ip) ⇒ i₂ ≥ i₀ + 2.          *)

Lemma r1_support_gt_ip_support :
  forall r1 ip i1 i0,
    r1 < r1_limit ->
    ip < ip_limit ->
    In i1 (r1_support r1) ->
    In i0 (ip_support ip) ->
    i1 > i0.
Proof.
  intros r1 ip i1 i0 Hr1 Hip H1 H0.
  eapply band_support_gt_of_separated_windows.
  - exact Hr1.
  - exact Hip.
  - exact H1.
  - exact H0.
  - unfold R1_offset, K_R1, IP_offset, K_IP.
    lia.
Qed.

Lemma r1_support_gap_ip_support :
  forall r1 ip i1 i0,
    r1 < r1_limit ->
    ip < ip_limit ->
    In i1 (r1_support r1) ->
    In i0 (ip_support ip) ->
    i1 >= i0 + 2.
Proof.
  intros r1 ip i1 i0 Hr1 Hip H1 H0.
  eapply band_support_gap_of_separated_windows.
  - exact Hr1.
  - exact Hip.
  - exact H1.
  - exact H0.
  - unfold R1_offset, K_R1, IP_offset, K_IP.
    lia.
Qed.

Lemma r2_support_gt_r1_support :
  forall r2 r1 i2 i1,
    r2 < r2_limit ->
    r1 < r1_limit ->
    In i2 (r2_support r2) ->
    In i1 (r1_support r1) ->
    i2 > i1.
Proof.
  intros r2 r1 i2 i1 Hr2 Hr1 H2 H1.
  eapply band_support_gt_of_separated_windows.
  - exact Hr2.
  - exact Hr1.
  - exact H2.
  - exact H1.
  - unfold R2_offset, K_R2, R1_offset, K_R1.
    lia.
Qed.

Lemma r2_support_gap_r1_support :
  forall r2 r1 i2 i1,
    r2 < r2_limit ->
    r1 < r1_limit ->
    In i2 (r2_support r2) ->
    In i1 (r1_support r1) ->
    i2 >= i1 + 2.
Proof.
  intros r2 r1 i2 i1 Hr2 Hr1 H2 H1.
  eapply band_support_gap_of_separated_windows.
  - exact Hr2.
  - exact Hr1.
  - exact H2.
  - exact H1.
  - unfold R2_offset, K_R2, R1_offset, K_R1.
    lia.
Qed.

Lemma r2_support_gt_ip_support :
  forall r2 ip i2 i0,
    r2 < r2_limit ->
    ip < ip_limit ->
    In i2 (r2_support r2) ->
    In i0 (ip_support ip) ->
    i2 > i0.
Proof.
  intros r2 ip i2 i0 Hr2 Hip H2 H0.
  eapply band_support_gt_of_separated_windows.
  - exact Hr2.
  - exact Hip.
  - exact H2.
  - exact H0.
  - unfold R2_offset, K_R2, IP_offset, K_IP.
    lia.
Qed.

Lemma r2_support_gap_ip_support :
  forall r2 ip i2 i0,
    r2 < r2_limit ->
    ip < ip_limit ->
    In i2 (r2_support r2) ->
    In i0 (ip_support ip) ->
    i2 >= i0 + 2.
Proof.
  intros r2 ip i2 i0 Hr2 Hip H2 H0.
  eapply band_support_gap_of_separated_windows.
  - exact Hr2.
  - exact Hip.
  - exact H2.
  - exact H0.
  - unfold R2_offset, K_R2, IP_offset, K_IP.
    lia.
Qed.

(*
│
│          `IP_R1_Isolation` is the first concrete isolation theorem
│          for the machine layout: every occupied `R1` index lies at
│          least two Fibonacci positions above every occupied `IP`
│          index, so the two windows cannot interfere.
│
*)

(* ip < ip_limit ∧ r1 < r1_limit ∧ i1 ∈ r1_support(r1) ∧ i0 ∈ ip_support(ip)  *)
(*                               ⇒ i1 ≥ i0 + 2.                               *)

Theorem IP_R1_Isolation :
  forall ip r1 i1 i0,
    ip < ip_limit ->
    r1 < r1_limit ->
    In i1 (r1_support r1) ->
    In i0 (ip_support ip) ->
    i1 >= i0 + 2.
Proof.
  intros ip r1 i1 i0 Hip Hr1 H1 H0.
  apply (r1_support_gap_ip_support r1 ip i1 i0); assumption.
Qed.

(*
│
│          We now replay the same carryless-band story parametrically
│          over an abstract `MachineLimits` package. The concrete
│          constants remain available, but the `_of` definitions
│          provide the abstraction boundary used later by the
│          universality layers, where the exact offsets and widths are
│          no longer fixed once and for all.
│
*)

(*    ip_limit_of(L) = fib(ml_K_IP(L)), r1_limit_of(L) = fib(ml_K_R1(L)),     *)
(*                      r2_limit_of(L) = fib(ml_K_R2(L))                      *)
(*           ip_support_of(L, x) = band_support(ml_IP_offset(L), x)           *)
(*           r1_support_of(L, x) = band_support(ml_R1_offset(L), x)           *)
(*          r2_support_of(L, x) = band_support(ml_R2_offset(L), x).           *)

Definition ip_limit_of (L : MachineLimits) : nat := fib (ml_K_IP L).
Definition r1_limit_of (L : MachineLimits) : nat := fib (ml_K_R1 L).
Definition r2_limit_of (L : MachineLimits) : nat := fib (ml_K_R2 L).

Definition ip_support_of (L : MachineLimits) : nat -> list nat :=
  band_support (ml_IP_offset L).

Definition r1_support_of (L : MachineLimits) : nat -> list nat :=
  band_support (ml_R1_offset L).

Definition r2_support_of (L : MachineLimits) : nat -> list nat :=
  band_support (ml_R2_offset L).

Definition ip_code_of (L : MachineLimits) : nat -> nat :=
  band_code (ml_IP_offset L).

Definition r1_code_of (L : MachineLimits) : nat -> nat :=
  band_code (ml_R1_offset L).

Definition r2_code_of (L : MachineLimits) : nat -> nat :=
  band_code (ml_R2_offset L).

Definition ip_pred_of (L : MachineLimits) (k : nat) : bool :=
  band_pred (ml_IP_offset L) (ml_K_IP L) k.

Definition r1_pred_of (L : MachineLimits) (k : nat) : bool :=
  band_pred (ml_R1_offset L) (ml_K_R1 L) k.

Definition r2_pred_of (L : MachineLimits) (k : nat) : bool :=
  band_pred (ml_R2_offset L) (ml_K_R2 L) k.

(*
│
│          So the parametric interface is deliberately literal: we
│          keep the fixed vocabulary, but thread a limit package `L`
│          through every support, code, and predicate. This lets later
│          files reason abstractly without changing the shape of any
│          statement.
│
*)

(* ip_support, r1_support, r2_support ⇝ ip_support_of(L, ·), r1_support_of(L, *)
(*                          ·), r2_support_of(L, ·).                          *)

(*
│
│          We first rebuild the predicate-recognition and
│          predicate-exclusion facts in the parametric setting. The
│          proofs are intentionally parallel to the fixed ones: the
│          only difference is that the separating arithmetic now comes
│          from the record fields of `L`.
│
*)

(*ip_pred_of(L, i) = true on ip_support_of(L, ip), ip_pred_of(L, i) = false on*)
(*              the foreign supports, and similarly cyclically.               *)

Lemma ip_pred_true_on_ip_support_of :
  forall L ip i,
    ip < ip_limit_of L ->
    In i (ip_support_of L ip) ->
    ip_pred_of L i = true.
Proof.
  intros L ip i Hip Hin.
  unfold ip_pred_of, ip_support_of, ip_limit_of in *.
  exact (band_pred_true_on_support (ml_IP_offset L) (ml_K_IP L) ip i Hip Hin).
Qed.

Lemma r1_pred_true_on_r1_support_of :
  forall L r1 i,
    r1 < r1_limit_of L ->
    In i (r1_support_of L r1) ->
    r1_pred_of L i = true.
Proof.
  intros L r1 i Hr1 Hin.
  unfold r1_pred_of, r1_support_of, r1_limit_of in *.
  exact (band_pred_true_on_support (ml_R1_offset L) (ml_K_R1 L) r1 i Hr1 Hin).
Qed.

Lemma r2_pred_true_on_r2_support_of :
  forall L r2 i,
    r2 < r2_limit_of L ->
    In i (r2_support_of L r2) ->
    r2_pred_of L i = true.
Proof.
  intros L r2 i Hr2 Hin.
  unfold r2_pred_of, r2_support_of, r2_limit_of in *.
  exact (band_pred_true_on_support (ml_R2_offset L) (ml_K_R2 L) r2 i Hr2 Hin).
Qed.

(*
│
│          This gives the positive half of the abstract decoder story:
│          each `_of` predicate still recognizes precisely its own
│          translated support.
│
*)

(*
│
│          The same rhythm now repeats in the abstract family: first
│          own-band recognition, then foreign-band exclusion. The only
│          new ingredient is that the disjointness arithmetic is no
│          longer hard-coded but supplied by the record fields of `L`.
│
*)

(*             i ∈ ip_support_of(L, ·) ⇒ ip_pred_of(L, i) = true              *)
(*             i ∈ r1_support_of(L, ·) ⇒ r1_pred_of(L, i) = true              *)
(*             i ∈ r2_support_of(L, ·) ⇒ r2_pred_of(L, i) = true.             *)

Lemma ip_pred_false_on_r1_support_of :
  forall L r1 i,
    r1 < r1_limit_of L ->
    In i (r1_support_of L r1) ->
    ip_pred_of L i = false.
Proof.
  intros L r1 i Hr1 Hin.
  unfold ip_pred_of, r1_support_of, r1_limit_of in *.
  eapply band_pred_false_on_support_above.
  - exact Hr1.
  - exact Hin.
  - pose proof (ml_sep_ip_r1 L) as Hsep.
    lia.
Qed.

Lemma ip_pred_false_on_r2_support_of :
  forall L r2 i,
    r2 < r2_limit_of L ->
    In i (r2_support_of L r2) ->
    ip_pred_of L i = false.
Proof.
  intros L r2 i Hr2 Hin.
  unfold ip_pred_of, r2_support_of, r2_limit_of in *.
  eapply band_pred_false_on_support_above.
  - exact Hr2.
  - exact Hin.
  - pose proof (ml_sep_ip_r2 L) as Hsep.
    lia.
Qed.

Lemma r1_pred_false_on_ip_support_of :
  forall L ip i,
    ip < ip_limit_of L ->
    In i (ip_support_of L ip) ->
    r1_pred_of L i = false.
Proof.
  intros L ip i Hip Hin.
  unfold r1_pred_of, ip_support_of, ip_limit_of in *.
  eapply band_pred_false_on_support_below.
  - exact Hip.
  - exact Hin.
  - pose proof (ml_sep_ip_r1 L) as Hsep.
    lia.
Qed.

Lemma r1_pred_false_on_r2_support_of :
  forall L r2 i,
    r2 < r2_limit_of L ->
    In i (r2_support_of L r2) ->
    r1_pred_of L i = false.
Proof.
  intros L r2 i Hr2 Hin.
  unfold r1_pred_of, r2_support_of, r2_limit_of in *.
  eapply band_pred_false_on_support_above.
  - exact Hr2.
  - exact Hin.
  - pose proof (ml_sep_r1_r2 L) as Hsep.
    lia.
Qed.

Lemma r2_pred_false_on_ip_support_of :
  forall L ip i,
    ip < ip_limit_of L ->
    In i (ip_support_of L ip) ->
    r2_pred_of L i = false.
Proof.
  intros L ip i Hip Hin.
  unfold r2_pred_of, ip_support_of, ip_limit_of in *.
  eapply band_pred_false_on_support_below.
  - exact Hip.
  - exact Hin.
  - pose proof (ml_sep_ip_r2 L) as Hsep.
    lia.
Qed.

Lemma r2_pred_false_on_r1_support_of :
  forall L r1 i,
    r1 < r1_limit_of L ->
    In i (r1_support_of L r1) ->
    r2_pred_of L i = false.
Proof.
  intros L r1 i Hr1 Hin.
  unfold r2_pred_of, r1_support_of, r1_limit_of in *.
  eapply band_pred_false_on_support_below.
  - exact Hr1.
  - exact Hin.
  - pose proof (ml_sep_r1_r2 L) as Hsep.
    lia.
Qed.

(*
│
│          At this point the three abstract predicates are separated
│          exactly as in the fixed geometry. Any occupied index
│          belongs to its own band view and is rejected by the two
│          foreign views.
│
*)

(*   own-band truth + foreign-band falsity = a three-way support partition    *)
(*                               indexed by L.                                *)

(*
│
│          We next specialize the abstract separation engine itself.
│          The point is that a `MachineLimits` record does not merely
│          store three capacities and three offsets; it also certifies
│          the exact inequalities needed to infer strict order and a
│          two-step gap between the corresponding supports.
│
*)

(*    ml_sep_ip_r1(L) ⇒ r1_support_of(L, ·) lies above ip_support_of(L, ·)    *)
(*    ml_sep_r1_r2(L) ⇒ r2_support_of(L, ·) lies above r1_support_of(L, ·)    *)
(*   ml_sep_ip_r2(L) ⇒ r2_support_of(L, ·) lies above ip_support_of(L, ·).    *)

Lemma r1_support_gt_ip_support_of :
  forall L r1 ip i1 i0,
    r1 < r1_limit_of L ->
    ip < ip_limit_of L ->
    In i1 (r1_support_of L r1) ->
    In i0 (ip_support_of L ip) ->
    i1 > i0.
Proof.
  intros L r1 ip i1 i0 Hr1 Hip H1 H0.
  unfold r1_support_of, r1_limit_of, ip_support_of, ip_limit_of in *.
  eapply band_support_gt_of_separated_windows.
  - exact Hr1.
  - exact Hip.
  - exact H1.
  - exact H0.
  - pose proof (ml_sep_ip_r1 L) as Hsep.
    lia.
Qed.

Lemma r1_support_gap_ip_support_of :
  forall L r1 ip i1 i0,
    r1 < r1_limit_of L ->
    ip < ip_limit_of L ->
    In i1 (r1_support_of L r1) ->
    In i0 (ip_support_of L ip) ->
    i1 >= i0 + 2.
Proof.
  intros L r1 ip i1 i0 Hr1 Hip H1 H0.
  unfold r1_support_of, r1_limit_of, ip_support_of, ip_limit_of in *.
  eapply band_support_gap_of_separated_windows.
  - exact Hr1.
  - exact Hip.
  - exact H1.
  - exact H0.
  - exact (ml_sep_ip_r1 L).
Qed.

Lemma r2_support_gt_r1_support_of :
  forall L r2 r1 i2 i1,
    r2 < r2_limit_of L ->
    r1 < r1_limit_of L ->
    In i2 (r2_support_of L r2) ->
    In i1 (r1_support_of L r1) ->
    i2 > i1.
Proof.
  intros L r2 r1 i2 i1 Hr2 Hr1 H2 H1.
  unfold r2_support_of, r2_limit_of, r1_support_of, r1_limit_of in *.
  eapply band_support_gt_of_separated_windows.
  - exact Hr2.
  - exact Hr1.
  - exact H2.
  - exact H1.
  - pose proof (ml_sep_r1_r2 L) as Hsep.
    lia.
Qed.

Lemma r2_support_gap_r1_support_of :
  forall L r2 r1 i2 i1,
    r2 < r2_limit_of L ->
    r1 < r1_limit_of L ->
    In i2 (r2_support_of L r2) ->
    In i1 (r1_support_of L r1) ->
    i2 >= i1 + 2.
Proof.
  intros L r2 r1 i2 i1 Hr2 Hr1 H2 H1.
  unfold r2_support_of, r2_limit_of, r1_support_of, r1_limit_of in *.
  eapply band_support_gap_of_separated_windows.
  - exact Hr2.
  - exact Hr1.
  - exact H2.
  - exact H1.
  - exact (ml_sep_r1_r2 L).
Qed.

Lemma r2_support_gt_ip_support_of :
  forall L r2 ip i2 i0,
    r2 < r2_limit_of L ->
    ip < ip_limit_of L ->
    In i2 (r2_support_of L r2) ->
    In i0 (ip_support_of L ip) ->
    i2 > i0.
Proof.
  intros L r2 ip i2 i0 Hr2 Hip H2 H0.
  unfold r2_support_of, r2_limit_of, ip_support_of, ip_limit_of in *.
  eapply band_support_gt_of_separated_windows.
  - exact Hr2.
  - exact Hip.
  - exact H2.
  - exact H0.
  - pose proof (ml_sep_ip_r2 L) as Hsep.
    lia.
Qed.

Lemma r2_support_gap_ip_support_of :
  forall L r2 ip i2 i0,
    r2 < r2_limit_of L ->
    ip < ip_limit_of L ->
    In i2 (r2_support_of L r2) ->
    In i0 (ip_support_of L ip) ->
    i2 >= i0 + 2.
Proof.
  intros L r2 ip i2 i0 Hr2 Hip H2 H0.
  unfold r2_support_of, r2_limit_of, ip_support_of, ip_limit_of in *.
  eapply band_support_gap_of_separated_windows.
  - exact Hr2.
  - exact Hip.
  - exact H2.
  - exact H0.
  - exact (ml_sep_ip_r2 L).
Qed.

(*
│
│          We then lift the geometric separation lemmas themselves to
│          the abstract family. At this stage the concrete offsets
│          disappear completely; only the three record inequalities
│          `ml_sep_ip_r1`, `ml_sep_r1_r2`, and `ml_sep_ip_r2` remain.
│
*)

(*  ml_sep_ip_r1(L), ml_sep_r1_r2(L), ml_sep_ip_r2(L) ⇒ the same support-gap  *)
(*                    conclusions as in the fixed layout.                     *)

(*
│
│          We close the parametric block by exporting the same summary
│          isolation theorem as before, now stated uniformly for
│          arbitrary `MachineLimits`. This is usually the form that
│          later files cite.
│
*)

(*
│
│          `IP_R1_Isolation_of` is the generic form of the first fixed
│          isolation theorem. We expose it separately because later
│          family-level statements quantify over arbitrary
│          `MachineLimits`, not just the built-in concrete package.
│
*)

(*ip < ip_limit_of(L) ∧ r1 < r1_limit_of(L) ∧ i₁ ∈ r1_support_of(L, r1) ∧ i₀ ∈*)
(*                    ip_support_of(L, ip) ⇒ i₁ ≥ i₀ + 2.                     *)

Theorem IP_R1_Isolation_of :
  forall L ip r1 i1 i0,
    ip < ip_limit_of L ->
    r1 < r1_limit_of L ->
    In i1 (r1_support_of L r1) ->
    In i0 (ip_support_of L ip) ->
    i1 >= i0 + 2.
Proof.
  intros L ip r1 i1 i0 Hip Hr1 H1 H0.
  apply (r1_support_gap_ip_support_of L r1 ip i1 i0); assumption.
Qed.
