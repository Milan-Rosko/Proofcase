(*P001_98_02C_Proof.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / P001_98_02C_Proof                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  We discharges the peeled goals by a single local proof development built
  from lemmas and reconstruct the (i) 2-adic core, (ii) the finite odd
  codomain, (iii) the collision step, (iv) and the divisibility orientation.
  We then exports the endpoint witness.

*)

From P001 Require Export P001_01_Reframing.

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                               PEELED GOALS                              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The proof phase restates the peeled goals locally so it
│          remains sequentially above `P001_01_Reframing` without
│          importing `P001_98_01_0_Peeling`.
│
*)

Definition show_two_adic_factorization : Prop :=
  forall n x,
    1 <= x ->
    x <= 2 * n ->
    exists k m,
      x = 2 ^ k * m /\
      Nat.Odd m.

Definition show_odd_domain_exhaustion : Prop :=
  forall n,
    exists odd_domain : list nat,
      NoDup odd_domain /\
      length odd_domain = n /\
      forall m,
        In m odd_domain <->
        1 <= m /\ m <= 2 * n /\ Nat.Odd m.

Definition show_odd_core_collision : Prop :=
  forall n A,
    (forall a, In a A -> 1 <= a /\ a <= 2 * n) ->
    NoDup A ->
    length A = n + 1 ->
    exists y z m i j,
      In y A /\
      In z A /\
      y <> z /\
      1 <= m /\
      m <= 2 * n /\
      Nat.Odd m /\
      y = 2 ^ i * m /\
      z = 2 ^ j * m.

Definition show_common_odd_core_implies_divisibility : Prop :=
  forall n A y z m i j,
    In y A ->
    In z A ->
    y <> z ->
    1 <= m ->
    m <= 2 * n ->
    Nat.Odd m ->
    y = 2 ^ i * m ->
    z = 2 ^ j * m ->
    Nat.divide y z \/ Nat.divide z y.

Definition peeling_package : Prop :=
  show_two_adic_factorization /\
  show_odd_domain_exhaustion /\
  show_odd_core_collision /\
  show_common_odd_core_implies_divisibility.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                               2-ADIC CORE                               ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

Fixpoint odd_part_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => n
  | S fuel' =>
      if Nat.even n
      then odd_part_aux fuel' (Nat.div2 n)
      else n
  end.

Definition odd_part (n : nat) : nat :=
  odd_part_aux n n.

Fixpoint val2_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      if Nat.even n
      then S (val2_aux fuel' (Nat.div2 n))
      else 0
  end.

Definition val2 (n : nat) : nat :=
  val2_aux n n.

Lemma odd_part_aux_le :
  forall fuel n,
    odd_part_aux fuel n <= n.
Proof.
  induction fuel as [|fuel IH]; intros n.
  - simpl. lia.
  - simpl.
    destruct (Nat.even n) eqn:Heven.
    + pose proof (IH (Nat.div2 n)) as Hrec.
      pose proof (Nat.div2_decr n n) as Hdiv2.
      specialize (Hdiv2 ltac:(lia)).
      lia.
    + lia.
Qed.

Lemma even_div2_eq :
  forall n,
    Nat.even n = true ->
    n = 2 * Nat.div2 n.
Proof.
  intros n Heven.
  apply Nat.even_spec in Heven.
  destruct Heven as [k Hk].
  subst n.
  rewrite Nat.div2_double.
  lia.
Qed.

Lemma even_div2_pos :
  forall n,
    Nat.even n = true ->
    1 <= n ->
    1 <= Nat.div2 n.
Proof.
  intros n Heven Hn.
  apply Nat.even_spec in Heven.
  destruct Heven as [k Hk].
  subst n.
  rewrite Nat.div2_double.
  destruct k as [|k'].
  - lia.
  - lia.
Qed.

Lemma div2_below_predecessor :
  forall fuel n,
    1 <= n ->
    n <= S fuel ->
    Nat.div2 n <= fuel.
Proof.
  intros fuel n Hn Hle.
  pose proof (Nat.lt_div2 n Hn) as Hlt.
  lia.
Qed.

Lemma odd_part_aux_odd :
  forall fuel n,
    1 <= n ->
    n <= fuel ->
    Nat.odd (odd_part_aux fuel n) = true.
Proof.
  induction fuel as [|fuel IH]; intros n Hn Hle.
  - lia.
  - simpl.
    destruct (Nat.even n) eqn:Heven.
    + assert (Hn_div2 : 1 <= Nat.div2 n) by
          (exact (even_div2_pos n Heven Hn)).
      assert (Hle_div2 : Nat.div2 n <= fuel) by
          (exact (div2_below_predecessor fuel n Hn Hle)).
      exact (IH (Nat.div2 n) Hn_div2 Hle_div2).
    + rewrite <- Nat.negb_even.
      rewrite Heven.
      reflexivity.
Qed.

Lemma odd_part_odd :
  forall n,
    1 <= n ->
    Nat.odd (odd_part n) = true.
Proof.
  intros n Hn.
  unfold odd_part.
  apply odd_part_aux_odd.
  - exact Hn.
  - lia.
Qed.

Lemma odd_part_le :
  forall n, odd_part n <= n.
Proof.
  intro n.
  unfold odd_part.
  apply odd_part_aux_le.
Qed.

Lemma odd_part_pos :
  forall n,
    1 <= n ->
    1 <= odd_part n.
Proof.
  intros n Hn.
  pose proof (odd_part_odd n Hn) as Hodd.
  apply Nat.odd_spec in Hodd.
  destruct Hodd as [k Hk].
  rewrite Hk.
  lia.
Qed.

Lemma decomposition_aux :
  forall fuel n,
    1 <= n ->
    n <= fuel ->
    n = 2 ^ (val2_aux fuel n) * odd_part_aux fuel n.
Proof.
  induction fuel as [|fuel IH]; intros n Hn Hle.
  - lia.
  - simpl.
    destruct (Nat.even n) eqn:Heven.
    + assert (Hd : n = 2 * Nat.div2 n) by
          (exact (even_div2_eq n Heven)).
      assert (Hdiv2_pos : 1 <= Nat.div2 n) by
          (exact (even_div2_pos n Heven Hn)).
      assert (Hdiv2_le : Nat.div2 n <= fuel) by
          (exact (div2_below_predecessor fuel n Hn Hle)).
      specialize (IH (Nat.div2 n) Hdiv2_pos Hdiv2_le).
      rewrite Hd at 1.
      rewrite IH at 1.
      rewrite Nat.pow_succ_r'.
      rewrite <- Nat.mul_assoc.
      reflexivity.
    + simpl.
      lia.
Qed.

Lemma decomposition :
  forall n,
    1 <= n ->
    n = 2 ^ (val2 n) * odd_part n.
Proof.
  intros n Hn.
  unfold val2, odd_part.
  apply decomposition_aux.
  - exact Hn.
  - lia.
Qed.

Lemma common_odd_core_implies_divisibility :
  forall y z m i j,
    y = 2 ^ i * m ->
    z = 2 ^ j * m ->
    Nat.divide y z \/ Nat.divide z y.
Proof.
  intros y z m i j Hy Hz.
  assert (Hdyadic :
            forall a b,
              a <= b ->
              Nat.divide (2 ^ a * m) (2 ^ b * m)).
  {
    intros a b Hab.
    exists (2 ^ (b - a)).
    assert (Hb : b = (b - a) + a) by lia.
    rewrite Hb at 1.
    rewrite Nat.pow_add_r.
    rewrite <- Nat.mul_assoc.
    reflexivity.
  }
  destruct (Nat.le_gt_cases i j) as [Hij | Hji].
  - left.
    rewrite Hy, Hz.
    exact (Hdyadic i j Hij).
  - right.
    rewrite Hy, Hz.
    exact (Hdyadic j i (Nat.lt_le_incl _ _ Hji)).
Qed.

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                           FINITE ODD CODOMAIN                           │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

Fixpoint odd_range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => odd_range n' ++ [2 * n' + 1]
  end.

Lemma odd_range_length :
  forall n, length (odd_range n) = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite length_app. simpl.
    rewrite IH. lia.
Qed.

Lemma odd_range_in_iff :
  forall n k,
    In k (odd_range n) <-> exists i, i < n /\ k = 2 * i + 1.
Proof.
  induction n as [|n IH]; intros k.
  - simpl. split.
    + intros Hin. inversion Hin.
    + intros [i [Hi _]]. lia.
  - split.
    + intros Hin.
      simpl in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * apply IH in Hin.
        destruct Hin as [i [Hi Hk]].
        exists i.
        split; lia.
      * simpl in Hin.
        destruct Hin as [Hk | []].
        subst k.
        exists n.
        split; lia.
    + intros [i [Hi Hk]].
      simpl.
      apply in_or_app.
      assert (i < n \/ i = n) as [Hil | Hieq] by lia.
      * left.
        apply IH.
        exists i.
        split; lia.
      * right.
        subst i.
        simpl.
        left.
        symmetry.
        exact Hk.
Qed.

Lemma odd_range_no_dup :
  forall n, NoDup (odd_range n).
Proof.
  induction n as [|n IH].
  - constructor.
  - simpl.
    apply NoDup_app.
    + exact IH.
    + constructor.
      * intros H. inversion H.
      * constructor.
    + intros x Hin1 Hin2.
      simpl in Hin2.
      destruct Hin2 as [Hx | []].
      * subst x.
        apply odd_range_in_iff in Hin1.
        destruct Hin1 as [i [Hi Hx]].
        lia.
Qed.

Lemma odd_range_spec :
  forall n m,
    In m (odd_range n) <->
    1 <= m /\ m <= 2 * n /\ Nat.Odd m.
Proof.
  intros n m.
  split.
  - intros Hin.
    apply odd_range_in_iff in Hin.
    destruct Hin as [i [Hi Hm]].
    subst m.
    split.
    + lia.
    + split.
      * lia.
      * exists i. lia.
  - intros [Hm_pos [Hm_bound Hm_odd]].
    destruct Hm_odd as [i Hi].
    apply odd_range_in_iff.
    exists i.
    split.
    + rewrite Hi in Hm_bound. lia.
    + exact Hi.
Qed.

Lemma odd_part_in_range :
  forall n a,
    1 <= a ->
    a <= 2 * n ->
    In (odd_part a) (odd_range n).
Proof.
  intros n a Ha_pos Ha_bound.
  pose proof (odd_part_odd a Ha_pos) as Hodd.
  apply Nat.odd_spec in Hodd.
  apply odd_range_spec.
  split.
  - exact (odd_part_pos a Ha_pos).
  - split.
    + eapply Nat.le_trans.
      * apply odd_part_le.
      * exact Ha_bound.
    + exact Hodd.
Qed.

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                           PIGEONHOLE PRINCIPLE                          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

Lemma collision_from_tail_image :
  forall (A : Type) (f : A -> nat) (x : A) (xs : list A),
    ~ In x xs ->
    In (f x) (map f xs) ->
    exists y,
      In y xs /\
      y <> x /\
      f x = f y.
Proof.
  intros A f x xs Hnotin_x Hfx_in.
  apply in_map_iff in Hfx_in.
  destruct Hfx_in as [y [Hy_eq Hy_in]].
  exists y.
  split.
  - exact Hy_in.
  - split.
    + intro Hxy. subst y. apply Hnotin_x. exact Hy_in.
    + symmetry. exact Hy_eq.
Qed.

Lemma witness_from_head_collision :
  forall (A : Type) (f : A -> nat) (x : A) (xs : list A),
    ~ In x xs ->
    In (f x) (map f xs) ->
    exists a b,
      In a (x :: xs) /\
      In b (x :: xs) /\
      a <> b /\
      f a = f b.
Proof.
  intros A f x xs Hnotin_x Hin.
  destruct (collision_from_tail_image A f x xs Hnotin_x Hin)
    as [y [Hy_in [Hy_neq Hxy]]].
  exists x, y.
  split.
  - simpl. left. reflexivity.
  - split.
    + simpl. right. exact Hy_in.
    + split.
      * exact (not_eq_sym Hy_neq).
      * exact Hxy.
Qed.

Lemma remove_preserves_tail_categories :
  forall (A : Type) (f : A -> nat) (x : A) (xs : list A) (cats : list nat) (y : A),
    In y xs ->
    In (f y) cats ->
    ~ In (f x) (map f xs) ->
    In (f y) (remove Nat.eq_dec (f x) cats).
Proof.
  intros A f x xs cats y Hy_in Hy_cat Hnotin_fx.
  apply in_in_remove.
  - intro Heq.
    apply Hnotin_fx.
    rewrite <- Heq.
    apply in_map.
    exact Hy_in.
  - exact Hy_cat.
Qed.

Lemma remove_strictly_shorter :
  forall (cats : list nat) (c : nat),
    In c cats ->
    length (remove Nat.eq_dec c cats) < length cats.
Proof.
  intros cats c Hc.
  now apply remove_length_lt.
Qed.

Lemma tail_reduction_data :
  forall (A : Type) (f : A -> nat) (x : A) (xs : list A) (cats : list nat),
    (forall y, In y (x :: xs) -> In (f y) cats) ->
    ~ In (f x) (map f xs) ->
    length cats < S (length xs) ->
    (forall y, In y xs -> In (f y) (remove Nat.eq_dec (f x) cats)) /\
    length (remove Nat.eq_dec (f x) cats) < length xs.
Proof.
  intros A f x xs cats Hcat Hnotin Hlen.
  split.
  - intros y Hy.
    specialize (Hcat y (or_intror Hy)) as Hy_cat.
    exact (remove_preserves_tail_categories A f x xs cats y Hy Hy_cat Hnotin).
  - specialize (Hcat x (or_introl eq_refl)) as Hfx_cat.
    pose proof (remove_strictly_shorter cats (f x) Hfx_cat) as Hrm.
    lia.
Qed.

Lemma lift_witness_from_tail :
  forall (A : Type) (f : A -> nat) (x : A) (xs : list A),
    (exists a b,
      In a xs /\
      In b xs /\
      a <> b /\
      f a = f b) ->
    exists a b,
      In a (x :: xs) /\
      In b (x :: xs) /\
      a <> b /\
      f a = f b.
Proof.
  intros A f x xs [a [b [Ha [Hb [Hab Hf]]]]].
  exists a, b.
  split.
  - simpl. right. exact Ha.
  - split.
    + simpl. right. exact Hb.
    + split.
      * exact Hab.
      * exact Hf.
Qed.

Theorem pigeonhole :
  forall (A : Type) (f : A -> nat) (xs : list A) (cats : list nat),
    NoDup xs ->
    (forall x, In x xs -> In (f x) cats) ->
    length cats < length xs ->
    exists a b,
      In a xs /\
      In b xs /\
      a <> b /\
      f a = f b.
Proof.
  intros A f xs.
  induction xs as [|x xs IH]; intros cats Hnodup Hcat Hlen.
  - simpl in Hlen. lia.
  - apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as [Hnotin_x Hnodup_xs].
    destruct (in_dec Nat.eq_dec (f x) (map f xs)) as [Hx_collides | Hx_fresh].
    + exact (witness_from_head_collision A f x xs Hnotin_x Hx_collides).
    + destruct (tail_reduction_data A f x xs cats Hcat Hx_fresh) as
          [Hcat_xs Hlen_xs].
      * simpl in Hlen. exact Hlen.
      * apply lift_witness_from_tail.
        exact (IH (remove Nat.eq_dec (f x) cats) Hnodup_xs Hcat_xs Hlen_xs).
Qed.

(*
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                             FINAL DISCHARGE                             │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
*)

Theorem show_two_adic_factorization_holds :
  show_two_adic_factorization.
Proof.
  intros n x Hx_pos Hx_bound.
  pose proof (odd_part_odd x Hx_pos) as Hodd.
  apply Nat.odd_spec in Hodd.
  exists (val2 x), (odd_part x).
  split.
  - exact (decomposition x Hx_pos).
  - exact Hodd.
Qed.

Theorem show_odd_domain_exhaustion_holds :
  show_odd_domain_exhaustion.
Proof.
  intros n.
  exists (odd_range n).
  split.
  - exact (odd_range_no_dup n).
  - split.
    + exact (odd_range_length n).
    + intros m.
      exact (odd_range_spec n m).
Qed.

Theorem show_odd_core_collision_holds :
  show_odd_core_collision.
Proof.
  intros n A Hbounds Hnodup Hlen.
  destruct (pigeonhole nat odd_part A (odd_range n)) as
      [a [b [Ha [Hb [Hneq Heq]]]]].
  - exact Hnodup.
  - intros x Hx.
    destruct (Hbounds x Hx) as [Hx_pos Hx_bound].
    exact (odd_part_in_range n x Hx_pos Hx_bound).
  - rewrite odd_range_length.
    rewrite Hlen.
    lia.
  - destruct (Hbounds a Ha) as [Ha_pos Ha_bound].
    destruct (Hbounds b Hb) as [Hb_pos Hb_bound].
    pose proof (odd_part_odd a Ha_pos) as Hodd_a.
    apply Nat.odd_spec in Hodd_a.
    exists a, b, (odd_part a), (val2 a), (val2 b).
    split.
    + exact Ha.
    + split.
      * exact Hb.
      * split.
        -- exact Hneq.
        -- split.
           ++ exact (odd_part_pos a Ha_pos).
           ++ split.
              ** eapply Nat.le_trans.
                 --- apply odd_part_le.
                 --- exact Ha_bound.
              ** split.
                 --- exact Hodd_a.
                 --- split.
                     +++ exact (decomposition a Ha_pos).
                     +++ rewrite (decomposition b Hb_pos) at 1.
                         rewrite <- Heq.
                         reflexivity.
Qed.

Theorem show_common_odd_core_implies_divisibility_holds :
  show_common_odd_core_implies_divisibility.
Proof.
  intros n A y z m i j Hy Hz Hneq Hm_pos Hm_bound Hm_odd Hy_eq Hz_eq.
  exact (common_odd_core_implies_divisibility y z m i j Hy_eq Hz_eq).
Qed.

Theorem peeling_package_holds :
  peeling_package.
Proof.
  split.
  - exact show_two_adic_factorization_holds.
  - split.
    + exact show_odd_domain_exhaustion_holds.
    + split.
      * exact show_odd_core_collision_holds.
      * exact show_common_odd_core_implies_divisibility_holds.
Qed.

Theorem the_four_conjectures_hold :
  first_expansion.
Proof.
  intros n A Hselection.
  destruct Hselection as [Hbounds [Hnodup Hlen]].
  split.
  - intros x Hx_pos Hx_bound.
    exact (show_two_adic_factorization_holds n x Hx_pos Hx_bound).
  - split.
    + exact (show_odd_domain_exhaustion_holds n).
    + split.
      * exact (show_odd_core_collision_holds n A Hbounds Hnodup Hlen).
      * intros y z m i j Hy Hz Hneq Hm_pos Hm_bound Hm_odd Hy_eq Hz_eq.
        exact
          (show_common_odd_core_implies_divisibility_holds
             n A y z m i j
             Hy Hz Hneq Hm_pos Hm_bound Hm_odd Hy_eq Hz_eq).
Qed.

Theorem UNCONDITIONAL_PROOF : WITNESS.
Proof.
  apply first_expansion_implies_WITNESS.
  exact the_four_conjectures_hold.
Qed.
