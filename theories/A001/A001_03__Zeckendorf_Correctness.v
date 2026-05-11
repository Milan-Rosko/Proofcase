(*A001_03__Zeckendorf_Correctness.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                 Proofcase / A001_03__Zeckendorf_Correctness                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Greedy Zeckendorf correctness layer for A001. We establish that the
  concrete support extractor `Z0` produces valid supports whose Fibonacci sum
  is the original input, and that valid supports are canonical.

*)

From A001 Require Export A001_02__Base_Fibonacci.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        GREEDY ZECKENDORF CORRECTNESS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Fixpoint all_le (m : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => x <= m /\ all_le m xs'
  end.

Definition bound (k : nat) (prev_taken : bool) : nat :=
  if prev_taken then Nat.pred k else k.

Lemma all_le_weaken : forall m n xs,
  all_le m xs -> m <= n -> all_le n xs.
Proof.
  induction xs as [|x xs IH]; intros Hle Hmn; simpl in *; auto.
  destruct Hle as [Hx Hxs].
  split; [lia | exact (IH Hxs Hmn)].
Qed.

Lemma zeck_valid_cons_ge2 :
  forall m xs,
    zeck_valid xs ->
    all_le m xs ->
    zeck_valid (S (S m) :: xs).
Proof.
  intros m xs [Hdec [Hadj Hge]] Hall.
  split; [|split].
  - destruct xs as [|x xs']; simpl; auto.
    destruct Hall as [Hx Hall'].
    split; [lia | exact Hdec].
  - destruct xs as [|x xs']; simpl; auto.
    destruct Hall as [Hx Hall'].
    split; [lia | exact Hadj].
  - simpl. split; [lia | exact Hge].
Qed.

(*
│
│          `greedy_inv` states the correctness invariant for the
│          greedy descent: the support `xs` together with the leftover
│          `rem'` reconstructs `rem`; `xs` is a valid Zeckendorf
│          support bounded by the current admissible index; the base
│          case `k ≤ 1` forces `xs = []`; and the next-Fibonacci
│          threshold is preserved across the step.
│
*)

Definition greedy_inv k rem prev_taken xs rem' :=
  sum_fib xs + rem' = rem /\
  zeck_valid xs /\
  all_le (bound k prev_taken) xs /\
  (k <= 1 -> xs = [] /\ rem' = rem) /\
  (rem < fib (S (bound k prev_taken)) -> rem' < fib (S (bound k prev_taken))).

Lemma greedy_take_step_sum :
  forall k rem xs rem',
    fib k <= rem ->
    sum_fib xs + rem' = rem - fib k ->
    sum_fib (k :: xs) + rem' = rem.
Proof.
  intros k rem xs rem' Hle Hsum.
  simpl.
  rewrite <- Nat.add_assoc.
  rewrite Hsum.
  apply add_sub_cancel_r.
  exact Hle.
Qed.

(*
│
│          `zeck_greedy_down_correct_core` is the main recursive
│          correctness lemma. It shows that every branch of the greedy
│          descent yields a support/remainder pair satisfying the
│          invariant `greedy_inv`.
│
*)

(*                zeck_greedy_down(k, rem, prev) = (xs, rem')                 *)
(*                   ⇒ greedy_inv(k, rem, prev, xs, rem').                    *)

Lemma zeck_greedy_down_correct_core :
  forall k rem prev_taken xs rem',
    zeck_greedy_down k rem prev_taken = (xs, rem') ->
    greedy_inv k rem prev_taken xs rem'.
Proof.
  induction k as [|k IH]; intros rem prev xs rem' H.
  - simpl in H. inversion H; subst.
    assert (Hsum : sum_fib [] + rem' = rem') by (simpl; lia).
    assert (Hz : zeck_valid []) by (simpl; split; [exact I|]; split; exact I).
    assert (Hall : all_le (bound 0 prev) []) by (simpl; exact I).
    assert (Hlow : 0 <= 1 -> ([] : list nat) = [] /\ rem' = rem')
      by (intros _; split; reflexivity).
    assert (Hbd : rem' < fib (S (bound 0 prev)) -> rem' < fib (S (bound 0 prev)))
      by (intro Hrem; exact Hrem).
    exact (conj Hsum (conj Hz (conj Hall (conj Hlow Hbd)))).
  - destruct k as [|k']; simpl in H.
    + simpl in H.
      inversion H; subst.
      assert (Hsum : sum_fib [] + rem' = rem') by (simpl; lia).
      assert (Hz : zeck_valid []) by (simpl; split; [exact I|]; split; exact I).
      assert (Hall : all_le (bound 1 prev) []) by (simpl; exact I).
      assert (Hlow : 1 <= 1 -> ([] : list nat) = [] /\ rem' = rem')
        by (intros _; split; reflexivity).
      assert (Hbd : rem' < fib (S (bound 1 prev)) -> rem' < fib (S (bound 1 prev)))
        by (intro Hrem; exact Hrem).
      exact (conj Hsum (conj Hz (conj Hall (conj Hlow Hbd)))).
    + destruct prev eqn:Hprev.
      * specialize (IH rem false xs rem' H) as [Hsum [Hz [Hall [Hlow Hbd]]]].
        refine (conj Hsum (conj Hz (conj _ (conj _ _))));
          [simpl; exact Hall | intros Hk; lia | intros Hrem; lia].
      * destruct (Nat.leb (fib (S (S k'))) rem) eqn:Hle.
        -- destruct (zeck_greedy_down (S k') (rem - fib (S (S k'))) true)
             as [xs' rem''] eqn:Hpr.
           change
             ((S (S k')
               :: fst (zeck_greedy_down (S k') (rem - fib (S (S k'))) true),
               snd (zeck_greedy_down (S k') (rem - fib (S (S k'))) true))
              = (xs, rem')) in H.
           rewrite Hpr in H.
           inversion H; subst xs rem'. clear H.
           specialize (IH (rem - fib (S (S k'))) true xs' rem'' Hpr)
             as [Hsum [Hz [Hall [Hlow Hbd]]]].
           refine (conj _ (conj _ (conj _ (conj _ _))));
             [ apply Nat.leb_le in Hle;
               eapply greedy_take_step_sum; [exact Hle | exact Hsum]
             | simpl in Hall; apply (zeck_valid_cons_ge2 k' xs'); assumption
             | simpl; split; [lia|]; apply all_le_weaken with (m:=k'); [exact Hall| lia]
             | intros Hk; lia
             | intros Hrem;
               apply Nat.leb_le in Hle;
               simpl in Hrem;
               assert (Hinner : rem - fib (S (S k')) < fib (S k')) by
                 (rewrite fib_step in Hrem; lia);
               assert (Hrem'' : rem'' < fib (S k')) by (apply Hbd; exact Hinner);
               apply Nat.lt_le_trans with (m:=fib (S k')); [exact Hrem''|];
               simpl; apply fib_monotone_le; lia ].
        -- specialize (IH rem false xs rem' H) as [Hsum [Hz [Hall [Hlow Hbd]]]].
           refine (conj Hsum (conj Hz (conj _ (conj _ _))));
             [ simpl; apply all_le_weaken with (m:=S k'); [exact Hall| lia]
             | intros Hk; lia
             | intros Hrem;
               apply Nat.leb_gt in Hle;
               assert (Hinner : rem < fib (S (S k'))) by lia;
               assert (Hrem' : rem' < fib (S (S k'))) by (apply Hbd; exact Hinner);
               apply Nat.lt_le_trans with (m:=fib (S (S k'))); [exact Hrem'|];
               simpl; apply fib_monotone_le; lia ].
Qed.

Lemma zeck_greedy_down_inv_k0 :
  forall rem prev,
    greedy_inv 0 rem prev
      (fst (zeck_greedy_down 0 rem prev))
      (snd (zeck_greedy_down 0 rem prev)).
Proof.
  intros rem prev.
  apply zeck_greedy_down_correct_core.
  reflexivity.
Qed.

Lemma zeck_greedy_down_inv_k1 :
  forall rem prev,
    greedy_inv 1 rem prev
      (fst (zeck_greedy_down 1 rem prev))
      (snd (zeck_greedy_down 1 rem prev)).
Proof.
  intros rem prev.
  apply zeck_greedy_down_correct_core.
  reflexivity.
Qed.

Lemma zeck_greedy_down_inv_skip_prev :
  forall k rem xs rem',
    zeck_greedy_down (S (S k)) rem true = (xs, rem') ->
    greedy_inv (S (S k)) rem true xs rem'.
Proof.
  intros k rem xs rem' H.
  apply zeck_greedy_down_correct_core.
  exact H.
Qed.

Lemma zeck_greedy_down_inv_skip_lt :
  forall k rem xs rem',
    fib (S (S k)) > rem ->
    zeck_greedy_down (S (S k)) rem false = (xs, rem') ->
    greedy_inv (S (S k)) rem false xs rem'.
Proof.
  intros k rem xs rem' _ H.
  apply zeck_greedy_down_correct_core.
  exact H.
Qed.

Lemma zeck_greedy_down_inv_take :
  forall k rem xs rem',
    fib (S (S k)) <= rem ->
    zeck_greedy_down (S (S k)) rem false = (xs, rem') ->
    greedy_inv (S (S k)) rem false xs rem'.
Proof.
  intros k rem xs rem' _ H.
  apply zeck_greedy_down_correct_core.
  exact H.
Qed.

(*
│
│          `zeck_greedy_down_correct` presents the greedy-descent
│          correctness theorem in the direct form used to derive the
│          Zeckendorf support results.
│
*)

Theorem zeck_greedy_down_correct :
  forall k rem prev xs rem',
    zeck_greedy_down k rem prev = (xs, rem') ->
    greedy_inv k rem prev xs rem'.
Proof.
  intros k rem prev xs rem' H.
  destruct k as [|k'].
  - apply zeck_greedy_down_correct_core. exact H.
  - destruct k' as [|k''].
    + apply zeck_greedy_down_correct_core. exact H.
    + destruct prev.
      * apply zeck_greedy_down_inv_skip_prev. exact H.
      * destruct (Nat.leb (fib (S (S k''))) rem) eqn:Hleb.
        -- apply zeck_greedy_down_inv_take.
           ++ apply Nat.leb_le. exact Hleb.
           ++ exact H.
        -- apply zeck_greedy_down_inv_skip_lt.
           ++ apply Nat.leb_gt. exact Hleb.
           ++ exact H.
Qed.

(*
│
│          Specializing the greedy invariant at the cutoff `r0(n)`
│          shows that the residual remainder already lies strictly
│          below the next admissible Fibonacci threshold.
│
*)

Lemma greedy_top_bound :
  forall n xs rem',
    zeck_greedy_down (r0 n) n false = (xs, rem') ->
    rem' < fib (S (r0 n)).
Proof.
  intros n xs rem' H.
  pose proof (zeck_greedy_down_correct (r0 n) n false xs rem' H)
    as [_ [_ [_ [_ Hbd]]]].
  simpl in Hbd.
  apply Hbd.
  apply r0_upper_S.
Qed.

(*
│
│          Whenever the greedy support begins with index `S(S(k))`,
│          the Fibonacci sum of its prefix remains strictly below the
│          next Fibonacci value.
│
*)

Lemma sum_fib_prefix_lt_next :
  forall k rem xs rem',
    greedy_inv (S (S k)) rem false (S (S k) :: xs) rem' ->
    rem < fib (S (S (S k))) ->
    sum_fib (S (S k) :: xs) < fib (S (S (S k))).
Proof.
  intros k rem xs rem' Hinv Hrem.
  destruct Hinv as [Hsum [_ [_ [_ _]]]].
  assert (sum_fib (S (S k) :: xs) <= rem) by lia.
  lia.
Qed.

Lemma rem_lt_1_is_0 : forall r, r < 1 -> r = 0.
Proof.
  intros r Hr. lia.
Qed.

Lemma bound_k1_le_1 : forall prev, bound 1 prev <= 1.
Proof.
  intro prev. destruct prev; simpl; lia.
Qed.

Lemma fib_2_eq_1 : fib 2 = 1.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma fib_1_eq_1 : fib 1 = 1.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma rem_lt_1_from_inv_k1 :
  forall rem prev xs rem',
    zeck_greedy_down 1 rem prev = (xs, rem') ->
    greedy_inv 1 rem prev xs rem' ->
    rem < fib (S (bound 1 prev)) ->
    rem' < 1.
Proof.
  intros rem prev xs rem' Hcall Hinv Hpre.
  destruct Hinv as [_ [_ [_ [_ Hbd]]]].
  specialize (Hbd Hpre).
  destruct prev.
  - simpl in Hbd. rewrite fib_1_eq_1 in Hbd. lia.
  - simpl in Hbd. rewrite fib_2_eq_1 in Hbd. lia.
Qed.

Lemma greedy_rem_lt_1_false :
  forall k rem xs rem',
    rem < fib (S k) ->
    zeck_greedy_down k rem false = (xs, rem') ->
    rem' < 1.
Proof.
  refine (well_founded_induction
            lt_wf
            (fun k =>
               forall rem xs rem',
                 rem < fib (S k) ->
                 zeck_greedy_down k rem false = (xs, rem') ->
                 rem' < 1) _).
  intros k IH rem xs rem' Hbound Hcall.
  destruct k as [|k1].
  - simpl in Hcall. inversion Hcall; subst. exact Hbound.
  - destruct k1 as [|k2].
    + simpl in Hcall. inversion Hcall; subst.
      rewrite fib_2_eq_1 in Hbound. exact Hbound.
    + simpl in Hcall.
      destruct (Nat.leb (fib (S (S k2))) rem) eqn:Hle.
      * destruct (zeck_greedy_down (S k2) (rem - fib (S (S k2))) true)
          as [xs1 rem1] eqn:Hrec.
        change
          ((S (S k2)
            :: fst (zeck_greedy_down (S k2) (rem - fib (S (S k2))) true),
            snd (zeck_greedy_down (S k2) (rem - fib (S (S k2))) true))
           = (xs, rem')) in Hcall.
        rewrite Hrec in Hcall.
        inversion Hcall; subst xs rem'. clear Hcall.
        apply Nat.leb_le in Hle.
        assert (Hrem1 : rem - fib (S (S k2)) < fib (S k2)).
        -- rewrite fib_step in Hbound. lia.
        -- destruct k2 as [|k3].
           ++ simpl in Hrec. inversion Hrec; subst.
              rewrite fib_1_eq_1 in Hrem1. exact Hrem1.
           ++ simpl in Hrec.
              pose proof (IH (S k3) ltac:(lia)) as IHk.
              exact (IHk (rem - fib (S (S (S k3)))) xs1 rem1 Hrem1 Hrec).
      * apply Nat.leb_gt in Hle.
        pose proof (IH (S k2) ltac:(lia)) as IHk.
        exact (IHk rem xs rem' Hle Hcall).
Qed.

Lemma Z0_rem_lt_1 :
  forall n xs rem',
    zeck_greedy_down (r0 n) n false = (xs, rem') ->
    rem' < 1.
Proof.
  intros n xs rem' H.
  eapply greedy_rem_lt_1_false; eauto.
  apply r0_upper_S.
Qed.

(*
│
│          `Z0_sound` is the basic adequacy theorem for the concrete
│          support extractor: evaluating the greedy support through
│          `sum_fib` recovers the original number.
│
*)

(*                            ∀ n, Σ_F(Z0(n)) = n.                            *)

Theorem Z0_sound : forall n, sum_fib (Z0 n) = n.
Proof.
  intro n.
  unfold Z0.
  destruct (zeck_greedy_down (r0 n) n false) as [xs rem'] eqn:Hgd.
  pose proof (zeck_greedy_down_correct (r0 n) n false xs rem' Hgd)
    as [Hsum _].
  assert (Hrem1 : rem' < 1) by (eapply Z0_rem_lt_1; exact Hgd).
  assert (Hrem0 : rem' = 0) by (apply rem_lt_1_is_0; exact Hrem1).
  rewrite Hrem0 in Hsum.
  rewrite Nat.add_0_r in Hsum.
  exact Hsum.
Qed.

(*
│
│          `Z0_valid` complements `Z0_sound`: the extractor produces a
│          canonical admissible support, not merely one whose sum is
│          correct.
│
*)

(*                          ∀ n, zeck_valid(Z0(n)).                           *)

Theorem Z0_valid : forall n, zeck_valid (Z0 n).
Proof.
  intro n.
  unfold Z0.
  destruct (zeck_greedy_down (r0 n) n false) as [xs rem'] eqn:Hgd.
  pose proof (zeck_greedy_down_correct (r0 n) n false xs rem' Hgd)
    as [_ [Hvalid _]].
  exact Hvalid.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              SUPPORT UNIQUENESS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Lemma sum_fib_ge_head :
  forall k xs, sum_fib (k :: xs) >= fib k.
Proof.
  intros k xs. simpl. lia.
Qed.

Lemma zeck_valid_tail :
  forall k xs,
    zeck_valid (k :: xs) ->
    zeck_valid xs.
Proof.
  intros k xs [Hdec [Hadj Hge]].
  destruct xs as [|a xs'].
  - simpl. split; [trivial|]. split; trivial.
  - simpl in Hdec, Hadj, Hge.
    destruct Hdec as [_ Hdec'].
    destruct Hadj as [_ Hadj'].
    destruct Hge as [_ Hge'].
    split; [exact Hdec'|]. split; assumption.
Qed.

Lemma zeck_valid_head_ge_2 :
  forall k xs,
    zeck_valid (k :: xs) ->
    2 <= k.
Proof.
  intros k xs [_ [_ Hge]].
  simpl in Hge.
  tauto.
Qed.

Lemma fib_le_of_le : forall a b, a <= b -> fib a <= fib b.
Proof.
  intros a b Hle.
  destruct (Nat.eq_dec a b) as [Heq|Hneq].
  - subst. apply Nat.le_refl.
  - apply fib_monotone_le. lia.
Qed.

Lemma fib_lt_succ_of_ge2 : forall k, 2 <= k -> fib k < fib (S k).
Proof.
  intros k Hk.
  destruct k as [|[|k']]; try lia.
  replace (fib (S (S (S k')))) with (fib (S (S k')) + fib (S k')) by
      (symmetry; apply fib_step).
  assert (Hpos : fib (S k') >= 1) by apply fib_pos_S.
  lia.
Qed.

Lemma fib_step_pred : forall k, 1 <= k -> fib (S k) = fib k + fib (Nat.pred k).
Proof.
  intros k Hk.
  destruct k as [|k']; [lia|].
  destruct k' as [|k''].
  - vm_compute. reflexivity.
  - simpl. apply fib_step.
Qed.

Lemma sum_fib_lt_next_of_valid :
  forall k xs,
    zeck_valid (k :: xs) ->
    sum_fib (k :: xs) < fib (S k).
Proof.
  intros k xs Hvalid.
  revert k Hvalid.
  induction xs as [|x xs' IH]; intros k Hvalid; simpl.
  - apply zeck_valid_head_ge_2 in Hvalid.
    rewrite Nat.add_0_r.
    apply fib_lt_succ_of_ge2.
    exact Hvalid.
  - pose proof (zeck_valid_tail k (x :: xs') Hvalid) as Htail_valid.
    pose proof (IH x Htail_valid) as Htail.
    destruct Hvalid as [_ [Hadj _]].
    simpl in Hadj.
    destruct Hadj as [Hgap _].
    assert (Hsx : S x <= Nat.pred k) by lia.
    assert (Hsx_le : fib (S x) <= fib (Nat.pred k)).
    + apply fib_le_of_le. exact Hsx.
    + assert (Hk1 : 1 <= k) by lia.
      assert (Hstep : fib (S k) = fib k + fib (Nat.pred k)).
      * apply fib_step_pred. exact Hk1.
      * rewrite Hstep.
        assert (Hlt_pred : fib x + sum_fib xs' < fib (Nat.pred k)).
        -- eapply Nat.lt_le_trans; [exact Htail | exact Hsx_le].
        -- lia.
Qed.

Lemma sum_fib_cons_pos_valid :
  forall k xs,
    zeck_valid (k :: xs) ->
    0 < sum_fib (k :: xs).
Proof.
  intros k xs Hvalid.
  simpl.
  assert (Hk2 : 2 <= k) by (apply zeck_valid_head_ge_2 with (xs:=xs); exact Hvalid).
  assert (Hf : fib k >= 1) by (apply fib_pos; lia).
  lia.
Qed.

Lemma fib_succ_le_of_lt_ge2 :
  forall a b,
    2 <= a ->
    a < b ->
    fib (S a) <= fib b.
Proof.
  intros a b Ha Hlt.
  destruct (Nat.eq_dec (S a) b) as [Heq|Hneq].
  - subst. apply Nat.le_refl.
  - apply fib_monotone_le. lia.
Qed.

(*
│
│          `Zeckendorf_unique_core` is the canonicality theorem for
│          valid supports: equality of Fibonacci sums forces equality
│          of the supports themselves.
│
*)

(*            zeck_valid(xs) ∧ zeck_valid(ys) ∧ Σ_F(xs) = Σ_F(ys)             *)
(*                                 ⇒ xs = ys.                                 *)

Lemma Zeckendorf_unique_core :
  forall xs ys,
    zeck_valid xs ->
    zeck_valid ys ->
    sum_fib xs = sum_fib ys ->
    xs = ys.
Proof.
  induction xs as [|k xs IH]; intros ys Hx Hy Heq.
  - destruct ys as [|l ys].
    + reflexivity.
    + exfalso.
      pose proof (sum_fib_cons_pos_valid l ys Hy) as Hpos.
      rewrite <- Heq in Hpos. simpl in Hpos. lia.
  - destruct ys as [|l ys].
    + exfalso.
      pose proof (sum_fib_cons_pos_valid k xs Hx) as Hpos.
      rewrite Heq in Hpos. simpl in Hpos. lia.
    + assert (Hk : k = l).
      * destruct (Nat.lt_ge_cases k l) as [Hkl|Hkge].
        -- pose proof (sum_fib_lt_next_of_valid k xs Hx) as Hup.
           pose proof (sum_fib_ge_head l ys) as Hlow.
           rewrite Heq in Hup.
           assert (Hf : fib (S k) <= fib l).
           ++ apply fib_succ_le_of_lt_ge2.
              ** apply zeck_valid_head_ge_2 with (xs:=xs). exact Hx.
              ** exact Hkl.
           ++ lia.
        -- destruct (Nat.lt_ge_cases l k) as [Hlk|Hlge].
           ++ pose proof (sum_fib_lt_next_of_valid l ys Hy) as Hup.
              pose proof (sum_fib_ge_head k xs) as Hlow.
              rewrite <- Heq in Hup.
              assert (Hf : fib (S l) <= fib k).
              ** apply fib_succ_le_of_lt_ge2.
                 --- apply zeck_valid_head_ge_2 with (xs:=ys). exact Hy.
                 --- exact Hlk.
              ** lia.
           ++ lia.
      * subst l.
        apply f_equal.
        apply IH.
        -- apply zeck_valid_tail with (k:=k). exact Hx.
        -- apply zeck_valid_tail with (k:=k). exact Hy.
        -- simpl in Heq. lia.
Qed.

(*
│
│          `Z0_of_sum_fib` is the converse of `Z0_sound`: every valid
│          support is a fixed point of the extractor.
│
*)

(*                     zeck_valid(xs) ⇒ Z0(Σ_F(xs)) = xs.                     *)

Theorem Z0_of_sum_fib :
  forall xs, zeck_valid xs -> Z0 (sum_fib xs) = xs.
Proof.
  intros xs Hvalid.
  apply Zeckendorf_unique_core.
  - apply Z0_valid.
  - exact Hvalid.
  - apply Z0_sound.
Qed.

(*
│
│          Admissible Fibonacci supports are canonical: among valid
│          supports, equality of the evaluated sums entails equality
│          of the supports.
│
*)

Theorem Zeckendorf_unique :
  forall xs ys,
    zeck_valid xs ->
    zeck_valid ys ->
    sum_fib xs = sum_fib ys ->
    xs = ys.
Proof.
  intros xs ys Hx Hy Heq.
  rewrite <- (Z0_of_sum_fib xs Hx).
  rewrite <- (Z0_of_sum_fib ys Hy).
  f_equal.
  exact Heq.
Qed.

Lemma sum_fib_app : forall xs ys, sum_fib (xs ++ ys) = sum_fib xs + sum_fib ys.
Proof.
  induction xs as [|a xs IH]; intro ys; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma all_ge_2_in :
  forall xs k, all_ge_2 xs -> In k xs -> 2 <= k.
Proof.
  induction xs as [|a xs IH]; intros k Hge Hin; simpl in *.
  - contradiction.
  - destruct Hge as [Ha Hxs].
    destruct Hin as [<-|Hin].
    + exact Ha.
    + apply (IH k Hxs Hin).
Qed.

Lemma all_le_in :
  forall m xs k, all_le m xs -> In k xs -> k <= m.
Proof.
  induction xs as [|a xs IH]; intros k Hle Hin; simpl in *.
  - contradiction.
  - destruct Hle as [Ha Hxs].
    destruct Hin as [<-|Hin].
    + exact Ha.
    + apply (IH k Hxs Hin).
Qed.

Lemma sum_fib_in_ge :
  forall xs k, In k xs -> fib k <= sum_fib xs.
Proof.
  induction xs as [|a xs IH]; intros k Hin; simpl in *.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + lia.
    + specialize (IH k Hin). lia.
Qed.

(*
│
│          Every index produced by the concrete extractor lies
│          strictly below the cutoff `r0(x)`, so that the recovered
│          support never reaches the boundary-defining index itself.
│
*)

Lemma Z0_indices_below_r0 :
  forall x e,
    In e (Z0 x) ->
    e < r0 x.
Proof.
  intros x e Hin.
  unfold Z0 in Hin.
  destruct (zeck_greedy_down (r0 x) x false) as [xs rem'] eqn:Hgd.
  simpl in Hin.
  pose proof (zeck_greedy_down_correct (r0 x) x false xs rem' Hgd)
    as [Hsum [_ [Hall _]]].
  assert (Hele : e <= r0 x).
  - apply (all_le_in (r0 x) xs e Hall Hin).
  - destruct (Nat.eq_dec e (r0 x)) as [Heq|Hneq].
    + subst e.
      assert (Hf_le : fib (r0 x) <= sum_fib xs).
      * apply sum_fib_in_ge. exact Hin.
      * assert (Hf_le_x : fib (r0 x) <= x) by lia.
        pose proof (r0_upper x) as Hru.
        lia.
    + lia.
Qed.
