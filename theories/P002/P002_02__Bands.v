(*P002_02__Bands.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                          Proofcase / P002_02__Bands                          │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This layer specializes the FM digit constraints to fixed machine windows.

  Only the pieces that matter for `compile_fm_family_correct` are kept
  central here: band-local booleanity, band-local non-adjacency, and the
  weighted linear decoder that turns a valid digit window into the
  corresponding `band_code`.

*)

From P002 Require Export P002_01__Architecture.

Definition band_digit_indices (offset K : nat) : list nat :=
  seq (offset + 2) (K - 2).

Definition band_adjacency_indices (offset K : nat) : list nat :=
  seq (offset + 2) (K - 3).

Definition emit_band_boolean_constraints (offset K : nat) : list h10_nd3n_equation :=
  map emit_boolean_constraint (band_digit_indices offset K).

Definition emit_band_non_adjacency_constraints (offset K : nat)
  : list h10_nd3n_equation :=
  map
    (fun k => emit_non_adjacency_constraint k (S k))
    (band_adjacency_indices offset K).

(*
│
│          The boolean and non-adjacency emitters are equation-valued
│          because later compilation needs honest local constraints,
│          not raw term payloads.
│
*)

Definition emit_band_decoder (_target_var offset K : nat) : list term :=
  map (fun k => {| coeff := fib k; mono := m_linear k |}) (band_digit_indices offset K).

Definition band_decoder_equation (target_var offset K : nat) : h10_nd3n_equation :=
  {|
    var_count := S (Nat.max target_var (offset + K));
    lhs_terms := [{| coeff := 1; mono := m_linear target_var |}];
    rhs_terms := emit_band_decoder target_var offset K
  |}.

Definition indicator_valuation (xs : list nat) : valuation :=
  fun n => if in_dec Nat.eq_dec n xs then 1 else 0.

Definition band_decoder_valuation (target_var offset x : nat) : valuation :=
  fun n =>
    if Nat.eqb n target_var
    then band_code offset x
    else indicator_valuation (band_support offset x) n.

Definition mem_nat (xs : list nat) (n : nat) : bool :=
  if in_dec Nat.eq_dec n xs then true else false.

Lemma mem_nat_true_iff :
  forall xs n,
    mem_nat xs n = true <-> In n xs.
Proof.
  intros xs n.
  unfold mem_nat.
  destruct (in_dec Nat.eq_dec n xs) as [Hin|Hnin].
  - split; intro H.
    + exact Hin.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + contradiction.
Qed.

Lemma NoDup_filter :
  forall (A : Type) (f : A -> bool) (xs : list A),
    NoDup xs ->
    NoDup (filter f xs).
Proof.
  intros A f xs Hnodup.
  induction Hnodup as [|x xs Hnotin Hnodup IH]; simpl.
  - constructor.
  - destruct (f x) eqn:Hx.
    + constructor.
      * intro Hin.
        apply filter_In in Hin as [Hin _].
        contradiction.
      * exact IH.
    + exact IH.
Qed.

Lemma strictly_decreasing_head_gt_all :
  forall a xs y,
    strictly_decreasing (a :: xs) ->
    In y xs ->
    a > y.
Proof.
  intros a xs.
  revert a.
  induction xs as [|b xs IH]; intros a y Hdec Hin.
  - contradiction.
  - simpl in Hdec.
    destruct Hdec as [Hab Htail].
    simpl in Hin.
    destruct Hin as [->|Hin].
    + exact Hab.
    + specialize (IH b y Htail Hin).
      lia.
Qed.

Lemma strictly_decreasing_NoDup :
  forall xs,
    strictly_decreasing xs ->
    NoDup xs.
Proof.
  induction xs as [|a xs IH]; intros Hdec.
  - constructor.
  - destruct xs as [|b xs'].
    + constructor; [intro Hin; contradiction|constructor].
    + simpl in Hdec.
      destruct Hdec as [Hab Htail].
      assert (Hfull : strictly_decreasing (a :: b :: xs')).
      { simpl. split; assumption. }
      constructor.
      * intro Hin.
        eapply Nat.lt_irrefl.
        eapply strictly_decreasing_head_gt_all.
        -- exact Hfull.
        -- exact Hin.
      * apply IH.
        exact Htail.
Qed.

Lemma no_adjacent_head_ge_all :
  forall a xs y,
    no_adjacent (a :: xs) ->
    In y xs ->
    a >= y + 2.
Proof.
  intros a xs.
  revert a.
  induction xs as [|b xs IH]; intros a y Hadj Hin.
  - contradiction.
  - simpl in Hadj.
    destruct Hadj as [Hab Htail].
    simpl in Hin.
    destruct Hin as [->|Hin].
    + exact Hab.
    + specialize (IH b y Htail Hin).
      lia.
Qed.

Lemma sum_fib_perm :
  forall xs ys,
    Permutation xs ys ->
    sum_fib xs = sum_fib ys.
Proof.
  intros xs ys Hperm.
  induction Hperm.
  - reflexivity.
  - simpl.
    rewrite IHHperm.
    reflexivity.
  - simpl.
    lia.
  - rewrite IHHperm1, IHHperm2.
    reflexivity.
Qed.

Lemma eval_poly_fib_linears_indicator :
  forall ks xs,
    eval_poly
      (map (fun k => {| coeff := fib k; mono := m_linear k |}) ks)
      (indicator_valuation xs) =
    sum_fib (filter (mem_nat xs) ks).
Proof.
  induction ks as [|k ks IH]; intros xs; simpl.
  - reflexivity.
  - unfold indicator_valuation at 1.
    unfold mem_nat.
    destruct (in_dec Nat.eq_dec k xs) as [Hin|Hnin].
    + assert (Hone : (if in_dec Nat.eq_dec k xs then 1 else 0) = 1).
      { destruct (in_dec Nat.eq_dec k xs); [reflexivity|contradiction]. }
      unfold eval_term.
      simpl.
      rewrite Hone, IH.
      rewrite Nat.mul_1_r.
      reflexivity.
    + assert (Hzero : (if in_dec Nat.eq_dec k xs then 1 else 0) = 0).
      { destruct (in_dec Nat.eq_dec k xs); [contradiction|reflexivity]. }
      unfold eval_term.
      simpl.
      rewrite Hzero, IH.
      rewrite Nat.mul_0_r.
      reflexivity.
Qed.

Lemma eval_poly_fib_linears_ext :
  forall ks rho rho',
    (forall k, In k ks -> rho k = rho' k) ->
    eval_poly
      (map (fun k => {| coeff := fib k; mono := m_linear k |}) ks) rho =
    eval_poly
      (map (fun k => {| coeff := fib k; mono := m_linear k |}) ks) rho'.
Proof.
  induction ks as [|k ks IH]; intros rho rho' Hext; simpl.
  - reflexivity.
  - unfold eval_term.
    simpl.
    rewrite Hext by (left; reflexivity).
    f_equal.
    apply IH.
    intros i Hi.
    apply Hext.
    right.
    exact Hi.
Qed.

Lemma band_digit_indices_bounds :
  forall offset K k,
    In k (band_digit_indices offset K) ->
    offset + 2 <= k /\ k < offset + K.
Proof.
  intros offset K k Hin.
  unfold band_digit_indices in Hin.
  apply in_seq in Hin.
  lia.
Qed.

Lemma filter_band_digit_indices_perm_support :
  forall offset K xs,
    NoDup xs ->
    (forall k, In k xs -> offset + 2 <= k /\ k < offset + K) ->
    Permutation (filter (mem_nat xs) (band_digit_indices offset K)) xs.
Proof.
  intros offset K xs Hnodup Hbounds.
  apply NoDup_Permutation.
  - apply NoDup_filter.
    unfold band_digit_indices.
    apply seq_NoDup.
  - exact Hnodup.
  - intro k.
    split; intro Hin.
    + apply filter_In in Hin as [_ Hmem].
      apply mem_nat_true_iff.
      exact Hmem.
    + apply filter_In.
      split.
      * unfold band_digit_indices.
        apply in_seq.
        specialize (Hbounds k Hin).
        lia.
      * apply mem_nat_true_iff.
        exact Hin.
Qed.

Lemma zeck_valid_not_both_adjacent :
  forall xs k,
    zeck_valid xs ->
    In k xs ->
    ~ In (S k) xs.
Proof.
  intros xs k Hvalid Hin.
  revert k Hin Hvalid.
  induction xs as [|a xs IH]; intros k Hin Hvalid; simpl in *.
  - contradiction.
  - destruct Hin as [Hk|Hin].
    + subst k.
      intro Hsucc.
      destruct Hvalid as [Hdec [_ _]].
      destruct Hsucc as [Heq|Hsucc]; [lia|].
      assert (Hgt : a > S a)
        by (eapply strictly_decreasing_head_gt_all; [exact Hdec | exact Hsucc]).
      eapply Nat.lt_irrefl.
      eapply Nat.lt_trans.
      1: apply Nat.lt_succ_diag_r.
      exact Hgt.
    + intro Hsucc.
      destruct Hvalid as [Hdec [Hadj Hge]].
      destruct Hsucc as [Heq|Hsucc].
      * assert (Hgap : a >= k + 2)
          by (eapply no_adjacent_head_ge_all; [exact Hadj | exact Hin]).
        lia.
      * eapply IH.
        -- exact Hin.
        -- apply zeck_valid_tail with (k := a).
           split.
           ++ exact Hdec.
           ++ split.
              ** exact Hadj.
              ** exact Hge.
        -- exact Hsucc.
Qed.

Lemma band_support_no_adjacent :
  forall offset x k,
    In k (band_support offset x) ->
    ~ In (S k) (band_support offset x).
Proof.
  intros offset x k Hin Hsucc.
  unfold band_support in Hin, Hsucc.
  apply in_map_iff in Hin.
  apply in_map_iff in Hsucc.
  destruct Hin as [a [Ha Hina]].
  destruct Hsucc as [b [Hb Hinb]].
  subst.
  assert (Hb' : b = S a) by lia.
  subst b.
  eapply zeck_valid_not_both_adjacent.
  - apply Z0_valid.
  - exact Hina.
  - exact Hinb.
Qed.

Lemma indicator_valuation_boolean :
  forall xs k,
    indicator_valuation xs k = 0 \/ indicator_valuation xs k = 1.
Proof.
  intros xs k.
  unfold indicator_valuation.
  destruct (in_dec Nat.eq_dec k xs); [right | left]; reflexivity.
Qed.

Lemma band_support_solves_boolean_constraint :
  forall offset x k,
    solves
      (emit_boolean_constraint k)
      (indicator_valuation (band_support offset x)).
Proof.
  intros offset x k.
  apply boolean_constraint_correct.
  apply indicator_valuation_boolean.
Qed.

Lemma band_support_solves_non_adjacency_constraint :
  forall offset x k,
    solves
      (emit_non_adjacency_constraint k (S k))
      (indicator_valuation (band_support offset x)).
Proof.
  intros offset x k.
  apply non_adjacency_correct.
  unfold indicator_valuation.
  destruct (in_dec Nat.eq_dec k (band_support offset x)) as [Hin|Hnin].
  - right.
    destruct (in_dec Nat.eq_dec (S k) (band_support offset x)) as [Hsucc|Hsucc].
    + exfalso.
      eapply (band_support_no_adjacent offset x k Hin).
      exact Hsucc.
    + reflexivity.
  - left.
    reflexivity.
Qed.

(*
│
│          The canonical indicator valuation attached to a band
│          support solves every emitted digit equation for that band.
│          This is the local correctness fact that the later compiler
│          will need when it instantiates digit witnesses coming from
│          a concrete FM run.
│
*)

Lemma emit_band_decoder_indicator :
  forall target_var offset K x,
    x < fib K ->
    eval_poly
      (emit_band_decoder target_var offset K)
      (indicator_valuation (band_support offset x)) =
    band_code offset x.
Proof.
  intros target_var offset K x Hx.
  unfold emit_band_decoder, band_code.
  rewrite eval_poly_fib_linears_indicator.
  apply sum_fib_perm.
  apply filter_band_digit_indices_perm_support.
  - apply strictly_decreasing_NoDup.
    destruct (band_support_valid offset x) as [Hdec [_ _]].
    exact Hdec.
  - intros k Hin.
    eapply band_support_window; eauto.
Qed.

Lemma band_decoder_valuation_on_window :
  forall target_var offset K x k,
    (target_var < offset + 2 \/ offset + K <= target_var) ->
    In k (band_digit_indices offset K) ->
    band_decoder_valuation target_var offset x k =
    indicator_valuation (band_support offset x) k.
Proof.
  intros target_var offset K x k Hsep Hk.
  unfold band_decoder_valuation.
  destruct (Nat.eqb_spec k target_var) as [Heq|Hneq].
  - destruct Hsep as [Hleft|Hright].
    + apply band_digit_indices_bounds in Hk.
      lia.
    + apply band_digit_indices_bounds in Hk.
      lia.
  - reflexivity.
Qed.

(*
│
│          Once the target variable is kept outside the active digit
│          window, the auxiliary valuation agrees pointwise with the
│          pure indicator valuation on every emitted digit index. This
│          is the separation fact that lets the decoder equation reuse
│          the support semantics without accidental self-interference
│          through the target channel.
│
*)
(*     target\_var \notin [offset+2,\,offset+K) \Rightarrow \forall k \in     *)
(*                      band\_digit\_indices(offset,K),                       *)
(*band\_decoder\_valuation(target\_var,offset,x)(k)=indicator\_valuation(band\_support(offset,x))(k).*)

Lemma eval_poly_emit_band_decoder_with_band_valuation :
  forall target_var offset K x,
    (target_var < offset + 2 \/ offset + K <= target_var) ->
    eval_poly
      (emit_band_decoder target_var offset K)
      (band_decoder_valuation target_var offset x) =
    eval_poly
      (emit_band_decoder target_var offset K)
      (indicator_valuation (band_support offset x)).
Proof.
  intros target_var offset K x Hsep.
  unfold emit_band_decoder.
  apply eval_poly_fib_linears_ext.
  intros k Hk.
  eapply band_decoder_valuation_on_window; eauto.
Qed.

Lemma band_decoder_equation_wf :
  forall target_var offset K,
    equation_wf (band_decoder_equation target_var offset K).
Proof.
  intros target_var offset K.
  unfold band_decoder_equation.
  split.
  - constructor.
    + simpl.
      eapply Nat.le_lt_trans.
      * apply Nat.le_max_l.
      * apply Nat.lt_succ_diag_r.
    + constructor.
  - unfold emit_band_decoder.
    apply Forall_forall.
    intros t Hin.
    apply in_map_iff in Hin.
    destruct Hin as [k [Ht Hk]].
    subst t.
    simpl.
    apply band_digit_indices_bounds in Hk.
    lia.
Qed.

(*
│
│          `band_decoder_correct` is the main arithmetic bridge of the
│          file: under the canonical support valuation, the emitted
│          linear decoder solves its equation and evaluates to the FM
│          band code. This is exactly the band-local statement later
│          needed when a full FM trace is compiled into one global
│          cubic instance.
│
*)
(*                           x < fib(K) \Rightarrow                           *)
(*solves(band\_decoder\_equation(target,offset,K),\,band\_decoder\_valuation(target,offset,x))*)
(*   \,\wedge\, \llbracket emit\_band\_decoder(target,offset,K)\rrbracket =   *)
(*                           band\_code(offset,x).                            *)

Theorem band_decoder_correct :
  forall target_var offset K x,
    (target_var < offset + 2 \/ offset + K <= target_var) ->
    x < fib K ->
    solves (band_decoder_equation target_var offset K)
      (band_decoder_valuation target_var offset x) /\
    eval_poly (emit_band_decoder target_var offset K)
      (band_decoder_valuation target_var offset x) = band_code offset x.
Proof.
  intros target_var offset K x Hsep Hx.
  split.
  - split.
    + apply band_decoder_equation_wf.
    + unfold band_decoder_equation.
      change
        (eval_poly [{| coeff := 1; mono := m_linear target_var |}]
           (band_decoder_valuation target_var offset x) =
         eval_poly (emit_band_decoder target_var offset K)
           (band_decoder_valuation target_var offset x)).
      rewrite eval_poly_singleton.
      unfold eval_term.
      simpl.
      symmetry.
      rewrite eval_poly_emit_band_decoder_with_band_valuation by exact Hsep.
      rewrite emit_band_decoder_indicator by exact Hx.
      unfold band_decoder_valuation.
      rewrite Nat.eqb_refl.
      rewrite Nat.add_0_r.
      reflexivity.
  - rewrite eval_poly_emit_band_decoder_with_band_valuation by exact Hsep.
    apply emit_band_decoder_indicator.
    exact Hx.
Qed.
