(*P002_01__Architecture.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / P002_01__Architecture                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file is the architecture layer for P002.

  It centralizes the direct D001 import, the FM numeric aliases, the atomic
  cubic digit constraints, the band-window decoder, and the state-code
  aggregation facts used by the downstream trace-family construction.

*)

(*
│
│          Direct D001 access is centralized here through
│          `D001_98_API`; downstream P002 files should depend on this
│          architecture layer instead of reopening D001.
│
*)

(*                              P002₀₀ → P002₀₁                               *)
(*                              D001API → P002₀₁                              *)

From P002 Require Export P002_00_Premises.
From D001 Require Export D001_98_API.
From Stdlib Require Export List Arith Lia Sorting.Permutation.

(*
│
│          The FM code type is the natural-number carrier used by the
│          compiler layers.
│
*)

(*                                 FMCode ≔ ℕ                                 *)

Definition FMCode : Type := nat.

(*
│
│          The FM program alias keeps downstream statements
│          independent of the concrete D001 module path.
│
*)

(*                            FMProgram ≔ Program                             *)

Definition FMProgram : Type := program.

(*
│
│          State encoding is re-exported under an FM-facing name.
│
*)

(*                        FMEncodeState ≔ EncodeState                         *)

Definition FMEncodeState : IterantState -> FMCode := encode_state.

(*
│
│          State decoding is total at the numeric-code boundary.
│
*)

(*                        FMDecodeState ≔ DecodeState                         *)

Definition FMDecodeState : FMCode -> IterantState := decode_state.

(*
│
│          Normalization projects an arbitrary numeric code onto its
│          canonical D001 state code.
│
*)

(*                    FMNormalizeCode ≔ NormalizeStateCode                    *)

Definition FMNormalizeCode : FMCode -> FMCode := normalize_state_code.

(*
│
│          Validity is the D001 predicate that recognizes canonical
│          numeric state codes.
│
*)

(*                     FMValidStateCode ≔ ValidStateCode                      *)

Definition FMValidStateCode : FMCode -> Prop := valid_state_code.

(*
│
│          The FM step function is the public D001 next-state
│          transformer.
│
*)

(*                     FMStep(prog,s) ≔ NextState(prog,s)                     *)

Definition FMStep : FMProgram -> FMCode -> FMCode := NextState.

(*
│
│          A trace of numeric state codes is packed with the shared
│          natural-list encoder.
│
*)

(*                    FMTraceCode(xs) ≔ EncodeNatList(xs)                     *)

Definition FMTraceCode : list FMCode -> nat := encode_nat_list.

(*
│
│          The executable trace runner iterates a numeric step
│          function from an initial code.
│
*)

(*                         FMRunTrace ≔ CodeRunTrace                          *)

Definition FMRunTrace : (FMCode -> FMCode) -> nat -> FMCode -> list FMCode :=
  code_run_trace.

(*
│
│          The raw trace-witness predicate packages a bounded run
│          together with an accepting predicate on its last code.
│
*)

(*                  FMRawTraceWitness ≔ RawTraceWitnessFrom                   *)

Definition FMRawTraceWitness
    : (FMCode -> FMCode) -> (FMCode -> Prop) -> FMCode -> nat -> Prop :=
  raw_trace_witness_from.

(*
│
│          A valid numeric FM state code is exactly a fixed point of
│          the D001 normalization map. This is the bridge used when
│          P002 switches between arbitrary natural inputs and
│          canonical encoded states.
│
*)

(*                      ValidCode(s) ⇔ Normalize(s) = s                       *)

Theorem FM_valid_state_code_iff_fixed :
  forall s,
    FMValidStateCode s <-> FMNormalizeCode s = s.
Proof.
  exact valid_state_code_iff_fixed.
Qed.

(*
│
│          Decoding is total into the well-formed Iterant state space.
│          No side condition is needed before applying D001 state
│          projections to a decoded code.
│
*)

Theorem FM_decode_state_well_formed :
  forall s,
    state_well_formed (FMDecodeState s).
Proof.
  exact decode_state_well_formed.
Qed.

(*
│
│          The executable step test is an exact graph predicate for
│          the public FM next-state function.
│
*)

(*                StepB(prog,s,t) = true ⇔ t = FMStep(prog,s)                 *)

Theorem FM_stepb_correct :
  forall prog s t,
    stepb prog s t = true <-> t = FMStep prog s.
Proof.
  exact stepb_correct.
Qed.

(*
│
│          The parameterized executable step test is the same graph
│          predicate for the local next-state function over an
│          explicit instruction table.
│
*)

(*           StepBOf(L,prog,s,t) = true ⇔ t = NextStateOf(L,prog,s)           *)

Theorem FM_stepb_correct_of :
  forall L prog s t,
    stepb_of L prog s t = true <-> t = NextState_of L prog s.
Proof.
  exact stepb_correct_of.
Qed.

(*
│
│          The boolean digit constraint forces the selected valuation
│          entry to satisfy `x²=x`. Over ℕ this is equivalent to the
│          entry being either 0 or 1.
│
*)

(*                            BoolEq(i) : xᵢ² = xᵢ                            *)

Definition emit_boolean_constraint (i : nat) : h10_nd3n_equation :=
  {|
    var_count := S i;
    lhs_terms := [{| coeff := 1; mono := m_quadratic i i |}];
    rhs_terms := [{| coeff := 1; mono := m_linear i |}]
  |}.

(*
│
│          The non-adjacency constraint forces two selected digit
│          variables not to be simultaneously active. It is used for
│          adjacent Zeckendorf/Fibonacci support slots.
│
*)

(*                         NoAdjEq(i,j) : xᵢ · xⱼ = 0                         *)

Definition emit_non_adjacency_constraint (i j : nat) : h10_nd3n_equation :=
  {|
    var_count := S (Nat.max i j);
    lhs_terms := [{| coeff := 1; mono := m_quadratic i j |}];
    rhs_terms := []
  |}.

(*
│
│          A one-term polynomial evaluates to the value of its only
│          term. This small normalization lemma keeps the later
│          semantic proofs independent of the concrete `fold_right`
│          representation.
│
*)

Lemma eval_poly_singleton :
  forall (t : term) (rho : valuation),
    eval_poly [t] rho = eval_term rho t.
Proof.
  intros t rho.
  unfold eval_poly.
  simpl.
  lia.
Qed.

(*
│
│          The boolean digit equation is scoped exactly by its single
│          variable index.
│
*)

(*                               WF(BoolEq(i))                                *)

Lemma emit_boolean_constraint_wf :
  forall i,
    equation_wf (emit_boolean_constraint i).
Proof.
  intro i.
  unfold emit_boolean_constraint, equation_wf.
  split.
  - constructor.
    + simpl.
      split.
      * apply Nat.lt_succ_diag_r.
      * apply Nat.lt_succ_diag_r.
    + constructor.
  - constructor.
    + simpl.
      apply Nat.lt_succ_diag_r.
    + constructor.
Qed.

(*
│
│          The non-adjacency equation is scoped by the maximum of its
│          two variable indices.
│
*)

(*                              WF(NoAdjEq(i,j))                              *)

Lemma emit_non_adjacency_constraint_wf :
  forall i j,
    equation_wf (emit_non_adjacency_constraint i j).
Proof.
  intros i j.
  unfold emit_non_adjacency_constraint, equation_wf.
  split.
  - constructor.
    + simpl.
      split.
      * apply Nat.lt_succ_r.
        apply Nat.le_max_l.
      * apply Nat.lt_succ_r.
        apply Nat.le_max_r.
    + constructor.
  - constructor.
Qed.

(*
│
│          Over ℕ, the equation `n²=n` forces and is forced by
│          booleanity. This is the arithmetic fact behind the emitted
│          boolean digit constraint.
│
*)

(*                             n² = n ⇔ n ∈ {0,1}                             *)

Lemma nat_square_eq_self :
  forall n,
    n * n = n <-> n = 0 \/ n = 1.
Proof.
  intros n.
  split.
  - intro Hsq.
    destruct n as [|n].
    + left.
      reflexivity.
    + assert (Hmul : S n * S n = S n * 1).
      { replace (S n * 1) with (S n) by lia. exact Hsq. }
      apply Nat.mul_cancel_l in Hmul.
      * right.
        lia.
      * lia.
  - intros Hn.
    destruct Hn as [Hz|Ho].
    + subst.
      reflexivity.
    + subst.
      reflexivity.
Qed.

(*
│
│          The emitted boolean constraint is semantically exact:
│          solving it under a valuation is equivalent to the selected
│          entry being 0 or 1.
│
*)

(*                     Solves(BoolEq(i),ρ) ⇔ ρ(i) ∈ {0,1}                     *)

Lemma boolean_constraint_correct :
  forall (rho : valuation) (i : nat),
    solves (emit_boolean_constraint i) rho <->
    (rho i = 0 \/ rho i = 1).
Proof.
  intros rho i.
  unfold solves.
  split.
  - intros [_ Hsol].
    cbv [emit_boolean_constraint lhs_terms rhs_terms eval_poly eval_term eval_monomial]
      in Hsol.
    simpl in Hsol.
    repeat rewrite Nat.add_0_r in Hsol.
    apply nat_square_eq_self.
    exact Hsol.
  - intros Hbool.
    split.
    + apply emit_boolean_constraint_wf.
    + cbv [emit_boolean_constraint lhs_terms rhs_terms eval_poly eval_term eval_monomial].
      simpl.
      repeat rewrite Nat.add_0_r.
      apply nat_square_eq_self.
      exact Hbool.
Qed.

(*
│
│          The emitted non-adjacency constraint is semantically exact:
│          solving it means at least one of the two selected entries
│          is zero.
│
*)

(*                  Solves(NoAdjEq(i,j),ρ) ⇔ ρ(i)=0 ∨ ρ(j)=0                  *)

Lemma non_adjacency_correct :
  forall (rho : valuation) (i j : nat),
    solves (emit_non_adjacency_constraint i j) rho <->
    (rho i = 0 \/ rho j = 0).
Proof.
  intros rho i j.
  unfold emit_non_adjacency_constraint.
  split.
  - intros [_ Hsol].
    cbv [emit_non_adjacency_constraint lhs_terms rhs_terms eval_poly eval_term eval_monomial]
      in Hsol.
    simpl in Hsol.
    repeat rewrite Nat.add_0_r in Hsol.
    apply Nat.eq_mul_0.
    exact Hsol.
  - intros Hzero.
    split.
    + apply emit_non_adjacency_constraint_wf.
    + cbv [emit_non_adjacency_constraint lhs_terms rhs_terms eval_poly eval_term eval_monomial].
      simpl.
      repeat rewrite Nat.add_0_r.
      apply Nat.eq_mul_0.
      exact Hzero.
Qed.

  BAND WINDOWS

(*
│
│          The active digit slots of a band start two positions after
│          the offset and run for `K-2` entries. The first two
│          Fibonacci positions are deliberately skipped to align with
│          the Zeckendorf support convention imported from D001.
│
*)

(*                Digits(offset,K) = [offset+2, …, offset+K−1                 *)

Definition band_digit_indices (offset K : nat) : list nat :=
  seq (offset + 2) (K - 2).

(*
│
│          Adjacency constraints use the same lower endpoint but stop
│          one slot earlier, so every emitted pair `k,k+1` stays
│          inside the digit window.
│
*)

(*              Adjacencies(offset,K) = [offset+2, …, offset+K−2              *)

Definition band_adjacency_indices (offset K : nat) : list nat :=
  seq (offset + 2) (K - 3).

(*
│
│          Boolean band constraints apply the one-variable boolean
│          equation to every digit slot in the active window.
│
*)

(*           BandBool(offset,K) = map BoolEq over Digits(offset,K)            *)

Definition emit_band_boolean_constraints (offset K : nat) : list h10_nd3n_equation :=
  map emit_boolean_constraint (band_digit_indices offset K).

(*
│
│          Non-adjacency band constraints apply the two-variable
│          no-adjacent equation to every adjacent pair in the active
│          window.
│
*)

(*    BandNoAdj(offset,K) = map NoAdjEq(k,k+1) over Adjacencies(offset,K)     *)

Definition emit_band_non_adjacency_constraints (offset K : nat)
  : list h10_nd3n_equation :=
  map
    (fun k => emit_non_adjacency_constraint k (S k))
    (band_adjacency_indices offset K).

(*
│
│          The decoder right-hand side is the weighted Fibonacci sum
│          over the active digit slots. The target variable is kept in
│          the signature for uniformity with the equation emitter, but
│          the term list itself depends only on the band window.
│
*)

(*        DecoderRHS(offset,K) = Σ fib(k)·xₖ over k ∈ Digits(offset,K)        *)

Definition emit_band_decoder (_target_var offset K : nat) : list term :=
  map (fun k => {| coeff := fib k; mono := m_linear k |}) (band_digit_indices offset K).

(*
│
│          The decoder equation is oriented as one distinguished
│          readout variable equalling the weighted digit sum. Later
│          proofs keep `target_var` outside the digit window so the
│          decoder can be reasoned about without self-interference
│          from the support valuation.
│
*)

(*            DecoderEq(target,offset,K) : ρ(target)=Σ fib(k)·ρ(k)            *)

Definition band_decoder_equation (target_var offset K : nat) : h10_nd3n_equation :=
  {|
    var_count := S (Nat.max target_var (offset + K));
    lhs_terms := [{| coeff := 1; mono := m_linear target_var |}];
    rhs_terms := emit_band_decoder target_var offset K
  |}.

(*
│
│          The indicator valuation sends exactly the listed support
│          indices to 1 and every other index to 0. It is the raw
│          valuation used to interpret a Zeckendorf support as digit
│          variables.
│
*)

(*                             χₓₛ(n)=1 ⇔ n ∈ xs                              *)

Definition indicator_valuation (xs : list nat) : valuation :=
  fun n => if in_dec Nat.eq_dec n xs then 1 else 0.

(*
│
│          The band decoder valuation extends the indicator valuation
│          by assigning the decoded numeric band value to the
│          distinguished target variable.
│
*)

(*             ρ(target)=BandCode(offset,x); ρ(k)=χₛ(k) otherwise             *)

Definition band_decoder_valuation (target_var offset x : nat) : valuation :=
  fun n =>
    if Nat.eqb n target_var
    then band_code offset x
    else indicator_valuation (band_support offset x) n.

(*
│
│          Boolean membership is a small executable wrapper around
│          list membership. It is used only to connect filtered
│          decoder windows with support lists.
│
*)

(*                          Mem(xs,n)=true ⇔ n ∈ xs                           *)

Definition mem_nat (xs : list nat) (n : nat) : bool :=
  if in_dec Nat.eq_dec n xs then true else false.

(*
│
│          The executable membership wrapper is logically equivalent
│          to ordinary list membership.
│
*)

(*                          Mem(xs,n)=true ⇔ n ∈ xs                           *)

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

(*
│
│          Filtering a duplicate-free list preserves
│          duplicate-freeness. This generic list fact supports the
│          permutation proof for filtered band windows.
│
*)

(*                      NoDup(xs) ⇒ NoDup(filter(f,xs))                       *)

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

(*
│
│          In a strictly decreasing list, the head is greater than
│          every element in the tail.
│
*)

(*                    StrictDec(a :: xs) ∧ y ∈ xs ⇒ a > y                     *)

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

(*
│
│          Strictly decreasing lists have no duplicate entries. This
│          is the uniqueness fact used for Zeckendorf supports.
│
*)

(*                         StrictDec(xs) ⇒ NoDup(xs)                          *)

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

(*
│
│          In a no-adjacent support list, the head is separated from
│          every later entry by at least one unused slot.
│
*)

(*                     NoAdj(a :: xs) ∧ y ∈ xs ⇒ a ≥ y+2                      *)

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

(*
│
│          The Fibonacci sum over a support list is invariant under
│          permutation.
│
*)

(*                        xs ≃ ys ⇒ Σfib(xs)=Σfib(ys)                         *)

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

(*
│
│          Evaluating a Fibonacci-weighted linear decoder under an
│          indicator valuation keeps exactly the weights whose indices
│          occur in the support.
│
*)

(*                ⟦Σ fib(k)·xₖ⟧χₓₛ = Σfib(filter(Mem(xs),ks))                 *)

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

(*
│
│          A Fibonacci-weighted linear decoder is insensitive to
│          valuation changes outside the listed indices.
│
*)

(*            ρ = ρ′ on ks ⇒ EvalDecoder(ks,ρ)=EvalDecoder(ks,ρ′)             *)

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

(*
│
│          Every digit index emitted for a band lies inside the
│          intended half-open window.
│
*)

(*               k ∈ Digits(offset,K) ⇒ offset+2 ≤ k < offset+K               *)

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

(*
│
│          Filtering the full band window by a duplicate-free
│          in-window support recovers that support up to permutation.
│
*)

(*                   filter(Mem(xs),Digits(offset,K)) ≃ xs                    *)

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

(*
│
│          A valid Zeckendorf support cannot contain both an index and
│          its immediate successor.
│
*)

(*                     ZeckValid(xs) ∧ k ∈ xs ⇒ k+1 ∉ xs                      *)

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

(*
│
│          The shifted support used by a band inherits the no-adjacent
│          property from the canonical Zeckendorf support of the
│          encoded number.
│
*)

(*          k ∈ BandSupport(offset,x) ⇒ k+1 ∉ BandSupport(offset,x)           *)

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

(*
│
│          Every entry of an indicator valuation is boolean.
│
*)

(*                               χₓₛ(k) ∈ {0,1}                               *)

Lemma indicator_valuation_boolean :
  forall xs k,
    indicator_valuation xs k = 0 \/ indicator_valuation xs k = 1.
Proof.
  intros xs k.
  unfold indicator_valuation.
  destruct (in_dec Nat.eq_dec k xs); [right | left]; reflexivity.
Qed.

(*
│
│          The indicator valuation for a band support solves every
│          boolean digit constraint.
│
*)

(*                            Solves(BoolEq(k),χₛ)                            *)

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

(*
│
│          The indicator valuation for a band support solves every
│          adjacent-pair exclusion equation.
│
*)

(*                         Solves(NoAdjEq(k,k+1),χₛ)                          *)

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
│          Under the indicator valuation, the Fibonacci-weighted
│          decoder right-hand side evaluates to the numeric band code.
│
*)

(*                     EvalDecoder(χₛ)=BandCode(offset,x)                     *)

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

(*
│
│          If the target variable is outside the digit window, the
│          band decoder valuation agrees with the indicator valuation
│          on every decoder digit.
│
*)

(*       target ∉ Digits(offset,K) ∧ k ∈ Digits(offset,K) ⇒ ρᵦ(k)=χₛ(k)       *)

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
│          Because the decoder polynomial only reads digit-window
│          variables, it has the same value under the band valuation
│          and the raw indicator valuation.
│
*)

(*                      EvalDecoder(ρᵦ)=EvalDecoder(χₛ)                       *)

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

(*
│
│          The band decoder equation is well-scoped by the maximum of
│          the target variable and the top of the band window.
│
*)

(*                       WF(DecoderEq(target,offset,K))                       *)

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
│          The decoder equation is correct for a value below the band
│          capacity: the constructed valuation solves the equation,
│          and the decoder right-hand side evaluates to the
│          corresponding band code.
│
*)

(*   x < fib(K) ⇒ Solves(DecoderEq,ρᵦ) ∧ EvalDecoder(ρᵦ)=BandCode(offset,x)   *)

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

  STATE CODEC

(*
│
│          The state codec section works with the D001 structured
│          machine state type under a local alias.
│
*)

(*                        MachineState ≔ IterantState                         *)

Definition MachineState : Type := IterantState.

(*
│
│          The right-hand side of the state codec equation is the
│          additive sum of the already-encoded instruction pointer and
│          register components.
│
*)

(*                        StateRHS(i,r₁,r₂)=xᵢ+xᵣ₁+xᵣ₂                        *)

Definition emit_state_codec_rhs (ip_var r1_var r2_var : nat) : list term :=
  [ {| coeff := 1; mono := m_linear ip_var |};
    {| coeff := 1; mono := m_linear r1_var |};
    {| coeff := 1; mono := m_linear r2_var |} ].

(*
│
│          The emitted state equation does not decode anything by
│          itself. It simply exposes one additive shell in which the
│          designated state-code variable is constrained to equal the
│          sum of the three already-understood channel codes.
│
*)

(*                 StateEq(s,i,r₁,r₂) : ρ(s)=ρ(i)+ρ(r₁)+ρ(r₂)                 *)

Definition state_codec_equation
    (state_var ip_var r1_var r2_var : nat) : h10_nd3n_equation :=
  {|
    var_count := S (Nat.max state_var (Nat.max ip_var (Nat.max r1_var r2_var)));
    lhs_terms := [{| coeff := 1; mono := m_linear state_var |}];
    rhs_terms := emit_state_codec_rhs ip_var r1_var r2_var
  |}.

(*
│
│          The canonical state-code valuation assigns the full encoded
│          state and its three additive component codes to four
│          distinct variable slots, defaulting all other variables to
│          zero.
│
*)

(*    ρ(s)=Encode(st); ρ(i)=IPCode(st); ρ(r₁)=R1Code(st); ρ(r₂)=R2Code(st)    *)

Definition state_codec_valuation
    (state_var ip_var r1_var r2_var : nat) (st : MachineState) : valuation :=
  fun n =>
    if Nat.eqb n state_var then encode_state st
    else if Nat.eqb n ip_var then ip_code (state_ip st)
    else if Nat.eqb n r1_var then r1_code (state_r1 st)
    else if Nat.eqb n r2_var then r2_code (state_r2 st)
    else 0.

(*
│
│          The four state-code slots must be pairwise distinct so that
│          the valuation clauses above do not shadow one another.
│
*)

(*                      s,i,r₁,r₂ are pairwise distinct                       *)

Definition state_codec_vars_separated
    (state_var ip_var r1_var r2_var : nat) : Prop :=
  state_var <> ip_var /\
  state_var <> r1_var /\
  state_var <> r2_var /\
  ip_var <> r1_var /\
  ip_var <> r2_var /\
  r1_var <> r2_var.

(*
│
│          Evaluating the state codec right-hand side under a
│          valuation gives the sum of the three component variables.
│
*)

(*                  ⟦StateRHS(i,r₁,r₂)⟧ρ = ρ(i)+ρ(r₁)+ρ(r₂)                   *)

Lemma eval_state_codec_rhs :
  forall rho ip_var r1_var r2_var,
    eval_poly (emit_state_codec_rhs ip_var r1_var r2_var) rho =
    rho ip_var + rho r1_var + rho r2_var.
Proof.
  intros rho ip_var r1_var r2_var.
  unfold emit_state_codec_rhs, eval_poly, eval_term.
  simpl.
  lia.
Qed.

(*
│
│          The state codec equation is well-scoped by the maximum of
│          its four designated variable indices.
│
*)

(*                           WF(StateEq(s,i,r₁,r₂))                           *)

Lemma state_codec_equation_wf :
  forall state_var ip_var r1_var r2_var,
    equation_wf (state_codec_equation state_var ip_var r1_var r2_var).
Proof.
  intros state_var ip_var r1_var r2_var.
  unfold state_codec_equation.
  split.
  - constructor.
    + simpl.
      apply Nat.lt_succ_r.
      apply Nat.le_max_l.
    + constructor.
  - constructor.
    + simpl.
      apply Nat.lt_succ_r.
      apply Nat.le_trans with (m := Nat.max ip_var (Nat.max r1_var r2_var)).
      * apply Nat.le_max_l.
      * apply Nat.le_max_r.
    + constructor.
      * simpl.
        apply Nat.lt_succ_r.
        apply Nat.le_trans with (m := Nat.max ip_var (Nat.max r1_var r2_var)).
        -- apply Nat.le_trans with (m := Nat.max r1_var r2_var).
           ++ apply Nat.le_max_l.
           ++ apply Nat.le_max_r.
        -- apply Nat.le_max_r.
      * constructor.
        -- simpl.
           apply Nat.lt_succ_r.
           apply Nat.le_trans with (m := Nat.max ip_var (Nat.max r1_var r2_var)).
           ++ apply Nat.le_trans with (m := Nat.max r1_var r2_var).
              ** apply Nat.le_max_r.
              ** apply Nat.le_max_r.
           ++ apply Nat.le_max_r.
        -- constructor.
Qed.

(*
│
│          Solving the state codec equation is equivalent to
│          well-formedness plus the intended additive equality between
│          the state-code slot and the three component slots.
│
*)

(*          Solves(StateEq,ρ) ⇔ WF(StateEq) ∧ ρ(s)=ρ(i)+ρ(r₁)+ρ(r₂)           *)

Lemma state_codec_equation_semantics :
  forall rho state_var ip_var r1_var r2_var,
    solves (state_codec_equation state_var ip_var r1_var r2_var) rho <->
    equation_wf (state_codec_equation state_var ip_var r1_var r2_var) /\
    rho state_var = rho ip_var + rho r1_var + rho r2_var.
Proof.
  intros rho state_var ip_var r1_var r2_var.
  unfold solves, state_codec_equation.
  split.
  - intros [Hwf Hsol].
    split.
    + exact Hwf.
    + change
        (eval_poly [{| coeff := 1; mono := m_linear state_var |}] rho =
         eval_poly (emit_state_codec_rhs ip_var r1_var r2_var) rho) in Hsol.
      rewrite eval_poly_singleton in Hsol.
      rewrite eval_state_codec_rhs in Hsol.
      unfold eval_term in Hsol.
      simpl in Hsol.
      lia.
  - intros [Hwf Hsum].
    split.
    + exact Hwf.
    + change
        (eval_poly [{| coeff := 1; mono := m_linear state_var |}] rho =
         eval_poly (emit_state_codec_rhs ip_var r1_var r2_var) rho).
      rewrite eval_poly_singleton.
      rewrite eval_state_codec_rhs.
      unfold eval_term.
      simpl.
      lia.
Qed.

(*
│
│          For pairwise-distinct variable slots, the canonical
│          state-code valuation solves the emitted state equation for
│          any structured machine state.
│
*)

(*                 Separated(s,i,r₁,r₂) ⇒ Solves(StateEq,ρₛ)                  *)

Lemma state_codec_equation_correct :
  forall state_var ip_var r1_var r2_var st,
    state_codec_vars_separated state_var ip_var r1_var r2_var ->
    solves
      (state_codec_equation state_var ip_var r1_var r2_var)
      (state_codec_valuation state_var ip_var r1_var r2_var st).
Proof.
  intros state_var ip_var r1_var r2_var st
    (Hsip & Hsr1 & Hsr2 & Hipr1 & Hipr2 & Hr1r2).
  apply (proj2 (state_codec_equation_semantics
                  (state_codec_valuation state_var ip_var r1_var r2_var st)
                  state_var ip_var r1_var r2_var)).
  split.
  - apply state_codec_equation_wf.
  - unfold state_codec_valuation.
    assert (Hstate :
      (if state_var =? state_var then encode_state st
       else if state_var =? ip_var then ip_code (state_ip st)
       else if state_var =? r1_var then r1_code (state_r1 st)
       else if state_var =? r2_var then r2_code (state_r2 st)
       else 0) = encode_state st).
    { rewrite Nat.eqb_refl. reflexivity. }
    assert (Hip :
      (if ip_var =? state_var then encode_state st
       else if ip_var =? ip_var then ip_code (state_ip st)
       else if ip_var =? r1_var then r1_code (state_r1 st)
       else if ip_var =? r2_var then r2_code (state_r2 st)
       else 0) = ip_code (state_ip st)).
    {
      destruct (Nat.eqb_spec ip_var state_var) as [Heq|Hneq].
      - exfalso. apply Hsip. symmetry. exact Heq.
      - rewrite Nat.eqb_refl.
        reflexivity.
    }
    assert (Hr1 :
      (if r1_var =? state_var then encode_state st
       else if r1_var =? ip_var then ip_code (state_ip st)
       else if r1_var =? r1_var then r1_code (state_r1 st)
       else if r1_var =? r2_var then r2_code (state_r2 st)
       else 0) = r1_code (state_r1 st)).
    {
      destruct (Nat.eqb_spec r1_var state_var) as [Heq|Hneq].
      - exfalso. apply Hsr1. symmetry. exact Heq.
      - destruct (Nat.eqb_spec r1_var ip_var) as [Heq'|Hneq'].
        + exfalso. apply Hipr1. symmetry. exact Heq'.
        + rewrite Nat.eqb_refl.
          reflexivity.
    }
    assert (Hr2 :
      (if r2_var =? state_var then encode_state st
       else if r2_var =? ip_var then ip_code (state_ip st)
       else if r2_var =? r1_var then r1_code (state_r1 st)
       else if r2_var =? r2_var then r2_code (state_r2 st)
       else 0) = r2_code (state_r2 st)).
    {
      destruct (Nat.eqb_spec r2_var state_var) as [Heq|Hneq].
      - exfalso. apply Hsr2. symmetry. exact Heq.
      - destruct (Nat.eqb_spec r2_var ip_var) as [Heq'|Hneq'].
        + exfalso. apply Hipr2. symmetry. exact Heq'.
        + destruct (Nat.eqb_spec r2_var r1_var) as [Heq''|Hneq''].
          * exfalso. apply Hr1r2. symmetry. exact Heq''.
          * rewrite Nat.eqb_refl.
            reflexivity.
    }
    rewrite Hstate, Hip, Hr1, Hr2.
    rewrite encode_state_as_components.
    lia.
Qed.

(*
│
│          A well-formed structured state has canonical Zeckendorf
│          support.
│
*)

(*                WellFormed(st) ⇒ ZeckValid(StateSupport(st))                *)

Lemma encode_is_canonical :
  forall st,
    state_well_formed st ->
    zeck_valid (state_support st).
Proof.
  exact state_support_valid.
Qed.

(*
│
│          Encoding and then decoding a well-formed structured state
│          is the identity.
│
*)

(*                  WellFormed(st) ⇒ Decode(Encode(st)) = st                  *)

Lemma decode_encode_id :
  forall st,
    state_well_formed st ->
    decode_state (encode_state st) = st.
Proof.
  exact decode_state_encode_state.
Qed.

(*
│
│          State encoding is injective on well-formed structured
│          states.
│
*)

(*                     Encode(st₁)=Encode(st₂) ⇒ st₁=st₂                      *)

Lemma encode_injective :
  forall st1 st2,
    state_well_formed st1 ->
    state_well_formed st2 ->
    encode_state st1 = encode_state st2 ->
    st1 = st2.
Proof.
  exact encode_state_injective.
Qed.

(*
│
│          A valid numeric state code is exactly the additive sum of
│          the decoded instruction-pointer and register component
│          codes.
│
*)

(*     ValidCode(s) ∧ Decode(s)=st ⇒ s = R2Code(st)+R1Code(st)+IPCode(st)     *)

Lemma state_arithmetization_form :
  forall s st,
    valid_state_code s ->
    decode_state s = st ->
    s =
    r2_code (state_r2 st) +
    r1_code (state_r1 st) +
    ip_code (state_ip st).
Proof.
  intros s st Hvalid Hdecode.
  destruct Hvalid as [st' [Hwf Hcode]].
  subst s.
  rewrite decode_state_encode_state in Hdecode by exact Hwf.
  subst st.
  apply encode_state_as_components.
Qed.
