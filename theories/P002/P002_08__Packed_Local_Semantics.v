(*P002_08__Packed_Local_Semantics.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                 Proofcase / P002_08__Packed_Local_Semantics                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This layer packages the local packed semantics below full trace validity:
  stacked mask constraints, one-step packed channel shifts, decoded-view
  predicates, and range facts obtained from mask bounds.

  The file is still semantic only. It does not emit polynomial families and
  does not prove full trace correctness; it only provides the
  current/tail-view interface consumed by packed machine-step and witness
  layers.

*)

(*
│
│          This file uses binary naturals and linear arithmetic for
│          local packed-channel decoding and range transport.
│
*)

(*                                  ℕ₂ ∧ lia                                  *)

From Stdlib Require Import NArith Lia.

(*
│
│          The local packed semantics consumes machine-step
│          observations and the packed carryless-mask codec.
│
*)

(*                          P002₀₂ ∧ P002₀₇ → P002₀₈                          *)

From P002 Require Import P002_02__Machine_Step.
From P002 Require Import P002_07__Packed_Carryless_Masks.

Module MS := P002_02__Machine_Step.
Module PC := P002_07__Packed_Carryless_Masks.
Module PM := P002_07__Packed_Carryless_Masks.

Local Notation packed_trace_params := PC.packed_trace_params.
Local Notation packed_trace_vars := PC.packed_trace_vars.
Local Notation packed_state_view := PC.packed_state_view.
Local Notation packed_state_at := PC.packed_state_at.
Local Notation state_view_matches_code := PC.state_view_matches_code.
Local Notation packs_trace := PC.packs_trace.
Local Notation packed_channel_bounds := PM.packed_channel_bounds.
Local Notation packed_digits_bounded := PM.packed_digits_bounded.
Local Notation packed_mask_constraints := PM.packed_mask_constraints.
Local Notation packed_boolean_channel := PM.channel_digits_bounded.
Local Notation channel_bounds_wf := PM.channel_bounds_wf.
Local Notation pt_base := PC.pt_base.
Local Notation pt_horizon := PC.pt_horizon.
Local Notation pt_state_ch := PC.pt_state_ch.
Local Notation pt_ip_ch := PC.pt_ip_ch.
Local Notation pt_r1_ch := PC.pt_r1_ch.
Local Notation pt_r2_ch := PC.pt_r2_ch.
Local Notation pt_halt_ch := PC.pt_halt_ch.
Local Notation pt_base_pow2 := PC.pt_base_pow2.
Local Notation ps_state := PC.ps_state.
Local Notation ps_ip := PC.ps_ip.
Local Notation ps_r1 := PC.ps_r1.
Local Notation ps_r2 := PC.ps_r2.
Local Notation ps_halt := PC.ps_halt.
Local Notation pcb_state_bound := PM.pcb_state_bound.
Local Notation pcb_ip_bound := PM.pcb_ip_bound.
Local Notation pcb_r1_bound := PM.pcb_r1_bound.
Local Notation pcb_r2_bound := PM.pcb_r2_bound.
Local Notation pcb_halt_bound := PM.pcb_halt_bound.

Local Open Scope N_scope.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                              MASK STACKING                              ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          One stack slot stores a low component and a higher stacked
│          tail in base `stack_base`.
│
*)

(*                        Slot(B,low,high)=low+high·B                         *)

Definition stack_slot (stack_base low high : N) : N :=
  low + high * stack_base.

(*
│
│          Five stack components are encoded by iterating the one-slot
│          constructor.
│
*)

(*           Stack₅(B,x₁,x₂,x₃,x₄,x₅)=x₁+B·(x₂+B·(x₃+B·(x₄+B·x₅)))            *)

Definition stack5 (stack_base x1 x2 x3 x4 x5 : N) : N :=
  stack_slot stack_base x1
    (stack_slot stack_base x2
      (stack_slot stack_base x3
        (stack_slot stack_base x4 x5))).

(*
│
│          If a low digit is below the base and the high tail is below
│          a limit, the stacked slot is below `limit·base`.
│
*)

(*                0<B ∧ low<B ∧ high<L ⇒ Slot(B,low,high)<L·B                 *)

Lemma stack_slot_bound :
  forall B low high limit,
    0 < B ->
    low < B ->
    high < limit ->
    stack_slot B low high < limit * B.
Proof.
  intros B low high limit HB Hlow Hhigh.
  unfold stack_slot.
  assert (Hsucc : N.succ high <= limit) by lia.
  assert (Hlt : high * B + low < high * B + B) by lia.
  assert (Hle : high * B + B <= limit * B).
  {
    rewrite <- N.mul_succ_l.
    apply N.mul_le_mono_r.
    exact Hsucc.
  }
  lia.
Qed.

(*
│
│          Five base-bounded digits stack below the fifth power of the
│          base.
│
*)

(*               0<B ∧ ∀ i. xᵢ<B ⇒ Stack₅(B,x₁,x₂,x₃,x₄,x₅)<B⁵                *)

Lemma stack5_bound :
  forall B x1 x2 x3 x4 x5,
    0 < B ->
    x1 < B ->
    x2 < B ->
    x3 < B ->
    x4 < B ->
    x5 < B ->
    stack5 B x1 x2 x3 x4 x5 < B * B * B * B * B.
Proof.
  intros B x1 x2 x3 x4 x5 HB H1 H2 H3 H4 H5.
  unfold stack5.
  pose proof (stack_slot_bound B x4 x5 B HB H4 H5) as H45.
  pose proof
    (stack_slot_bound B x3 (stack_slot B x4 x5)
       (B * B) HB H3 H45) as H345.
  pose proof
    (stack_slot_bound B x2 (stack_slot B x3 (stack_slot B x4 x5))
       (B * B * B) HB H2 H345) as H2345.
  pose proof
    (stack_slot_bound B x1
       (stack_slot B x2 (stack_slot B x3 (stack_slot B x4 x5)))
       (B * B * B * B) HB H1 H2345) as H12345.
  exact H12345.
Qed.

(*
│
│          The state-channel mask value is the repeated bound mask for
│          the state bound.
│
*)

(*         StateMask(p,b)=MaskValue(base(p),horizon(p),stateBound(b))         *)

Definition packed_mask_state_value
    (p : packed_trace_params) (b : packed_channel_bounds) : N :=
  bound_mask_value (pt_base p) (pt_horizon p) (pcb_state_bound b).

(*
│
│          The instruction-pointer mask value is the repeated bound
│          mask for the instruction-pointer bound.
│
*)

(*            IpMask(p,b)=MaskValue(base(p),horizon(p),ipBound(b))            *)

Definition packed_mask_ip_value
    (p : packed_trace_params) (b : packed_channel_bounds) : N :=
  bound_mask_value (pt_base p) (pt_horizon p) (pcb_ip_bound b).

(*
│
│          The first-register mask value is the repeated bound mask
│          for the first-register bound.
│
*)

(*            R₁Mask(p,b)=MaskValue(base(p),horizon(p),r₁Bound(b))            *)

Definition packed_mask_r1_value
    (p : packed_trace_params) (b : packed_channel_bounds) : N :=
  bound_mask_value (pt_base p) (pt_horizon p) (pcb_r1_bound b).

(*
│
│          The second-register mask value is the repeated bound mask
│          for the second-register bound.
│
*)

(*            R₂Mask(p,b)=MaskValue(base(p),horizon(p),r₂Bound(b))            *)

Definition packed_mask_r2_value
    (p : packed_trace_params) (b : packed_channel_bounds) : N :=
  bound_mask_value (pt_base p) (pt_horizon p) (pcb_r2_bound b).

(*
│
│          The halt-channel mask value is the repeated bound mask for
│          the halt-channel bound.
│
*)

(*          HaltMask(p,b)=MaskValue(base(p),horizon(p),haltBound(b))          *)

Definition packed_mask_halt_value
    (p : packed_trace_params) (b : packed_channel_bounds) : N :=
  bound_mask_value (pt_base p) (pt_horizon p) (pcb_halt_bound b).

(*
│
│          The stacked mask source packages the five packed channel
│          values into one stacked number.
│
*)

(*               StackSource(B,v)=Stack₅(B,state,ip,r₁,r₂,halt)               *)

Definition packed_mask_stack_source
    (stack_base : N) (v : packed_trace_vars) : N :=
  stack5 stack_base
    (pt_state_ch v)
    (pt_ip_ch v)
    (pt_r1_ch v)
    (pt_r2_ch v)
    (pt_halt_ch v).

(*
│
│          The stacked mask target packages the five repeated mask
│          values into one stacked number.
│
*)

(*    StackTarget(p,b,B)=Stack₅(B,StateMask,IpMask,R₁Mask,R₂Mask,HaltMask)    *)

Definition packed_mask_stack_target
    (p : packed_trace_params)
    (b : packed_channel_bounds)
    (stack_base : N) : N :=
  stack5 stack_base
    (packed_mask_state_value p b)
    (packed_mask_ip_value p b)
    (packed_mask_r1_value p b)
    (packed_mask_r2_value p b)
    (packed_mask_halt_value p b).

(*
│
│          A stacked mask instance stores the stack base and the two
│          aggregate values whose no-carry relation will represent all
│          five channel masks.
│
*)

(*                            StackedMask=(B,S,T)                             *)

Record stacked_mask_instance : Type := {
  sm_stack_base : N;
  sm_S : N;
  sm_T : N
}.

(*
│
│          A stacked mask instance is well-formed when the slot base
│          is binary, every source and target component fits below it,
│          and the stored aggregates are the intended stacks.
│
*)

(*StackWF ⇔ pow₂(B) ∧ components<B ∧ S=StackSource(B,v) ∧ T=StackTarget(p,b,B)*)

Definition mask_stack_wf
    (p : packed_trace_params)
    (b : packed_channel_bounds)
    (v : packed_trace_vars)
    (sm : stacked_mask_instance) : Prop :=
  pow2 (sm_stack_base sm) /\
  pt_state_ch v < sm_stack_base sm /\
  packed_mask_state_value p b < sm_stack_base sm /\
  pt_ip_ch v < sm_stack_base sm /\
  packed_mask_ip_value p b < sm_stack_base sm /\
  pt_r1_ch v < sm_stack_base sm /\
  packed_mask_r1_value p b < sm_stack_base sm /\
  pt_r2_ch v < sm_stack_base sm /\
  packed_mask_r2_value p b < sm_stack_base sm /\
  pt_halt_ch v < sm_stack_base sm /\
  packed_mask_halt_value p b < sm_stack_base sm /\
  sm_S sm = packed_mask_stack_source (sm_stack_base sm) v /\
  sm_T sm = packed_mask_stack_target p b (sm_stack_base sm).

(*
│
│          The stacked mask constraint is one aggregate carryless
│          predicate between the stacked source and target.
│
*)

(*                   StackConstraint(sm) ⇔ carryless₂(S,T)                    *)

Definition packed_mask_stack_constraint
    (sm : stacked_mask_instance) : Prop :=
  carryless2 (sm_S sm) (sm_T sm).

(*
│
│          Five componentwise carryless constraints stack into one
│          aggregate carryless constraint.
│
*)

(*               pow₂(N) ∧ bounds₁₋₄ ∧ ∀ i. carryless₂(sᵢ,tᵢ) ⇒               *)
(*                   carryless₂(Stack₅(N,sᵢ),Stack₅(N,tᵢ))                    *)

Lemma carryless_stack_5 :
  forall N s1 s2 s3 s4 s5 t1 t2 t3 t4 t5,
    pow2 N ->
    s1 < N ->
    t1 < N ->
    s2 < N ->
    t2 < N ->
    s3 < N ->
    t3 < N ->
    s4 < N ->
    t4 < N ->
    carryless2 s1 t1 ->
    carryless2 s2 t2 ->
    carryless2 s3 t3 ->
    carryless2 s4 t4 ->
    carryless2 s5 t5 ->
    carryless2 (stack5 N s1 s2 s3 s4 s5)
               (stack5 N t1 t2 t3 t4 t5).
Proof.
  intros N s1 s2 s3 s4 s5 t1 t2 t3 t4 t5
    Hpow Hs1 Ht1 Hs2 Ht2 Hs3 Ht3 Hs4 Ht4
    H1 H2 H3 H4 H5.
  unfold stack5, stack_slot.
  apply carryless_stack_2.
  - exact Hpow.
  - exact Hs1.
  - exact Ht1.
  - exact H1.
  - apply carryless_stack_2.
    + exact Hpow.
    + exact Hs2.
    + exact Ht2.
    + exact H2.
    + apply carryless_stack_2.
      * exact Hpow.
      * exact Hs3.
      * exact Ht3.
      * exact H3.
      * apply carryless_stack_2.
        -- exact Hpow.
        -- exact Hs4.
        -- exact Ht4.
        -- exact H4.
        -- exact H5.
Qed.

(*
│
│          One aggregate carryless constraint over five stacked slots
│          unpacks into the five componentwise carryless constraints.
│
*)

(*     pow₂(N) ∧ bounds₁₋₄ ∧ carryless₂(Stack₅(N,sᵢ),Stack₅(N,tᵢ)) ⇒ ∀ i.     *)
(*                             carryless₂(sᵢ,tᵢ)                              *)

Lemma carryless_unstack_5 :
  forall N s1 s2 s3 s4 s5 t1 t2 t3 t4 t5,
    pow2 N ->
    s1 < N ->
    t1 < N ->
    s2 < N ->
    t2 < N ->
    s3 < N ->
    t3 < N ->
    s4 < N ->
    t4 < N ->
    carryless2 (stack5 N s1 s2 s3 s4 s5)
               (stack5 N t1 t2 t3 t4 t5) ->
    carryless2 s1 t1 /\
    carryless2 s2 t2 /\
    carryless2 s3 t3 /\
    carryless2 s4 t4 /\
    carryless2 s5 t5.
Proof.
  intros N s1 s2 s3 s4 s5 t1 t2 t3 t4 t5
    Hpow Hs1 Ht1 Hs2 Ht2 Hs3 Ht3 Hs4 Ht4 Hcarry.
  unfold stack5, stack_slot in Hcarry.
  pose proof
    (carryless_unstack_2
       N
       s1 t1
       (stack_slot N s2 (stack_slot N s3 (stack_slot N s4 s5)))
       (stack_slot N t2 (stack_slot N t3 (stack_slot N t4 t5)))
       Hpow Hs1 Ht1 Hcarry) as [H1 Hrest1].
  pose proof
    (carryless_unstack_2
       N
       s2 t2
       (stack_slot N s3 (stack_slot N s4 s5))
       (stack_slot N t3 (stack_slot N t4 t5))
       Hpow Hs2 Ht2 Hrest1) as [H2 Hrest2].
  pose proof
    (carryless_unstack_2
       N
       s3 t3
       (stack_slot N s4 s5)
       (stack_slot N t4 t5)
       Hpow Hs3 Ht3 Hrest2) as [H3 Hrest3].
  pose proof
    (carryless_unstack_2
       N
       s4 t4
       s5 t5
       Hpow Hs4 Ht4 Hrest3) as [H4 H5].
  repeat split; assumption.
Qed.

(*
│
│          A well-formed stacked mask instance is correct: the single
│          aggregate no-carry constraint is equivalent to the five
│          packed mask constraints.
│
*)

(*        StackWF(p,b,v,sm) ⇒ StackConstraint(sm) ⇔ PackedMasks(p,b,v)        *)

Theorem packed_mask_stack_correct :
  forall p b v sm,
    mask_stack_wf p b v sm ->
    packed_mask_stack_constraint sm <->
    packed_mask_constraints p b v.
Proof.
  intros p b v sm
    (Hpow &
     Hstate & HstateMask &
     Hip & HipMask &
     Hr1 & Hr1Mask &
     Hr2 & Hr2Mask &
     Hhalt & HhaltMask &
     HS & HT).
  unfold packed_mask_stack_constraint, packed_mask_constraints.
  rewrite HS, HT.
  split.
  - intro Hstack.
    pose proof
      (carryless_unstack_5
         (sm_stack_base sm)
         (pt_state_ch v) (pt_ip_ch v) (pt_r1_ch v) (pt_r2_ch v) (pt_halt_ch v)
         (packed_mask_state_value p b)
         (packed_mask_ip_value p b)
         (packed_mask_r1_value p b)
         (packed_mask_r2_value p b)
         (packed_mask_halt_value p b)
         Hpow
         Hstate HstateMask
         Hip HipMask
         Hr1 Hr1Mask
         Hr2 Hr2Mask
         Hstack) as
      (HstateC & HipC & Hr1C & Hr2C & HhaltC).
    repeat split; assumption.
  - intros (HstateC & HipC & Hr1C & Hr2C & HhaltC).
    eapply carryless_stack_5.
    + exact Hpow.
    + exact Hstate.
    + exact HstateMask.
    + exact Hip.
    + exact HipMask.
    + exact Hr1.
    + exact Hr1Mask.
    + exact Hr2.
    + exact Hr2Mask.
    + exact HstateC.
    + exact HipC.
    + exact Hr1C.
    + exact Hr2C.
    + exact HhaltC.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                            PACKED SHIFT CODEC                           ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          Binary powers are strictly positive.
│
*)

(*                               pow₂(B) ⇒ 0<B                                *)

Lemma pow2_positive :
  forall B,
    pow2 B ->
    0 < B.
Proof.
  intros B Hpow.
  apply (proj1 (N.neq_0_lt_0 B)).
  apply PC.pow2_nonzero.
  exact Hpow.
Qed.

(*
│
│          Successor base powers can be written with the base on the
│          right.
│
*)

(*                       BasePow(B,S t)=BasePow(B,t)·B                        *)

Lemma base_pow_succ :
  forall B t,
    base_pow B (S t) = base_pow B t * B.
Proof.
  intros B t.
  rewrite PC.base_pow_succ.
  rewrite N.mul_comm.
  reflexivity.
Qed.

(*
│
│          Dividing a channel by the base shifts digit extraction to
│          the next original digit.
│
*)

(*                   0<B ⇒ Digit(B,⌊X÷B⌋,t)=Digit(B,X,S t)                    *)

Lemma digit_at_div_base :
  forall B X t,
    0 < B ->
    digit_at B (X / B) t = digit_at B X (S t).
Proof.
  intros B X t Hpos.
  unfold digit_at.
  rewrite PC.base_pow_succ.
  rewrite <- (N.Div0.div_div X B (base_pow B t)).
  reflexivity.
Qed.

(*
│
│          Multiplying by the base makes the lowest digit zero when
│          the base is greater than one.
│
*)

(*                           1<B ⇒ Digit(B,X·B,0)=0                           *)

Lemma digit_at_mul_base_0 :
  forall B X,
    1 < B ->
    digit_at B (X * B) 0 = 0.
Proof.
  intros B X HB.
  unfold digit_at.
  rewrite PC.base_pow_0.
  rewrite N.div_1_r.
  rewrite N.Div0.mod_mul by lia.
  reflexivity.
Qed.

(*
│
│          Above the lowest digit, multiplying by the base shifts the
│          original digits upward.
│
*)

(*                    0<B ⇒ Digit(B,X·B,S t)=Digit(B,X,t)                     *)

Lemma digit_at_mul_base_S :
  forall B X t,
    0 < B ->
    digit_at B (X * B) (S t) = digit_at B X t.
Proof.
  intros B X t Hpos.
  symmetry.
  rewrite <- (digit_at_div_base B (X * B) t Hpos).
  rewrite N.div_mul by (apply (proj2 (N.neq_0_lt_0 B)); exact Hpos).
  reflexivity.
Qed.

(*
│
│          The tail packed variables divide every channel by the
│          packed base, so time `t` in the tail is time `S t` in the
│          original channels.
│
*)

(*                          Tail(p,v).X=⌊X÷base(p)⌋                           *)

Definition packed_vars_tail
    (p : packed_trace_params)
    (v : packed_trace_vars) : packed_trace_vars :=
  {|
    pt_state_ch := pt_state_ch v / pt_base p;
    pt_ip_ch := pt_ip_ch v / pt_base p;
    pt_r1_ch := pt_r1_ch v / pt_base p;
    pt_r2_ch := pt_r2_ch v / pt_base p;
    pt_halt_ch := pt_halt_ch v / pt_base p
  |}.

(*
│
│          Decoded state views commute with the tail operation.
│
*)

(*                   ViewAt(p,Tail(p,v),t)=ViewAt(p,v,S t)                    *)

Lemma packed_state_at_tail :
  forall p v t,
    packed_state_at p (packed_vars_tail p v) t =
    packed_state_at p v (S t).
Proof.
  intros [B horizon cell_bound Hpow Hlt] [state ip r1 r2 halt] t.
  unfold packed_vars_tail, packed_state_at.
  simpl.
  repeat rewrite digit_at_div_base by (apply pow2_positive; exact Hpow).
  reflexivity.
Qed.

(*
│
│          A packed channel still reads the original stream at
│          successor time after dividing the channel by the base.
│
*)

(*          PacksChannel(B,H,x,X) ∧ S t<H ⇒ Digit(B,⌊X÷B⌋,t)=x(S t)           *)

Lemma packs_channel_tail_upto :
  forall B horizon xs X t,
    0 < B ->
    packs_channel B horizon xs X ->
    (S t < horizon)%nat ->
    digit_at B (X / B) t = xs (S t).
Proof.
  intros B horizon xs X t Hpos Hpack Ht.
  rewrite digit_at_div_base by exact Hpos.
  apply Hpack.
  exact Ht.
Qed.

(*
│
│          If a packed valuation packs a trace, its tail view at time
│          `t` matches the trace at time `S t`.
│
*)

(*     PacksTrace(p,v,tr) ∧ S t<H ⇒ ViewAt(p,Tail(p,v),t) matches tr(S t)     *)

Lemma packs_trace_tail_at :
  forall p v tr t,
    packs_trace p v tr ->
    (S t < pt_horizon p)%nat ->
    state_view_matches_code
      (packed_state_at p (packed_vars_tail p v) t)
      (tr (S t)).
Proof.
  intros p v tr t Hpack Ht.
  rewrite packed_state_at_tail.
  apply Hpack.
  exact Ht.
Qed.

(*
│
│          A packed trace supplies both the current decoded view and
│          the successor decoded tail view.
│
*)

(* PacksTrace ∧ S t<H ⇒ ViewAt(t) matches tr(t) ∧ TailView(t) matches tr(S t) *)

Lemma packed_adjacent_views_correct :
  forall p v tr t,
    packs_trace p v tr ->
    (S t < pt_horizon p)%nat ->
    state_view_matches_code (packed_state_at p v t) (tr t) /\
    state_view_matches_code
      (packed_state_at p (packed_vars_tail p v) t)
      (tr (S t)).
Proof.
  intros p v tr t Hpack Ht.
  split.
  - apply Hpack.
    lia.
  - apply packs_trace_tail_at.
    + exact Hpack.
    + exact Ht.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                           LOCAL VIEW RELATIONS                          ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The initial-view predicate records the initial instruction
│          pointer, input in register one, zero in register two, and a
│          non-halt digit.
│
*)

(*          InitialAt(input,view) ⇔ ip=1 ∧ r₁=input ∧ r₂=0 ∧ halt=0           *)

Definition packed_initial_at (input : N) (view : packed_state_view) : Prop :=
  ps_ip view = 1 /\
  ps_r1 view = input /\
  ps_r2 view = 0 /\
  ps_halt view = 0.

(*
│
│          The halt-view predicate ties the halt digit to the zero
│          instruction pointer convention.
│
*)

(*                       HaltAt(view) ⇔ (halt=1 ↔ ip=0)                       *)

Definition packed_halt_at (view : packed_state_view) : Prop :=
  ps_halt view = 1 <-> ps_ip view = 0.

(*
│
│          The state-code range predicate bounds the decoded full
│          state field.
│
*)

(*                        StateRange(b,view) ⇔ state<b                        *)

Definition packed_state_range (bound : N) (view : packed_state_view) : Prop :=
  ps_state view < bound.

(*
│
│          The instruction-pointer range predicate bounds the decoded
│          instruction pointer field.
│
*)

(*                           IpRange(b,view) ⇔ ip<b                           *)

Definition packed_ip_range (bound : N) (view : packed_state_view) : Prop :=
  ps_ip view < bound.

(*
│
│          The register range predicate bounds both decoded register
│          fields.
│
*)

(*                 RegisterRange(b₁,b₂,view) ⇔ r₁<b₁ ∧ r₂<b₂                  *)

Definition packed_register_range
    (r1_bound r2_bound : N) (view : packed_state_view) : Prop :=
  ps_r1 view < r1_bound /\ ps_r2 view < r2_bound.

(*
│
│          The halt range predicate bounds the decoded halt digit.
│
*)

(*                         HaltRange(b,view) ⇔ halt<b                         *)

Definition packed_halt_range (bound : N) (view : packed_state_view) : Prop :=
  ps_halt view < bound.

(*
│
│          A packed Boolean digit is any digit below two.
│
*)

(*                             BoolDigit(x) ⇔ x<2                             *)

Definition packed_boolean_digit (x : N) : Prop :=
  x < 2.

(*
│
│          A packed Boolean channel is a channel whose every
│          in-horizon digit is below two.
│
*)

(*               BoolChannel(p,X) ⇔ ∀ t<H. Digit(base(p),X,t)<2               *)

Definition packed_boolean_channel_pred
    (p : packed_trace_params) (X : N) : Prop :=
  packed_boolean_channel p 2 X.

(*
│
│          Reading a machine counter from a packed view selects
│          register one or register two.
│
*)

(*                   Read(Counter₁)=r₁ ∧ Read(Counter₂)=r₂                    *)

Definition packed_read_counter
    (c : MS.MachineCounter) (view : packed_state_view) : N :=
  match c with
  | Counter1 => ps_r1 view
  | Counter2 => ps_r2 view
  end.

(*
│
│          The source instruction-pointer predicate says the decoded
│          instruction pointer equals a concrete instruction index.
│
*)

(*                          IpMatches(q,view) ⇔ ip=q                          *)

Definition packed_ip_matches_at (q : nat) (view : packed_state_view) : Prop :=
  ps_ip view = N.of_nat q.

(*
│
│          The target instruction-pointer predicate has the same local
│          shape, used for successor views.
│
*)

(*                       TargetIpMatches(q,view) ⇔ ip=q                       *)

Definition packed_target_ip_matches_at
    (q : nat) (view : packed_state_view) : Prop :=
  ps_ip view = N.of_nat q.

(*
│
│          The counter-zero predicate reads the selected decoded
│          register and checks that it is zero.
│
*)

(*                    CounterZero(c,view) ⇔ Read(c,view)=0                    *)

Definition packed_counter_zero_at
    (c : MS.MachineCounter) (view : packed_state_view) : Prop :=
  packed_read_counter c view = 0.

(*
│
│          The counter-successor predicate compares a selected decoded
│          register between the current and tail views.
│
*)

(*           CounterSucc(c,view,tail) ⇔ Read(c,tail)=Read(c,view)+1           *)

Definition packed_counter_succ_at
    (c : MS.MachineCounter)
    (view tail_view : packed_state_view) : Prop :=
  packed_read_counter c tail_view = N.succ (packed_read_counter c view).

(*
│
│          A decoded view matching the initial encoded state satisfies
│          the packed initial-view predicate.
│
*)

(*          ViewMatches(view,code) ∧ current(code)=Initial(input) ⇒           *)
(*                           InitialAt(input,view)                            *)

Lemma state_view_matches_code_initial_at :
  forall view code input,
    state_view_matches_code view code ->
    MS.current_state code = initial_state input ->
    packed_initial_at (N.of_nat input) view.
Proof.
  intros view code input Hmatch Hinit.
  destruct Hmatch as (_ & Hip & Hr1 & Hr2 & Hhalt).
  unfold packed_initial_at.
  pose proof (MS.initial_state_components input) as (Hip0 & Hr10 & Hr20).
  rewrite Hinit in Hip, Hr1, Hr2.
  repeat split.
  - rewrite Hip0 in Hip.
    exact Hip.
  - rewrite Hr10 in Hr1.
    exact Hr1.
  - rewrite Hr20 in Hr2.
    exact Hr2.
  - rewrite Hhalt.
    unfold PC.halt_digit_of_code.
    unfold MS.halted_code_b, MS.halted_state_b.
    rewrite Hinit.
    rewrite Hip0.
    reflexivity.
Qed.

(*
│
│          Any decoded view matching an encoded state satisfies the
│          packed halt convention.
│
*)

(*                   ViewMatches(view,code) ⇒ HaltAt(view)                    *)

Lemma state_view_matches_code_halt_at :
  forall view code,
    state_view_matches_code view code ->
    packed_halt_at view.
Proof.
  intros view code Hmatch.
  destruct Hmatch as (_ & Hip & _ & _ & Hhalt).
  unfold packed_halt_at.
  split.
  - intro H.
    rewrite Hhalt in H.
    unfold PC.halt_digit_of_code in H.
    destruct (MS.halted_code_b code) eqn:Hb; simpl in H.
    + rewrite Hip.
      unfold MS.halted_code_b, MS.halted_state_b in Hb.
      apply Nat.eqb_eq in Hb.
      now rewrite Hb.
    + discriminate H.
  - intro H.
    rewrite Hhalt.
    unfold PC.halt_digit_of_code.
    assert (Hb : MS.halted_code_b code = true).
    {
      unfold MS.halted_code_b, MS.halted_state_b.
      apply Nat.eqb_eq.
      rewrite Hip in H.
      apply Nat2N.inj.
      simpl.
      exact H.
    }
    now rewrite Hb.
Qed.

(*
│
│          The halt digit of any decoded view matching an encoded
│          state is Boolean.
│
*)

(*               ViewMatches(view,code) ⇒ BoolDigit(halt(view))               *)

Lemma state_view_matches_code_halt_boolean :
  forall view code,
    state_view_matches_code view code ->
    packed_boolean_digit (ps_halt view).
Proof.
  intros view code Hmatch.
  unfold packed_boolean_digit.
  destruct Hmatch as (_ & _ & _ & _ & Hhalt).
  rewrite Hhalt.
  unfold PC.halt_digit_of_code.
  destruct (MS.halted_code_b code); lia.
Qed.

(*
│
│          Matching the same decoded full-state field determines the
│          encoded state code uniquely.
│
*)

(*            ViewMatches(view,c₁) ∧ ViewMatches(view,c₂) ⇒ c₁=c₂             *)

Lemma state_view_matches_code_functional :
  forall view code1 code2,
    state_view_matches_code view code1 ->
    state_view_matches_code view code2 ->
    code1 = code2.
Proof.
  intros view code1 code2 H1 H2.
  destruct H1 as (Hstate1 & _).
  destruct H2 as (Hstate2 & _).
  apply Nat2N.inj.
  rewrite <- Hstate1.
  exact Hstate2.
Qed.

(*
│
│          The local packed source instruction-pointer predicate
│          agrees with the machine-step Boolean observer.
│
*)

(*    ViewMatches(view,code) ⇒ IpMatches(q,view) ⇔ IpMatchesB(q,code)=true    *)

Lemma state_view_matches_code_ip_matches_at :
  forall view code q,
    state_view_matches_code view code ->
    packed_ip_matches_at q view <->
    MS.ip_matches_b q code = true.
Proof.
  intros view code q Hmatch.
  destruct Hmatch as (_ & Hip & _ & _ & _).
  unfold packed_ip_matches_at.
  split.
  - intro H.
    apply (proj2 (MS.ip_matches_b_correct_bridge q code)).
    rewrite Hip in H.
    rewrite MS.current_state_eq in H.
    apply Nat2N.inj in H.
    exact H.
  - intro H.
    apply (proj1 (MS.ip_matches_b_correct_bridge q code)) in H.
    rewrite Hip.
    rewrite MS.current_state_eq.
    now rewrite H.
Qed.

(*
│
│          The local packed target instruction-pointer predicate
│          agrees with the target Boolean observer.
│
*)

(*             ViewMatches(view,code) ⇒ TargetIpMatches(q,view) ⇔             *)
(*                       TargetIpMatchesB(q,code)=true                        *)

Lemma state_view_matches_code_target_ip_matches_at :
  forall view code q,
    state_view_matches_code view code ->
    packed_target_ip_matches_at q view <->
    MS.target_ip_matches_b q code = true.
Proof.
  intros view code q Hmatch.
  destruct Hmatch as (_ & Hip & _ & _ & _).
  unfold packed_target_ip_matches_at.
  split.
  - intro H.
    apply (proj2 (MS.target_ip_matches_b_correct_bridge q code)).
    rewrite Hip in H.
    rewrite MS.current_state_eq in H.
    apply Nat2N.inj in H.
    exact H.
  - intro H.
    apply (proj1 (MS.target_ip_matches_b_correct_bridge q code)) in H.
    rewrite Hip.
    rewrite MS.current_state_eq.
    now rewrite H.
Qed.

(*
│
│          The local packed counter-zero predicate agrees with the
│          corresponding Boolean counter observer.
│
*)

(*  ViewMatches(view,code) ⇒ CounterZero(c,view) ⇔ CounterZeroB(c,code)=true  *)

Lemma state_view_matches_code_counter_zero_at :
  forall c view code,
    state_view_matches_code view code ->
    packed_counter_zero_at c view <->
    MS.counter_zero_obs_b c code = true.
Proof.
  intros c view code Hmatch.
  destruct c.
  - destruct Hmatch as (_ & _ & Hr1 & _ & _).
    unfold packed_counter_zero_at, packed_read_counter.
    split.
    + intro H.
      apply (proj2 (MS.counter_zero_obs_b_correct_bridge Counter1 code)).
      apply Nat2N.inj.
      change (N.of_nat (state_r1 (current_state code)) = 0).
      rewrite <- Hr1.
      exact H.
    + intro H.
      apply (proj1 (MS.counter_zero_obs_b_correct_bridge Counter1 code)) in H.
      rewrite <- MS.current_state_eq in H.
      cbn in H.
      rewrite Hr1.
      rewrite MS.current_state_eq.
      cbn.
      now rewrite H.
  - destruct Hmatch as (_ & _ & _ & Hr2 & _).
    unfold packed_counter_zero_at, packed_read_counter.
    split.
    + intro H.
      apply (proj2 (MS.counter_zero_obs_b_correct_bridge Counter2 code)).
      apply Nat2N.inj.
      change (N.of_nat (state_r2 (current_state code)) = 0).
      rewrite <- Hr2.
      exact H.
    + intro H.
      apply (proj1 (MS.counter_zero_obs_b_correct_bridge Counter2 code)) in H.
      rewrite <- MS.current_state_eq in H.
      cbn in H.
      rewrite Hr2.
      rewrite MS.current_state_eq.
      cbn.
      now rewrite H.
Qed.

(*
│
│          The local packed counter-successor predicate agrees with
│          the corresponding Boolean observer across current and tail
│          codes.
│
*)

(*           ViewMatches(view,code) ∧ ViewMatches(tail,tailCode) ⇒            *)
(*       CounterSucc(c,view,tail) ⇔ CounterSuccB(c,code,tailCode)=true        *)

Lemma state_view_matches_codes_counter_succ_at :
  forall c view tail_view code tail_code,
    state_view_matches_code view code ->
    state_view_matches_code tail_view tail_code ->
    packed_counter_succ_at c view tail_view <->
    MS.counter_succ_obs_b c code tail_code = true.
Proof.
  intros c view tail_view code tail_code Hsrc Htail.
  destruct c.
  - destruct Hsrc as (_ & _ & Hr1 & _ & _).
    destruct Htail as (_ & _ & Hr1' & _ & _).
    unfold packed_counter_succ_at, packed_read_counter.
    split.
    + intro H.
      apply (proj2 (MS.counter_succ_obs_b_correct_bridge Counter1 code tail_code)).
      apply Nat2N.inj.
      change
        (N.of_nat (state_r1 (current_state tail_code)) =
         N.of_nat (S (state_r1 (current_state code)))).
      rewrite Nat2N.inj_succ.
      rewrite <- Hr1', <- Hr1.
      exact H.
    + intro H.
      apply (proj1 (MS.counter_succ_obs_b_correct_bridge Counter1 code tail_code)) in H.
      repeat rewrite <- MS.current_state_eq in H.
      cbn in H.
      rewrite Hr1', Hr1.
      repeat rewrite MS.current_state_eq.
      cbn.
      rewrite H.
      rewrite Nat2N.inj_succ.
      reflexivity.
  - destruct Hsrc as (_ & _ & _ & Hr2 & _).
    destruct Htail as (_ & _ & _ & Hr2' & _).
    unfold packed_counter_succ_at, packed_read_counter.
    split.
    + intro H.
      apply (proj2 (MS.counter_succ_obs_b_correct_bridge Counter2 code tail_code)).
      apply Nat2N.inj.
      change
        (N.of_nat (state_r2 (current_state tail_code)) =
         N.of_nat (S (state_r2 (current_state code)))).
      rewrite Nat2N.inj_succ.
      rewrite <- Hr2', <- Hr2.
      exact H.
    + intro H.
      apply (proj1 (MS.counter_succ_obs_b_correct_bridge Counter2 code tail_code)) in H.
      repeat rewrite <- MS.current_state_eq in H.
      cbn in H.
      rewrite Hr2', Hr2.
      repeat rewrite MS.current_state_eq.
      cbn.
      rewrite H.
      rewrite Nat2N.inj_succ.
      reflexivity.
Qed.

(*
│
│          Channelwise digit bounds imply the corresponding local
│          range predicates for any decoded view at an in-horizon
│          time.
│
*)

(*    PackedBounded(p,b,v) ∧ t<H ⇒ StateRange ∧ IpRange ∧ RegisterRange ∧     *)
(*                                 HaltRange                                  *)

Lemma packed_digits_bounded_local_ranges :
  forall p b v t,
    packed_digits_bounded p b v ->
    (t < pt_horizon p)%nat ->
    packed_state_range (pcb_state_bound b) (packed_state_at p v t) /\
    packed_ip_range (pcb_ip_bound b) (packed_state_at p v t) /\
    packed_register_range (pcb_r1_bound b) (pcb_r2_bound b) (packed_state_at p v t) /\
    packed_halt_range (pcb_halt_bound b) (packed_state_at p v t).
Proof.
  intros p b v t (Hstate & Hip & Hr1 & Hr2 & Hhalt) Ht.
  split.
  - unfold packed_state_range, packed_state_at.
    exact (Hstate t Ht).
  - split.
    + unfold packed_ip_range, packed_state_at.
      exact (Hip t Ht).
    + split.
      * unfold packed_register_range, packed_state_at.
        split.
        -- exact (Hr1 t Ht).
        -- exact (Hr2 t Ht).
      * unfold packed_halt_range, packed_state_at.
        exact (Hhalt t Ht).
Qed.

(*
│
│          Well-formed packed mask constraints imply the same local
│          range predicates by the mask-correctness theorem from
│          P002₀₇.
│
*)

(*   BoundsWF ∧ PackedMasks ∧ t<H ⇒ StateRange ∧ IpRange ∧ RegisterRange ∧    *)
(*                                 HaltRange                                  *)

Lemma packed_masks_imply_local_ranges :
  forall p b v t,
    channel_bounds_wf p b ->
    packed_mask_constraints p b v ->
    (t < pt_horizon p)%nat ->
    packed_state_range (pcb_state_bound b) (packed_state_at p v t) /\
    packed_ip_range (pcb_ip_bound b) (packed_state_at p v t) /\
    packed_register_range (pcb_r1_bound b) (pcb_r2_bound b) (packed_state_at p v t) /\
    packed_halt_range (pcb_halt_bound b) (packed_state_at p v t).
Proof.
  intros p b v t Hwf Hmask Ht.
  apply packed_digits_bounded_local_ranges.
  - apply (proj1 (PM.packed_mask_constraints_correct p b v Hwf)).
    exact Hmask.
  - exact Ht.
Qed.

(*
│
│          A Boolean channel predicate makes each in-horizon extracted
│          digit a Boolean digit.
│
*)

(*           BoolChannel(p,X) ∧ t<H ⇒ BoolDigit(Digit(base(p),X,t))           *)

Lemma packed_boolean_channel_digit :
  forall p X t,
    packed_boolean_channel_pred p X ->
    (t < pt_horizon p)%nat ->
    packed_boolean_digit (PC.digit_at (pt_base p) X t).
Proof.
  intros p X t Hbool Ht.
  unfold packed_boolean_channel_pred, packed_boolean_digit, packed_boolean_channel in *.
  exact (Hbool t Ht).
Qed.

(*
│
│          A Boolean halt channel makes the halt field of any
│          in-horizon decoded view a Boolean digit.
│
*)

(*       BoolChannel(p,halt(v)) ∧ t<H ⇒ BoolDigit(halt(ViewAt(p,v,t)))        *)

Lemma packed_halt_channel_boolean_at :
  forall p v t,
    packed_boolean_channel_pred p (pt_halt_ch v) ->
    (t < pt_horizon p)%nat ->
    packed_boolean_digit (ps_halt (packed_state_at p v t)).
Proof.
  intros p v t Hbool Ht.
  unfold packed_boolean_digit.
  unfold packed_boolean_channel_pred, packed_boolean_channel in Hbool.
  unfold packed_state_at.
  exact (Hbool t Ht).
Qed.

(*
│
│          If mask bounds force the halt bound below two, packed masks
│          imply Boolean halt digits locally.
│
*)

(*BoundsWF ∧ PackedMasks ∧ haltBound≤2 ∧ t<H ⇒ BoolDigit(halt(ViewAt(p,v,t))) *)

Lemma packed_masks_imply_halt_boolean :
  forall p b v t,
    channel_bounds_wf p b ->
    packed_mask_constraints p b v ->
    pcb_halt_bound b <= 2 ->
    (t < pt_horizon p)%nat ->
    packed_boolean_digit (ps_halt (packed_state_at p v t)).
Proof.
  intros p b v t Hwf Hmask Hbound Ht.
  pose proof (packed_masks_imply_local_ranges p b v t Hwf Hmask Ht)
    as (_ & _ & _ & Hhalt).
  unfold packed_boolean_digit, packed_halt_range in *.
  lia.
Qed.

(*
│
│          A packed trace makes the halt channel Boolean because every
│          halt digit is decoded from an encoded machine state.
│
*)

(*                PacksTrace(p,v,tr) ⇒ BoolChannel(p,halt(v))                 *)

Lemma packs_trace_halt_channel_boolean :
  forall p v tr,
    packs_trace p v tr ->
    packed_boolean_channel_pred p (pt_halt_ch v).
Proof.
  intros p v tr Hpack t Ht.
  unfold packed_boolean_channel_pred, packed_boolean_channel.
  specialize (Hpack t Ht).
  destruct Hpack as (_ & _ & _ & _ & Hhalt).
  unfold packed_state_at in Hhalt.
  simpl in Hhalt.
  rewrite Hhalt.
  apply PC.halt_digit_of_code_bound.
Qed.

(*
│
│          At time zero, a packed trace whose decoded state is the
│          machine initial state satisfies the local initial
│          predicate.
│
*)

(*             PacksTrace ∧ 0<H ∧ current(tr(0))=Initial(input) ⇒             *)
(*                         InitialAt(input,ViewAt(0))                         *)

Lemma packs_trace_initial_at_0 :
  forall p v tr input,
    packs_trace p v tr ->
    (0 < pt_horizon p)%nat ->
    MS.current_state (tr 0%nat) = initial_state input ->
    packed_initial_at (N.of_nat input) (packed_state_at p v 0%nat).
Proof.
  intros p v tr input Hpack Hhorizon Hinit.
  eapply state_view_matches_code_initial_at.
  - apply Hpack.
    exact Hhorizon.
  - exact Hinit.
Qed.

(*
│
│          Every in-horizon view of a packed trace satisfies the local
│          halt convention.
│
*)

(*                    PacksTrace ∧ t<H ⇒ HaltAt(ViewAt(t))                    *)

Lemma packs_trace_halt_at :
  forall p v tr t,
    packs_trace p v tr ->
    (t < pt_horizon p)%nat ->
    packed_halt_at (packed_state_at p v t).
Proof.
  intros p v tr t Hpack Ht.
  apply (state_view_matches_code_halt_at (packed_state_at p v t) (tr t)).
  apply Hpack.
  exact Ht.
Qed.

(*
│
│          The packed local source instruction-pointer predicate
│          agrees with the Boolean observer at any in-horizon trace
│          time.
│
*)

(*    PacksTrace ∧ t<H ⇒ IpMatches(q,ViewAt(t)) ⇔ IpMatchesB(q,tr(t))=true    *)

Lemma packs_trace_ip_matches_at :
  forall p v tr t q,
    packs_trace p v tr ->
    (t < pt_horizon p)%nat ->
    packed_ip_matches_at q (packed_state_at p v t) <->
    MS.ip_matches_b q (tr t) = true.
Proof.
  intros p v tr t q Hpack Ht.
  apply (state_view_matches_code_ip_matches_at (packed_state_at p v t) (tr t) q).
  apply Hpack.
  exact Ht.
Qed.

(*
│
│          The packed local target instruction-pointer predicate
│          agrees with the Boolean observer on the successor tail
│          view.
│
*)

(*           PacksTrace ∧ S t<H ⇒ TargetIpMatches(q,TailView(t)) ⇔            *)
(*                      TargetIpMatchesB(q,tr(S t))=true                      *)

Lemma packs_trace_target_ip_matches_tail :
  forall p v tr t q,
    packs_trace p v tr ->
    (S t < pt_horizon p)%nat ->
    packed_target_ip_matches_at q (packed_state_at p (packed_vars_tail p v) t) <->
    MS.target_ip_matches_b q (tr (S t)) = true.
Proof.
  intros p v tr t q Hpack Ht.
  apply
    (state_view_matches_code_target_ip_matches_at
       (packed_state_at p (packed_vars_tail p v) t) (tr (S t)) q).
  apply packs_trace_tail_at.
  - exact Hpack.
  - exact Ht.
Qed.

(*
│
│          The packed local counter-zero predicate agrees with the
│          Boolean observer at any in-horizon trace time.
│
*)

(*  PacksTrace ∧ t<H ⇒ CounterZero(c,ViewAt(t)) ⇔ CounterZeroB(c,tr(t))=true  *)

Lemma packs_trace_counter_zero_at :
  forall p v tr t c,
    packs_trace p v tr ->
    (t < pt_horizon p)%nat ->
    packed_counter_zero_at c (packed_state_at p v t) <->
    MS.counter_zero_obs_b c (tr t) = true.
Proof.
  intros p v tr t c Hpack Ht.
  apply (state_view_matches_code_counter_zero_at c (packed_state_at p v t) (tr t)).
  apply Hpack.
  exact Ht.
Qed.

(*
│
│          The packed local counter-successor predicate agrees with
│          the Boolean observer across the current view and successor
│          tail view.
│
*)

(*        PacksTrace ∧ S t<H ⇒ CounterSucc(c,ViewAt(t),TailView(t)) ⇔         *)
(*                     CounterSuccB(c,tr(t),tr(S t))=true                     *)

Lemma packs_trace_counter_succ_tail :
  forall p v tr t c,
    packs_trace p v tr ->
    (S t < pt_horizon p)%nat ->
    packed_counter_succ_at c
      (packed_state_at p v t)
      (packed_state_at p (packed_vars_tail p v) t) <->
    MS.counter_succ_obs_b c (tr t) (tr (S t)) = true.
Proof.
  intros p v tr t c Hpack Ht.
  apply
    (state_view_matches_codes_counter_succ_at
       c
       (packed_state_at p v t)
       (packed_state_at p (packed_vars_tail p v) t)
       (tr t)
       (tr (S t))).
  - apply Hpack.
    lia.
  - apply packs_trace_tail_at.
    + exact Hpack.
    + exact Ht.
Qed.
