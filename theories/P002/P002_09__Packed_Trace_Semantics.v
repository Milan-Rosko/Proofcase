(*P002_09__Packed_Trace_Semantics.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                 Proofcase / P002_09__Packed_Trace_Semantics                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This layer packages packed trace semantics: a packed current view and tail
  view are related by the existing FM step relation, and fixed packed
  channels realize one finite encoded witness trace.

  The file remains semantic only. It does not emit polynomial families or
  terminal target equations; it bridges fixed-channel packed traces to
  `StepRelation`, `CodeTraceWitness`, and `FMValidTrace`.

*)

(*
│
│          This layer uses lists for finite code traces, binary
│          naturals for packed digits, and linear arithmetic for
│          horizon bounds.
│
*)

(*                              List ∧ ℕ₂ ∧ lia                               *)

From Stdlib Require Import List NArith Lia.

(*
│
│          Packed trace semantics consumes the witness-family core,
│          the packed channel codec, and the local packed-view
│          semantics.
│
*)

(*                     P002₀₃ ∧ P002₀₇ ∧ P002₀₈ → P002₀₉                      *)

From P002 Require Import P002_03__Witness_Family_Core.
From P002 Require Import P002_07__Packed_Carryless_Masks.
From P002 Require Import P002_08__Packed_Local_Semantics.

Module MS := P002_02__Machine_Step.
Module TW := P002_03__Witness_Family_Core.
Module PC := P002_07__Packed_Carryless_Masks.
Module PL := P002_08__Packed_Local_Semantics.

Local Notation CodeTrace := TW.CodeTrace.
Local Notation packed_trace_params := PC.packed_trace_params.
Local Notation packed_trace_vars := PC.packed_trace_vars.
Local Notation packed_state_at := PC.packed_state_at.
Local Notation packed_vars_tail := PL.packed_vars_tail.
Local Notation state_view_matches_code := PC.state_view_matches_code.
Local Notation packs_trace := PC.packs_trace.
Local Notation pt_horizon := PC.pt_horizon.
Local Notation ps_state := PC.ps_state.
Local Notation ps_halt := PC.ps_halt.
Local Notation encode_code_trace := TW.encode_code_trace.
Local Notation decode_code_trace := TW.decode_code_trace.
Local Notation start_code := TW.start_code.
Local Notation CodeTraceStartsWith := TW.CodeTraceStartsWith.
Local Notation CodeTraceWitness := TW.CodeTraceWitness.
Local Notation ValidCodeTrace := TW.ValidCodeTrace.
Local Notation FMValidTrace := TW.FMValidTrace.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                      PACKED MACHINE STEP SEMANTICS                      ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          A packed step at time `t` says the current packed view and
│          tail packed view decode to state codes linked by the
│          existing FM step relation.
│
*)

(*     PackedStepAt(p,v,prog,t) ⇔ ∃ c c'. ViewAt(t)=c ∧ TailView(t)=c' ∧      *)
(*                          StepRelation(prog,c,c')                           *)

Definition packed_step_at
    (p : packed_trace_params)
    (v : packed_trace_vars)
    (prog : MS.MachineProgram)
    (t : nat) : Prop :=
  exists code code',
    state_view_matches_code (packed_state_at p v t) code /\
    state_view_matches_code
      (packed_state_at p (packed_vars_tail p v) t) code' /\
    MS.StepRelation prog code code'.

(*
│
│          All packed steps hold when every adjacent in-horizon time
│          cell satisfies the packed step predicate.
│
*)

(*      PackedAllSteps(p,v,prog) ⇔ ∀ t. S t<H ⇒ PackedStepAt(p,v,prog,t)      *)

Definition packed_all_steps
    (p : packed_trace_params)
    (v : packed_trace_vars)
    (prog : MS.MachineProgram) : Prop :=
  forall t, (S t < pt_horizon p)%nat -> packed_step_at p v prog t.

(*
│
│          A real packed trace plus a concrete FM step induces the
│          corresponding packed-step predicate.
│
*)

(*          PacksTrace ∧ S t<H ∧ StepRelation(prog,tr(t),tr(S t)) ⇒           *)
(*                          PackedStepAt(p,v,prog,t)                          *)

Lemma packed_step_at_of_trace :
  forall p v prog tr t,
    packs_trace p v tr ->
    (S t < pt_horizon p)%nat ->
    MS.StepRelation prog (tr t) (tr (S t)) ->
    packed_step_at p v prog t.
Proof.
  intros p v prog tr t Hpack Ht Hstep.
  exists (tr t), (tr (S t)).
  split.
  - apply Hpack.
    lia.
  - split.
    + apply PL.packs_trace_tail_at.
      * exact Hpack.
      * exact Ht.
    + exact Hstep.
Qed.

(*
│
│          Conversely, a packed-step predicate over a packed trace
│          recovers the concrete FM step between trace cells.
│
*)

(*PacksTrace ∧ S t<H ∧ PackedStepAt(p,v,prog,t) ⇒ StepRelation(prog,tr(t),tr(S*)
(*                                    t))                                     *)

Lemma packed_step_at_to_trace :
  forall p v prog tr t,
    packs_trace p v tr ->
    (S t < pt_horizon p)%nat ->
    packed_step_at p v prog t ->
    MS.StepRelation prog (tr t) (tr (S t)).
Proof.
  intros p v prog tr t Hpack Ht (code & code' & Hview & Htail & Hstep).
  pose proof (PL.packed_adjacent_views_correct p v tr t Hpack Ht)
    as (Hview_tr & Htail_tr).
  pose proof
    (PL.state_view_matches_code_functional
       (packed_state_at p v t) (tr t) code Hview_tr Hview)
    as Hcode.
  pose proof
    (PL.state_view_matches_code_functional
       (packed_state_at p (packed_vars_tail p v) t) (tr (S t)) code' Htail_tr Htail)
    as Hcode'.
  rewrite Hcode.
  rewrite Hcode'.
  exact Hstep.
Qed.

(*
│
│          For a fixed packed trace, the all-steps predicate is
│          equivalent to the ordinary step relation at every adjacent
│          trace pair.
│
*)

(*PacksTrace ⇒ PackedAllSteps ⇔ ∀ t. S t<H ⇒ StepRelation(prog,tr(t),tr(S t)) *)

Theorem packed_all_steps_correct_for_trace :
  forall p v prog tr,
    packs_trace p v tr ->
    packed_all_steps p v prog <->
    forall t,
      (S t < pt_horizon p)%nat ->
      MS.StepRelation prog (tr t) (tr (S t)).
Proof.
  intros p v prog tr Hpack.
  split.
  - intros Hall t Ht.
    apply (packed_step_at_to_trace p v prog tr t Hpack Ht).
    apply Hall.
    exact Ht.
  - intros Hsteps t Ht.
    apply (packed_step_at_of_trace p v prog tr t Hpack Ht).
    apply Hsteps.
    exact Ht.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                      PACKED TRACE WITNESS SEMANTICS                     ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The stream view of a finite code trace reads `nth t tr 0`,
│          using zero as the out-of-range default.
│
*)

(*                       TraceStream(tr,t)=nth(t,tr,0)                        *)

Definition code_trace_stream (tr : CodeTrace) : nat -> MS.EncodedState :=
  fun t => nth t tr 0.

(*
│
│          The last-code view of a finite code trace uses zero as the
│          default for the empty trace.
│
*)

(*                          TraceLast(tr)=last(tr,0)                          *)

Definition code_trace_last (tr : CodeTrace) : MS.EncodedState :=
  last tr 0.

(*
│
│          A packed trace starts with the input when the decoded
│          state-code field at time zero is the designated start code.
│
*)

(*        PackedStarts(p,v,input) ⇔ state(ViewAt(0))=StartCode(input)         *)

Definition packed_starts_with_input
    (p : packed_trace_params)
    (v : packed_trace_vars)
    (input : nat) : Prop :=
  ps_state (packed_state_at p v 0%nat) = N.of_nat (start_code input).

(*
│
│          A packed trace finishes halted when the halt digit at the
│          predecessor of the horizon is one.
│
*)

(*                PackedFinishes(p,v) ⇔ halt(ViewAt(pred H))=1                *)

Definition packed_finishes_halted
    (p : packed_trace_params)
    (v : packed_trace_vars) : Prop :=
  ps_halt (packed_state_at p v (Nat.pred (pt_horizon p))) = 1%N.

(*
│
│          Packed trace semantics ties one finite code trace to the
│          packed channels: nonempty horizon, matching length, packed
│          digits, start, all steps, and final halt.
│
*)

(*PackedTraceSem ⇔ 0<H ∧ len(tr)=H ∧ PacksTrace ∧ Starts ∧ AllSteps ∧ Finishes*)

Definition packed_trace_sem
    (p : packed_trace_params)
    (v : packed_trace_vars)
    (prog : MS.MachineProgram)
    (input : nat)
    (tr : CodeTrace) : Prop :=
  (0 < pt_horizon p)%nat /\
  length tr = pt_horizon p /\
  packs_trace p v (code_trace_stream tr) /\
  packed_starts_with_input p v input /\
  packed_all_steps p v prog /\
  packed_finishes_halted p v.

(*
│
│          Packed witness semantics applies packed trace semantics to
│          the decoded witness and requires the witness to be
│          canonically encoded from that decoded trace.
│
*)

(*     PackedWitnessSem ⇔ PackedTraceSem(decode(w)) ∧ w=encode(decode(w))     *)

Definition packed_trace_witness_sem
    (p : packed_trace_params)
    (v : packed_trace_vars)
    (prog : MS.MachineProgram)
    (input witness : nat) : Prop :=
  packed_trace_sem p v prog input (decode_code_trace witness) /\
  witness = encode_code_trace (decode_code_trace witness).

(*
│
│          Starting with an input is equivalent to a nonempty code
│          trace whose zeroth stream value is the designated start
│          code.
│
*)

(* CodeTraceStartsWith(input,tr) ⇔ tr≠[] ∧ TraceStream(tr,0)=StartCode(input) *)

Lemma CodeTraceStartsWith_iff_stream0 :
  forall input tr,
    CodeTraceStartsWith input tr <->
    tr <> [] /\ code_trace_stream tr 0%nat = start_code input.
Proof.
  intros input [|s rest]; simpl.
  - split; intro H.
    + contradiction.
    + destruct H as [Hneq _].
      contradiction.
  - split.
    + intro H.
      split.
      * discriminate.
      * exact H.
    + intros [_ H].
      exact H.
Qed.

(*
│
│          For a nonempty finite trace, the stream value at the
│          predecessor of its length is the list's last code.
│
*)

(*            tr≠[] ⇒ TraceStream(tr,pred(len(tr)))=TraceLast(tr)             *)

Lemma code_trace_last_stream :
  forall tr,
    tr <> [] ->
    code_trace_stream tr (Nat.pred (length tr)) = code_trace_last tr.
Proof.
  induction tr as [|x tr IH]; intros Hneq.
  - contradiction.
  - destruct tr as [|y ys].
    + reflexivity.
    + simpl.
      apply IH.
      discriminate.
Qed.

(*
│
│          A true halted-code Boolean gives halt digit one.
│
*)

(*                 HaltedCodeB(code)=true ⇒ HaltDigit(code)=1                 *)

Lemma halt_digit_of_code_true :
  forall code,
    MS.halted_code_b code = true ->
    PC.halt_digit_of_code code = 1%N.
Proof.
  intros code Hhalt.
  unfold PC.halt_digit_of_code.
  now rewrite Hhalt.
Qed.

(*
│
│          Conversely, halt digit one forces the halted-code Boolean
│          to be true.
│
*)

(*                 HaltDigit(code)=1 ⇒ HaltedCodeB(code)=true                 *)

Lemma halt_digit_of_code_eq_1 :
  forall code,
    PC.halt_digit_of_code code = 1%N ->
    MS.halted_code_b code = true.
Proof.
  intros code.
  unfold PC.halt_digit_of_code.
  destruct (MS.halted_code_b code); simpl; intro H; try discriminate; reflexivity.
Qed.

(*
│
│          A valid code trace is exactly a nonempty trace whose
│          adjacent cells step correctly and whose last code is
│          halted.
│
*)

(*           ValidCodeTrace(prog,tr) ⇔ tr≠[] ∧ (∀ t. S t<len(tr) ⇒            *)
(*         StepRelation(prog,trₜ,trₜ₊₁)) ∧ HaltedCodeB(last(tr))=true         *)

Lemma ValidCodeTrace_iff_steps_and_halt :
  forall prog tr,
    ValidCodeTrace prog tr <->
    tr <> [] /\
    (forall t, (S t < length tr)%nat ->
       MS.StepRelation prog (code_trace_stream tr t)
         (code_trace_stream tr (S t))) /\
    MS.halted_code_b (code_trace_last tr) = true.
Proof.
  intros prog tr.
  induction tr as [|s1 tr IH]; simpl.
  - split; intro H.
    + contradiction.
    + destruct H as [Hneq _].
      contradiction.
  - destruct tr as [|s2 rest].
    + split.
      * intro Hvalid.
        repeat split.
        -- discriminate.
        -- intros t Ht.
           destruct t; simpl in Ht; lia.
        -- apply MS.halted_code_b_correct.
           exact Hvalid.
      * intros (_ & _ & Hhalt).
        apply MS.halted_code_b_correct in Hhalt.
        exact Hhalt.
    + split.
      * intro Hvalid.
        apply TW.ValidCodeTrace_cons in Hvalid.
        destruct Hvalid as [Hstep Htail].
        pose proof (proj1 IH Htail) as (Hneq_tail & Hsteps_tail & Hhalt_tail).
        repeat split.
        -- discriminate.
        -- intros [|t] Ht.
           ++ unfold MS.StepRelation.
              exact Hstep.
           ++ simpl.
              apply Hsteps_tail.
              lia.
        -- exact Hhalt_tail.
      * intros (Hneq & Hsteps & Hhalt).
        apply TW.ValidCodeTrace_cons.
        split.
        -- specialize (Hsteps 0%nat).
           assert (H01 : (S 0 < length (s1 :: s2 :: rest))%nat).
           { simpl. lia. }
           specialize (Hsteps H01).
           unfold code_trace_stream in Hsteps.
           simpl in Hsteps.
           unfold MS.StepRelation in Hsteps.
           exact Hsteps.
        -- apply (proj2 IH).
           repeat split.
           ++ discriminate.
           ++ intros t Ht.
              specialize (Hsteps (S t)).
              assert (HSS : (S (S t) < length (s1 :: s2 :: rest))%nat).
              {
                simpl in Ht |- *.
                assert (Hle : S t <= length rest) by lia.
                lia.
              }
              specialize (Hsteps HSS).
              unfold code_trace_stream in Hsteps.
              simpl in Hsteps.
              exact Hsteps.
           ++ exact Hhalt.
Qed.

(*
│
│          If packed semantics finishes halted, the last code of the
│          realized finite trace is halted.
│
*)

(*              0<H ∧ len(tr)=H ∧ PacksTrace ∧ PackedFinishes ⇒               *)
(*                      HaltedCodeB(TraceLast(tr))=true                       *)

Lemma packed_finishes_halted_implies_last_halt :
  forall p v tr,
    (0 < pt_horizon p)%nat ->
    length tr = pt_horizon p ->
    packs_trace p v (code_trace_stream tr) ->
    packed_finishes_halted p v ->
    MS.halted_code_b (code_trace_last tr) = true.
Proof.
  intros p v tr Hhorizon Hlen Hpack Hhalt.
  assert (Hneq : tr <> []).
  {
    intro Hnil.
    subst tr.
    simpl in Hlen.
    lia.
  }
  assert (Hlast : (Nat.pred (pt_horizon p) < pt_horizon p)%nat) by lia.
  specialize (Hpack (Nat.pred (pt_horizon p)) Hlast).
  unfold PC.packs_state_at, PC.state_view_matches_code, packed_finishes_halted,
    packed_state_at in *.
  simpl in Hpack.
  destruct Hpack as (_ & _ & _ & _ & Hhalt_digit).
  apply halt_digit_of_code_eq_1.
  rewrite <- (code_trace_last_stream tr Hneq).
  rewrite Hlen.
  rewrite <- Hhalt_digit.
  exact Hhalt.
Qed.

(*
│
│          If the last realized code is halted, the packed final halt
│          digit is one.
│
*)

(*      0<H ∧ len(tr)=H ∧ PacksTrace ∧ HaltedCodeB(TraceLast(tr))=true ⇒      *)
(*                               PackedFinishes                               *)

Lemma packed_finishes_halted_of_last_halt :
  forall p v tr,
    (0 < pt_horizon p)%nat ->
    length tr = pt_horizon p ->
    packs_trace p v (code_trace_stream tr) ->
    MS.halted_code_b (code_trace_last tr) = true ->
    packed_finishes_halted p v.
Proof.
  intros p v tr Hhorizon Hlen Hpack Hhalt.
  assert (Hneq : tr <> []).
  {
    intro Hnil.
    subst tr.
    simpl in Hlen.
    lia.
  }
  assert (Hlast : (Nat.pred (pt_horizon p) < pt_horizon p)%nat) by lia.
  specialize (Hpack (Nat.pred (pt_horizon p)) Hlast).
  unfold PC.packs_state_at, PC.state_view_matches_code, packed_finishes_halted,
    packed_state_at in *.
  simpl in Hpack.
  destruct Hpack as (_ & _ & _ & _ & Hhalt_digit).
  rewrite Hhalt_digit.
  apply halt_digit_of_code_true.
  rewrite <- Hlen.
  rewrite code_trace_last_stream by exact Hneq.
  exact Hhalt.
Qed.

(*
│
│          Packed trace semantics is equivalent to ordinary finite
│          code-trace validity plus the fixed-channel realization of
│          that trace.
│
*)

(*           PackedTraceSem(p,v,prog,input,tr) ⇔ Starts(input,tr) ∧           *)
(*          ValidCodeTrace(prog,tr) ∧ len(tr)=H ∧ PacksTrace(p,v,tr)          *)

Theorem packed_trace_sem_correct :
  forall p v prog input tr,
    packed_trace_sem p v prog input tr <->
    CodeTraceStartsWith input tr /\
    ValidCodeTrace prog tr /\
    length tr = pt_horizon p /\
    packs_trace p v (code_trace_stream tr).
Proof.
  intros p v prog input tr.
  split.
  - intros (Hhorizon & Hlen & Hpack & Hstart & Hall & Hhalt).
    split.
    + apply (proj2 (CodeTraceStartsWith_iff_stream0 input tr)).
      split.
      * intro Hnil.
        subst tr.
        simpl in Hlen.
        lia.
      * specialize (Hpack 0%nat Hhorizon).
        unfold PC.packs_state_at, PC.state_view_matches_code, packed_starts_with_input,
          packed_state_at in *.
        simpl in Hpack.
        destruct Hpack as (Hstate & _).
        apply Nat2N.inj.
        rewrite <- Hstate.
        exact Hstart.
    + split.
      * apply (proj2 (ValidCodeTrace_iff_steps_and_halt prog tr)).
        split.
        -- intro Hnil.
           subst tr.
           simpl in Hlen.
           lia.
        -- split.
           ++ pose proof
                (proj1
                   (packed_all_steps_correct_for_trace
                      p v prog (code_trace_stream tr) Hpack) Hall)
                as Hsteps.
              intros t Ht.
              rewrite Hlen in Ht.
              apply Hsteps.
              exact Ht.
           ++ eapply packed_finishes_halted_implies_last_halt.
              ** exact Hhorizon.
              ** exact Hlen.
              ** exact Hpack.
              ** exact Hhalt.
      * split.
        -- exact Hlen.
        -- exact Hpack.
  - intros (Hstart & Hvalid & Hlen & Hpack).
    pose proof (proj1 (CodeTraceStartsWith_iff_stream0 input tr) Hstart)
      as (Hneq & Hstream0).
    pose proof (proj1 (ValidCodeTrace_iff_steps_and_halt prog tr) Hvalid)
      as (_ & Hsteps & Hhalt).
    assert (Hhorizon : (0 < pt_horizon p)%nat).
    {
      rewrite <- Hlen.
      destruct tr as [|s rest].
      - contradiction.
      - simpl.
        lia.
    }
    split.
    + exact Hhorizon.
    + split.
      * exact Hlen.
      * split.
        -- exact Hpack.
        -- split.
           ++ unfold packed_starts_with_input.
              unfold packed_state_at.
              simpl.
              pose proof (Hpack 0%nat Hhorizon) as Hpack0.
              unfold PC.packs_state_at, PC.state_view_matches_code, packed_state_at in Hpack0.
              simpl in Hpack0.
              destruct Hpack0 as (Hstate & _).
              rewrite Hstate.
              now rewrite Hstream0.
           ++ split.
              ** apply
                   (proj2
                      (packed_all_steps_correct_for_trace
                         p v prog (code_trace_stream tr) Hpack)).
                 intros t Ht.
                 rewrite <- Hlen in Ht.
                 apply Hsteps.
                 exact Ht.
              ** eapply packed_finishes_halted_of_last_halt.
                 --- exact Hhorizon.
                 --- exact Hlen.
                 --- exact Hpack.
                 --- exact Hhalt.
Qed.

(*
│
│          Packed witness semantics is equivalent to
│          `CodeTraceWitness` plus horizon length and packed-channel
│          realization of the decoded trace.
│
*)

(*   PackedWitnessSem(p,v,prog,input,w) ⇔ CodeTraceWitness(prog,input,w) ∧    *)
(*                len(decode(w))=H ∧ PacksTrace(p,v,decode(w))                *)

Theorem packed_trace_witness_sem_correct :
  forall p v prog input witness,
    packed_trace_witness_sem p v prog input witness <->
    CodeTraceWitness prog input witness /\
    length (decode_code_trace witness) = pt_horizon p /\
    packs_trace p v (code_trace_stream (decode_code_trace witness)).
Proof.
  intros p v prog input witness.
  split.
  - intros (Hsem & Heq).
    destruct (proj1 (packed_trace_sem_correct p v prog input (decode_code_trace witness)) Hsem)
      as (Hstart & Hvalid & Hlen & Hpack).
    split.
    + exists (decode_code_trace witness).
      repeat split; assumption.
    + split; assumption.
  - intros ((tr & Hstart & Hvalid & Hwitness) & Hlen & Hpack).
    assert (Hdecode : decode_code_trace witness = tr).
    {
      rewrite Hwitness.
      apply TW.decode_code_trace_encode_code_trace.
    }
    split.
    + apply (proj2 (packed_trace_sem_correct p v prog input (decode_code_trace witness))).
      rewrite Hdecode.
      rewrite Hdecode in Hlen, Hpack.
      split.
      * exact Hstart.
      * split.
        -- exact Hvalid.
        -- split.
           ++ exact Hlen.
           ++ exact Hpack.
    + rewrite Hdecode.
      exact Hwitness.
Qed.

(*
│
│          The raw witness theorem replaces `CodeTraceWitness` by the
│          public `FMValidTrace` predicate.
│
*)

(*     PackedWitnessSem(p,v,prog,input,w) ⇔ FMValidTrace(prog,input,w) ∧      *)
(*                len(decode(w))=H ∧ PacksTrace(p,v,decode(w))                *)

Theorem packed_trace_witness_sem_correct_raw :
  forall p v prog input witness,
    packed_trace_witness_sem p v prog input witness <->
    FMValidTrace prog input witness /\
    length (decode_code_trace witness) = pt_horizon p /\
    packs_trace p v (code_trace_stream (decode_code_trace witness)).
Proof.
  intros p v prog input witness.
  split.
  - intros H.
    destruct (proj1 (packed_trace_witness_sem_correct p v prog input witness) H)
      as (Hctw & Hlen & Hpack).
    split.
    + apply (proj2 (TW.FMValidTrace_iff_CodeTraceWitness prog input witness)).
      exact Hctw.
    + split; assumption.
  - intros (Hraw & Hlen & Hpack).
    apply (proj2 (packed_trace_witness_sem_correct p v prog input witness)).
    split.
    + apply (proj1 (TW.FMValidTrace_iff_CodeTraceWitness prog input witness)).
      exact Hraw.
    + split; assumption.
Qed.
