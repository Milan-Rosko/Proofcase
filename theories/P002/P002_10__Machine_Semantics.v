(*P002_10__Machine_Semantics.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                    Proofcase / P002_10__Machine_Semantics                    │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This layer sits directly on top of the fixed-witness trace family in
  `P002_09__Trace_Family`.

  Its role is now strictly family-level: expose the open witness-search
  emitter, relate it to the existence of numeric FM trace witnesses, and
  package the internal compiler theorem `compile_fm_family_correct`.

  No single-equation compression appears here. The compiler endpoint of the
  reset P002 project is a finite cubic family, not one aggregated cubic
  instance.

*)

From P002 Require Export P002_09__Trace_Family.
From Stdlib Require Import ClassicalEpsilon ClassicalDescription.

Definition MachineConstraintFamily : Type := TraceConstraintFamily.

Definition FMBoundedTraceSearchPayload
    (prog : MachineProgram) (input bound : nat) : Prop :=
  exists witness fuel,
    witness <= bound /\
    FMFixedTracePayload prog input witness fuel.

Definition emit_bounded_witness_search_family :
  MachineProgram -> nat -> nat -> MachineConstraintFamily :=
  fun prog input bound =>
    match search_FMValidTrace_upto prog input bound with
    | Some witness => emit_trace_family prog input witness
    | None => [emit_false_equation]
    end.

(* Open witness-search layer. For the current salvage route we package it as a
   classical choice of a sufficiently large bound, then reuse the constructive
   bounded search compiler below that bound. This keeps the unbounded endpoint
   honest about where classicality still enters, while factoring all concrete
   witness selection through the primitive-recursive bounded layer. *)

Definition chosen_trace_bound
    (prog : MachineProgram) (input : nat) : nat :=
  epsilon (inhabits 0)
    (fun bound =>
       exists witness, witness <= bound /\ FMValidTrace prog input witness).

(*
│
│          `chosen_trace_bound` is the exact place where the remaining
│          classicality of the unbounded compiler is concentrated. It
│          does not choose a witness directly; it chooses only a
│          numeric budget guaranteed to dominate some valid witness,
│          after which the constructive bounded search layer takes
│          over.
│
*)
(*   chosen\_trace\_bound(prog,input)\;:=\;\varepsilon B.\;\exists W\le B,\   *)
(*                        FMValidTrace(prog,input,W).                         *)

Definition emit_witness_search_family :
  MachineProgram -> nat -> MachineConstraintFamily :=
  fun prog input =>
    if excluded_middle_informative (exists witness, FMValidTrace prog input witness)
    then emit_bounded_witness_search_family prog input (chosen_trace_bound prog input)
    else [emit_false_equation].

(*
│
│          `emit_witness_search_family` is currently realized as a
│          classical choice of a bound large enough to contain some
│          valid witness, followed by the constructive bounded search
│          compiler. This is enough to close the family-level theorem
│          chain cleanly, but it should still be read as an
│          intermediate search-family realization rather than the
│          final syntax-driven unbounded compiler.
│
*)
(*
│
│          `emit_bounded_witness_search_family` is the constructive
│          sibling: given an explicit numeric bound, it performs
│          primitive-recursive search over raw witness numbers and
│          emits the corresponding fixed-witness family if one is
│          found. This is the honest syntax-first search layer
│          currently available in P002.
│
*)

Lemma family_satisfiable_false_equation :
  ~ family_satisfiable [emit_false_equation].
Proof.
  intro Hsat.
  apply family_satisfiable_iff in Hsat.
  destruct Hsat as [rho Hsat].
  apply solves_all_singleton in Hsat.
  exact (emit_false_equation_unsat rho Hsat).
Qed.

Lemma chosen_trace_bound_correct :
  forall prog input,
    (exists witness, FMValidTrace prog input witness) ->
    exists witness,
      witness <= chosen_trace_bound prog input /\
      FMValidTrace prog input witness.
Proof.
  intros prog input Hex.
  unfold chosen_trace_bound.
  apply (epsilon_spec (inhabits 0)
           (fun bound =>
              exists witness,
                witness <= bound /\ FMValidTrace prog input witness)).
  destruct Hex as [witness Hvalid].
  exists witness.
  exists witness.
  split.
  - lia.
  - exact Hvalid.
Qed.

Lemma emit_witness_search_family_wf :
  forall prog input,
    family_wf (emit_witness_search_family prog input).
Proof.
  intros prog input.
  unfold emit_witness_search_family.
  destruct (excluded_middle_informative
              (exists witness : nat, FMValidTrace prog input witness)).
  - unfold emit_bounded_witness_search_family.
    destruct (search_FMValidTrace_upto prog input (chosen_trace_bound prog input))
      as [witness|].
    + apply emit_trace_family_wf.
    + apply family_wf_singleton.
      apply emit_false_equation_wf.
  - apply family_wf_singleton.
    apply emit_false_equation_wf.
Qed.

Lemma emit_bounded_witness_search_family_wf :
  forall prog input bound,
    family_wf (emit_bounded_witness_search_family prog input bound).
Proof.
  intros prog input bound.
  unfold emit_bounded_witness_search_family.
  destruct (search_FMValidTrace_upto prog input bound) as [witness|].
  - apply emit_trace_family_wf.
  - apply family_wf_singleton.
    apply emit_false_equation_wf.
Qed.

Theorem exists_valid_trace_iff_trace_search_payload :
  forall prog input,
    (exists witness, FMValidTrace prog input witness) <->
    FMTraceSearchPayload prog input.
Proof.
  intros prog input.
  unfold FMTraceSearchPayload.
  split.
  - intros [witness Hvalid].
    apply FMValidTrace_iff_exists_fixed_trace_payload in Hvalid.
    destruct Hvalid as [fuel Hpayload].
    exists witness, fuel.
    exact Hpayload.
  - intros [witness [fuel Hpayload]].
    exists witness.
    apply (proj2 (FMValidTrace_iff_exists_fixed_trace_payload prog input witness)).
    exists fuel.
    exact Hpayload.
Qed.

Theorem exists_bounded_valid_trace_iff_bounded_trace_search_payload :
  forall prog input bound,
    (exists witness, witness <= bound /\ FMValidTrace prog input witness) <->
    FMBoundedTraceSearchPayload prog input bound.
Proof.
  intros prog input bound.
  unfold FMBoundedTraceSearchPayload.
  split.
  - intros [witness [Hle Hvalid]].
    apply FMValidTrace_iff_exists_fixed_trace_payload in Hvalid.
    destruct Hvalid as [fuel Hpayload].
    exists witness, fuel.
    split.
    + exact Hle.
    + exact Hpayload.
  - intros [witness [fuel [Hle Hpayload]]].
    exists witness.
    split.
    + exact Hle.
    + apply (proj2 (FMValidTrace_iff_exists_fixed_trace_payload prog input witness)).
      exists fuel.
      exact Hpayload.
Qed.

Theorem witness_search_family_payload_correct :
  forall prog input,
    FMTraceSearchPayload prog input <->
    family_satisfiable (emit_witness_search_family prog input).
Proof.
  intros prog input.
  rewrite <- exists_valid_trace_iff_trace_search_payload.
  unfold emit_witness_search_family, emit_bounded_witness_search_family.
  destruct (excluded_middle_informative
              (exists witness : nat, FMValidTrace prog input witness))
    as [Hex|Hnex].
  - destruct (search_FMValidTrace_upto prog input (chosen_trace_bound prog input))
      as [found|] eqn:Hsearch.
    + split.
      * intros _.
        apply (proj1 (trace_family_correct prog input found)).
        destruct (search_FMValidTrace_upto_sound
                    prog input (chosen_trace_bound prog input) found Hsearch)
          as [_ Hvalid].
        exact Hvalid.
      * intro Hsat.
        exists found.
        destruct (search_FMValidTrace_upto_sound
                    prog input (chosen_trace_bound prog input) found Hsearch)
          as [_ Hvalid].
        exact Hvalid.
    + split.
      * intro Hex'.
        exfalso.
        destruct (chosen_trace_bound_correct prog input Hex)
          as [witness [Hle Hvalid]].
        destruct (search_FMValidTrace_upto_complete
                    prog input (chosen_trace_bound prog input) witness Hle Hvalid)
          as [found [Hfound _]].
        rewrite Hsearch in Hfound.
        discriminate.
      * intro Hsat.
        exfalso.
        apply family_satisfiable_false_equation.
        exact Hsat.
  - split.
    + intro Hex'.
      exfalso.
      apply Hnex.
      exact Hex'.
    + intro Hsat.
      exfalso.
      apply family_satisfiable_false_equation.
      exact Hsat.
Qed.

Theorem bounded_witness_search_family_payload_correct :
  forall prog input bound,
    FMBoundedTraceSearchPayload prog input bound <->
    family_satisfiable (emit_bounded_witness_search_family prog input bound).
Proof.
  intros prog input bound.
  unfold emit_bounded_witness_search_family.
  destruct (search_FMValidTrace_upto prog input bound) as [witness|] eqn:Hsearch.
  - split.
    + intros _.
      apply (proj1 (trace_family_correct prog input witness)).
      destruct (search_FMValidTrace_upto_sound prog input bound witness Hsearch)
        as [_ Hvalid].
      exact Hvalid.
    + intro Hsat.
      destruct (search_FMValidTrace_upto_sound prog input bound witness Hsearch)
        as [Hle Hvalid].
      apply FMValidTrace_iff_exists_fixed_trace_payload in Hvalid.
      destruct Hvalid as [fuel Hpayload].
      exists witness, fuel.
      split.
      * exact Hle.
      * exact Hpayload.
  - split.
    + intros Hpayload.
      exfalso.
      destruct Hpayload as [witness [fuel [Hle Hfixed]]].
      destruct (search_FMValidTrace_upto_complete prog input bound witness Hle)
        as [found [Hfound _]].
      * apply (proj2 (FMValidTrace_iff_exists_fixed_trace_payload prog input witness)).
        exists fuel.
        exact Hfixed.
      * rewrite Hsearch in Hfound.
        discriminate.
    + intro Hsat.
      exfalso.
      apply family_satisfiable_false_equation.
      exact Hsat.
Qed.

(*
│
│          `witness_search_family_payload_correct` now follows by
│          case-splitting on witness existence and routing through the
│          fixed-witness theorem `trace_family_correct`. The current
│          open emitter is therefore concrete, though still
│          semantically chosen rather than yet syntax-first.
│
*)
(*              FMTraceSearchPayload(prog,input)\Leftrightarrow               *)
(*       cubic\_family\_yes(emit\_witness\_search\_family(prog,input)).       *)
(*
│
│          `bounded_witness_search_family_payload_correct` isolates
│          the constructive search theorem that does not need
│          classical choice: within any explicit bound, the bounded
│          search emitter is satisfiable exactly when some valid FM
│          witness occurs below that bound.
│
*)

Theorem witness_search_family_correct :
  forall prog input,
    (exists witness, FMValidTrace prog input witness) <->
    family_satisfiable (emit_witness_search_family prog input).
Proof.
  intros prog input.
  rewrite exists_valid_trace_iff_trace_search_payload.
  apply witness_search_family_payload_correct.
Qed.

Theorem bounded_witness_search_family_correct :
  forall prog input bound,
    (exists witness, witness <= bound /\ FMValidTrace prog input witness) <->
    family_satisfiable (emit_bounded_witness_search_family prog input bound).
Proof.
  intros prog input bound.
  rewrite exists_bounded_valid_trace_iff_bounded_trace_search_payload.
  apply bounded_witness_search_family_payload_correct.
Qed.

Definition compile_fm_family
    (prog : MachineProgram) (input : nat) : cubic_family_instance :=
  emit_witness_search_family prog input.

Definition compile_fm_family_upto
    (prog : MachineProgram) (input bound : nat) : cubic_family_instance :=
  emit_bounded_witness_search_family prog input bound.

Definition trace_family_yes
    (prog : MachineProgram) (input witness : nat) : Prop :=
  cubic_family_yes (emit_trace_family prog input witness).

Definition compile_fm_family_yes
    (prog : MachineProgram) (input : nat) : Prop :=
  cubic_family_yes (compile_fm_family prog input).

Definition compile_fm_family_upto_yes
    (prog : MachineProgram) (input bound : nat) : Prop :=
  cubic_family_yes (compile_fm_family_upto prog input bound).

(*
│
│          `compile_fm_family` is the honest compiler endpoint
│          exported by the reset project: given an FM program and
│          input, produce the cubic family whose satisfiability is
│          intended to capture one accepting run.
│
*)
(*                     compile\_fm\_family(prog,input) :=                     *)
(*                 emit\_witness\_search\_family(prog,input).                 *)

Lemma compile_fm_family_unfold :
  forall prog input,
    compile_fm_family prog input =
    emit_witness_search_family prog input.
Proof.
  reflexivity.
Qed.

Lemma compile_fm_family_upto_unfold :
  forall prog input bound,
    compile_fm_family_upto prog input bound =
    emit_bounded_witness_search_family prog input bound.
Proof.
  reflexivity.
Qed.

Theorem compile_fm_family_wf :
  forall prog input,
    family_wf (compile_fm_family prog input).
Proof.
  intros prog input.
  rewrite compile_fm_family_unfold.
  apply emit_witness_search_family_wf.
Qed.

Theorem compile_fm_family_upto_wf :
  forall prog input bound,
    family_wf (compile_fm_family_upto prog input bound).
Proof.
  intros prog input bound.
  rewrite compile_fm_family_upto_unfold.
  apply emit_bounded_witness_search_family_wf.
Qed.

Theorem compile_fm_family_correct :
  forall prog input,
    (exists witness, FMValidTrace prog input witness) <->
    cubic_family_yes (compile_fm_family prog input).
Proof.
  intros prog input.
  rewrite compile_fm_family_unfold.
  unfold family_satisfiable.
  apply witness_search_family_correct.
Qed.

Theorem compile_fm_family_upto_correct :
  forall prog input bound,
    (exists witness, witness <= bound /\ FMValidTrace prog input witness) <->
    cubic_family_yes (compile_fm_family_upto prog input bound).
Proof.
  intros prog input bound.
  rewrite compile_fm_family_upto_unfold.
  unfold family_satisfiable.
  apply bounded_witness_search_family_correct.
Qed.

Theorem compile_fm_family_exists_bound_correct :
  forall prog input,
    (exists witness, FMValidTrace prog input witness) <->
    (exists bound, cubic_family_yes (compile_fm_family_upto prog input bound)).
Proof.
  intros prog input.
  split.
  - intros [witness Hvalid].
    exists witness.
    apply compile_fm_family_upto_correct.
    exists witness.
    split.
    + lia.
    + exact Hvalid.
  - intros [bound Hyes].
    apply compile_fm_family_upto_correct in Hyes.
    destruct Hyes as [witness [_ Hvalid]].
    exists witness.
    exact Hvalid.
Qed.

Theorem compile_fm_family_yes_iff_exists_bound :
  forall prog input,
    cubic_family_yes (compile_fm_family prog input) <->
    exists bound, cubic_family_yes (compile_fm_family_upto prog input bound).
Proof.
  intros prog input.
  rewrite <- compile_fm_family_correct.
  apply compile_fm_family_exists_bound_correct.
Qed.

(*
│
│          `compile_fm_family_correct` is the new internal north star
│          of P002: explicit FM witnesses exist exactly when the
│          emitted cubic family is satisfiable. Every later
│          Σ₁-completeness statement should factor through this
│          theorem, not through any single-equation compression claim.
│
*)
(*           \exists W,\ FMValidTrace(prog,input,W)\Leftrightarrow            *)
(*            cubic\_family\_yes(compile\_fm\_family(prog,input)).            *)
(*
│
│          `compile_fm_family_upto_correct` is the constructive
│          approximation to the open search theorem. It is completely
│          syntax-driven: below any explicit bound, compilation and
│          satisfiability exactly match bounded FM witness existence,
│          with no appeal to classical witness choice.
│
*)
(*
│
│          `compile_fm_family_exists_bound_correct` isolates the
│          remaining unbounded step cleanly: unbounded FM witness
│          existence is already equivalent to the existence of some
│          satisfiable bounded compiled family. What remains classical
│          in `compile_fm_family_correct` is therefore only the
│          collapse of that outer existential over bounds into one
│          open family instance.
│
*)
(*
│
│          This theorem is the architectural hinge between the
│          constructive and classical halves of reset P002. It says
│          the syntax-driven bounded compiler is already extensionally
│          complete for raw FM witness existence; the unbounded
│          endpoint only packages the outer existential over bounds
│          into one family-valued map.
│
*)
(*     \exists W,\ FMValidTrace(prog,input,W)\Leftrightarrow \exists B,\      *)
(*        cubic\_family\_yes(compile\_fm\_family\_upto(prog,input,B)).        *)
(*
│
│          `compile_fm_family_yes_iff_exists_bound` is the same
│          factorization stated directly at the family-satisfiability
│          layer. It is the cleanest summary of the current
│          architecture: the unbounded compiled family adds no new
│          satisfiable instances beyond the bounded constructive core;
│          it only hides the outer bound existential behind one
│          classical wrapper.
│
*)
