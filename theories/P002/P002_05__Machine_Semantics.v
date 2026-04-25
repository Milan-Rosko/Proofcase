(*P002_05__Machine_Semantics.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                    Proofcase / P002_05__Machine_Semantics                    │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This layer packages bounded witness search and the public cubic-family
  compiler surface.

  The bounded compiler is constructive. The unbounded `compile_fm_family`
  wrapper uses one classical choice of a large enough bound, isolated in
  `chosen_trace_bound`.

*)

(*
│
│          This public semantics layer consumes the fixed-witness
│          trace-family emitter and packages it into bounded and open
│          compiler surfaces.
│
*)

(*                              P002₀₄ → P002₀₅                               *)

From P002 Require Export P002_04__Trace_Family_Emitter.

(*
│
│          The open wrapper uses `epsilon` for a bound and excluded
│          middle to choose whether the open search family should be
│          real or explicitly false.
│
*)

(*          Classical(OpenSearch)=ε ∧ EM; Classical(BoundedSearch)=∅          *)

From Stdlib Require Import ClassicalEpsilon ClassicalDescription.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                       BOUNDED CONSTRUCTIVE SEARCH                       ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The public FM trace predicate is decidable because the
│          executable checker is exact.
│
*)

(*       FMValidTraceB(prog,input,W)=true ⇔ FMValidTrace(prog,input,W)        *)

Theorem FMValidTrace_decidable :
  forall prog input witness,
    {FMValidTrace prog input witness} + {~ FMValidTrace prog input witness}.
Proof.
  intros prog input witness.
  destruct (FMValidTrace_b prog input witness) eqn:Hb.
  - left.
    apply FMValidTrace_b_correct.
    exact Hb.
  - right.
    intro Hvalid.
    apply FMValidTrace_b_correct in Hvalid.
    rewrite Hvalid in Hb.
    discriminate.
Qed.

(*
│
│          Bounded search scans witness numbers from `0` through
│          `bound` and returns the first valid witness it finds, if
│          any.
│
*)

(*                    SearchUpTo(prog,input,B) ∈ option ℕ                     *)

Fixpoint search_FMValidTrace_upto
    (prog : MachineProgram) (input bound : nat) : option nat :=
  match bound with
  | 0 =>
      if FMValidTrace_b prog input 0 then Some 0 else None
  | S bound' =>
      match search_FMValidTrace_upto prog input bound' with
      | Some witness => Some witness
      | None =>
          if FMValidTrace_b prog input (S bound')
          then Some (S bound')
          else None
      end
  end.

(*
│
│          Soundness of bounded search: any returned witness is within
│          the bound and satisfies the FM trace predicate.
│
*)

(*    SearchUpTo(prog,input,B)=Some(W) ⇒ W≤B ∧ FMValidTrace(prog,input,W)     *)

Lemma search_FMValidTrace_upto_sound :
  forall prog input bound witness,
    search_FMValidTrace_upto prog input bound = Some witness ->
    witness <= bound /\
    FMValidTrace prog input witness.
Proof.
  intros prog input bound.
  induction bound as [|bound IH]; intros witness Hsearch; simpl in Hsearch.
  - destruct (FMValidTrace_b prog input 0) eqn:Hb.
    + assert (Hwitness : witness = 0).
      { destruct witness; simpl in Hsearch; [reflexivity|discriminate]. }
      subst witness.
      split.
      * lia.
      * apply FMValidTrace_b_correct.
        exact Hb.
    + discriminate.
  - destruct (search_FMValidTrace_upto prog input bound) as [found|] eqn:Hprev.
    + assert (Hwitness : witness = found).
      { inversion Hsearch. reflexivity. }
      subst witness.
      destruct (IH found eq_refl) as [Hle Hvalid].
      split.
      * lia.
      * exact Hvalid.
    + destruct (FMValidTrace_b prog input (S bound)) eqn:Hb.
      * assert (Hwitness : witness = S bound).
        { destruct witness; simpl in Hsearch; [discriminate|inversion Hsearch; reflexivity]. }
        subst witness.
        split.
        -- lia.
        -- apply FMValidTrace_b_correct.
           exact Hb.
      * discriminate.
Qed.

(*
│
│          Completeness of bounded search: if a valid witness lies
│          within the bound, the search returns some valid witness.
│
*)

(* W≤B ∧ FMValidTrace(prog,input,W) ⇒ ∃ F. SearchUpTo(prog,input,B)=Some(F) ∧ *)
(*                         FMValidTrace(prog,input,F)                         *)

Lemma search_FMValidTrace_upto_complete :
  forall prog input bound witness,
    witness <= bound ->
    FMValidTrace prog input witness ->
    exists found,
      search_FMValidTrace_upto prog input bound = Some found /\
      FMValidTrace prog input found.
Proof.
  intros prog input bound.
  induction bound as [|bound IH]; intros witness Hle Hvalid.
  - assert (witness = 0) by lia.
    subst witness.
    exists 0.
    split.
    + assert (Hb : FMValidTrace_b prog input 0 = true).
      { apply FMValidTrace_b_correct. exact Hvalid. }
      unfold search_FMValidTrace_upto.
      rewrite Hb.
      reflexivity.
    + exact Hvalid.
  - simpl.
    destruct (Nat.eq_dec witness (S bound)) as [Heq|Hneq].
    + subst witness.
      destruct (search_FMValidTrace_upto prog input bound) as [found|] eqn:Hprev.
      * exists found.
        split.
        -- reflexivity.
        -- destruct (search_FMValidTrace_upto_sound prog input bound found Hprev)
             as [_ Hfound].
           exact Hfound.
      * rewrite (proj2 (FMValidTrace_b_correct prog input (S bound))) by exact Hvalid.
        exists (S bound).
        split.
        -- reflexivity.
        -- exact Hvalid.
    + assert (Hlt : witness <= bound) by lia.
      destruct (IH witness Hlt Hvalid) as [found [Hfound Hvalid_found]].
      rewrite Hfound.
      exists found.
      split.
      * reflexivity.
      * exact Hvalid_found.
Qed.

(*
│
│          Existence of any valid witness is equivalent to successful
│          bounded search for some bound.
│
*)

(*∃ W. FMValidTrace(prog,input,W) ⇔ ∃ B F. SearchUpTo(prog,input,B)=Some(F) ∧ *)
(*                         FMValidTrace(prog,input,F)                         *)

Theorem exists_FMValidTrace_iff_bounded_search :
  forall prog input,
    (exists witness, FMValidTrace prog input witness) <->
    (exists bound found,
        search_FMValidTrace_upto prog input bound = Some found /\
        FMValidTrace prog input found).
Proof.
  intros prog input.
  split.
  - intros [witness Hvalid].
    pose proof
      (search_FMValidTrace_upto_complete
         prog input witness witness (Nat.le_refl witness) Hvalid)
      as Hcomplete.
    destruct Hcomplete as [found [Hsearch Hfound]].
    exists witness, found.
    split.
    + exact Hsearch.
    + exact Hfound.
  - intros [bound [found [Hsearch Hvalid]]].
    exists found.
    exact Hvalid.
Qed.

(*
│
│          The bounded payload says that some witness below an
│          explicit bound realizes a fixed trace payload.
│
*)

(*  BoundedPayload(prog,input,B) ⇔ ∃ W T. W≤B ∧ FixedPayload(prog,input,W,T)  *)

Definition FMBoundedTraceSearchPayload
    (prog : MachineProgram) (input bound : nat) : Prop :=
  exists witness fuel,
    witness <= bound /\
    FMFixedTracePayload prog input witness fuel.

(*
│
│          The bounded witness-search family emits the fixed trace
│          family for the found witness, or `FalseEq` when bounded
│          search fails.
│
*)

(*SearchUpTo(prog,input,B)=Some(F) ⇒ BoundedSearchFamily=TraceFamily(F); None *)
(*                  ⇒ BoundedSearchFamily=singleton(FalseEq)                  *)

Definition emit_bounded_witness_search_family :
  MachineProgram -> nat -> nat -> TraceConstraintFamily :=
  fun prog input bound =>
    match search_FMValidTrace_upto prog input bound with
    | Some witness => emit_trace_family prog input witness
    | None => [emit_false_equation]
    end.

(*
│
│          The singleton false-equation family is not satisfiable.
│
*)

(*                           ¬ FamilySat([FalseEq])                           *)

Lemma family_satisfiable_false_equation :
  ~ family_satisfiable [emit_false_equation].
Proof.
  intro Hsat.
  apply family_satisfiable_singleton in Hsat.
  destruct Hsat as [rho Hsolve].
  exact (emit_false_equation_unsat rho Hsolve).
Qed.

(*
│
│          The bounded witness-search family is always well-formed.
│
*)

(*                FamilyWF(BoundedSearchFamily(prog,input,B))                 *)

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

(*
│
│          A bounded valid FM trace exists exactly when a bounded
│          fixed-payload witness exists.
│
*)

(*      ∃ W≤B. FMValidTrace(prog,input,W) ⇔ BoundedPayload(prog,input,B)      *)

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

(*
│
│          The bounded search family is satisfiable exactly when the
│          bounded fixed-payload predicate holds.
│
*)

(*BoundedPayload(prog,input,B) ⇔ FamilySat(BoundedSearchFamily(prog,input,B)) *)

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
│          The constructive bounded search theorem: below an explicit
│          bound, the emitted family is satisfiable exactly when some
│          valid raw FM witness occurs below that bound.
│
*)

(*                    ∃ W≤B. FMValidTrace(prog,input,W) ⇔                     *)
(*                FamilySat(BoundedSearchFamily(prog,input,B))                *)

Theorem bounded_witness_search_family_correct :
  forall prog input bound,
    (exists witness, witness <= bound /\ FMValidTrace prog input witness) <->
    family_satisfiable (emit_bounded_witness_search_family prog input bound).
Proof.
  intros prog input bound.
  rewrite exists_bounded_valid_trace_iff_bounded_trace_search_payload.
  apply bounded_witness_search_family_payload_correct.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                  OPEN SEARCH VIA CLASSICAL BOUND CHOICE                 ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The open payload drops the explicit bound: some witness and
│          fuel realize a fixed trace payload.
│
*)

(*       OpenPayload(prog,input) ⇔ ∃ W T. FixedPayload(prog,input,W,T)        *)

Definition FMTraceSearchPayload
    (prog : MachineProgram) (input : nat) : Prop :=
  exists witness fuel,
    FMFixedTracePayload prog input witness fuel.

(*
│
│          The chosen trace bound is an epsilon-selected bound that
│          contains some valid witness whenever any valid witness
│          exists.
│
*)

(*      ChosenBound(prog,input) ≔ ε B. ∃ W≤B. FMValidTrace(prog,input,W)      *)

Definition chosen_trace_bound
    (prog : MachineProgram) (input : nat) : nat :=
  epsilon (inhabits 0)
    (fun bound =>
       exists witness, witness <= bound /\ FMValidTrace prog input witness).

(*
│
│          The open search family uses excluded middle: if a witness
│          exists, search up to the chosen bound; otherwise emit the
│          explicit false family.
│
*)

(*     WitnessExists ⇒ OpenSearchFamily=BoundedSearchFamily(ChosenBound);     *)
(*            ¬WitnessExists ⇒ OpenSearchFamily=singleton(FalseEq)            *)

Definition emit_witness_search_family :
  MachineProgram -> nat -> TraceConstraintFamily :=
  fun prog input =>
    if excluded_middle_informative (exists witness, FMValidTrace prog input witness)
    then emit_bounded_witness_search_family prog input (chosen_trace_bound prog input)
    else [emit_false_equation].

(*
│
│          Correctness of the chosen bound: under witness existence,
│          some valid witness lies below the selected bound.
│
*)

(*             ∃ W. FMValidTrace(prog,input,W) ⇒ ∃ W≤ChosenBound.             *)
(*                         FMValidTrace(prog,input,W)                         *)

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

(*
│
│          The open witness-search family is always well-formed.
│
*)

(*                   FamilyWF(OpenSearchFamily(prog,input))                   *)

Lemma emit_witness_search_family_wf :
  forall prog input,
    family_wf (emit_witness_search_family prog input).
Proof.
  intros prog input.
  unfold emit_witness_search_family.
  destruct (excluded_middle_informative
              (exists witness : nat, FMValidTrace prog input witness)).
  - apply emit_bounded_witness_search_family_wf.
  - apply family_wf_singleton.
    apply emit_false_equation_wf.
Qed.

(*
│
│          Valid FM trace existence is equivalent to the open
│          fixed-payload predicate.
│
*)

(*         ∃ W. FMValidTrace(prog,input,W) ⇔ OpenPayload(prog,input)          *)

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

(*
│
│          The open search family is satisfiable exactly when the open
│          fixed-payload predicate holds.
│
*)

(*     OpenPayload(prog,input) ⇔ FamilySat(OpenSearchFamily(prog,input))      *)

Theorem witness_search_family_payload_correct :
  forall prog input,
    FMTraceSearchPayload prog input <->
    family_satisfiable (emit_witness_search_family prog input).
Proof.
  intros prog input.
  rewrite <- exists_valid_trace_iff_trace_search_payload.
  unfold emit_witness_search_family.
  destruct (excluded_middle_informative
              (exists witness : nat, FMValidTrace prog input witness))
    as [Hex|Hnex].
  - unfold emit_bounded_witness_search_family.
    destruct (search_FMValidTrace_upto prog input (chosen_trace_bound prog input))
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

(*
│
│          The open witness-search theorem: choose a large enough
│          bound classically, then use bounded constructive search.
│
*)

(* ∃ W. FMValidTrace(prog,input,W) ⇔ FamilySat(OpenSearchFamily(prog,input))  *)

Theorem witness_search_family_correct :
  forall prog input,
    (exists witness, FMValidTrace prog input witness) <->
    family_satisfiable (emit_witness_search_family prog input).
Proof.
  intros prog input.
  rewrite exists_valid_trace_iff_trace_search_payload.
  apply witness_search_family_payload_correct.
Qed.

(*
╔═════════════════════════════════════════════════════════════════════════╗
║                                                                         ║
║                         PUBLIC COMPILER SURFACE                         ║
║                                                                         ║
╚═════════════════════════════════════════════════════════════════════════╝
*)

(*
│
│          The public unbounded compiler is the open witness-search
│          family. Its only classical step is inherited from
│          `emit_witness_search_family`.
│
*)

(*            CompileFM(prog,input) ≔ OpenSearchFamily(prog,input)            *)

Definition compile_fm_family
    (prog : MachineProgram) (input : nat) : cubic_family_instance :=
  emit_witness_search_family prog input.

(*
│
│          The bounded compiler is the constructive bounded
│          witness-search family.
│
*)

(*      CompileFMUpTo(prog,input,B) ≔ BoundedSearchFamily(prog,input,B)       *)

Definition compile_fm_family_upto
    (prog : MachineProgram) (input bound : nat) : cubic_family_instance :=
  emit_bounded_witness_search_family prog input bound.

(*
│
│          The unbounded compiler well-formedness contract says every
│          produced family is well-formed.
│
*)

(*     CompilerWF(compile) ⇔ ∀ prog input. FamilyWF(compile(prog,input))      *)

Definition cubic_machine_compiler_wf
    (compile3 : MachineProgram -> nat -> cubic_family_instance) : Prop :=
  forall prog input,
    family_wf (compile3 prog input).

(*
│
│          The bounded compiler well-formedness contract says every
│          family produced at every explicit bound is well-formed.
│
*)

(* CompilerWFUpTo(compile) ⇔ ∀ prog input B. FamilyWF(compile(prog,input,B))  *)

Definition cubic_machine_compiler_wf_upto
    (compile3 : MachineProgram -> nat -> nat -> cubic_family_instance) : Prop :=
  forall prog input bound,
    family_wf (compile3 prog input bound).

(*
│
│          The unbounded compiler correctness contract equates FM
│          witness existence with satisfiability of the compiled cubic
│          family.
│
*)

(*CompilerCorrect(compile) ⇔ ∀ prog input. (∃ W. FMValidTrace(prog,input,W)) ⇔*)
(*                    CubicFamilyYes(compile(prog,input))                     *)

Definition cubic_machine_compiler_correct
    (compile3 : MachineProgram -> nat -> cubic_family_instance) : Prop :=
  forall prog input,
    (exists witness, FMValidTrace prog input witness) <->
    cubic_family_yes (compile3 prog input).

(*
│
│          The bounded compiler correctness contract equates bounded
│          FM witness existence with satisfiability of the compiled
│          bounded family.
│
*)

(*           CompilerCorrectUpTo(compile) ⇔ ∀ prog input B. (∃ W≤B.           *)
(*    FMValidTrace(prog,input,W)) ⇔ CubicFamilyYes(compile(prog,input,B))     *)

Definition cubic_machine_compiler_correct_upto
    (compile3 : MachineProgram -> nat -> nat -> cubic_family_instance) : Prop :=
  forall prog input bound,
    (exists witness, witness <= bound /\ FMValidTrace prog input witness) <->
    cubic_family_yes (compile3 prog input bound).

(*
│
│          The unbounded combined compiler contract packages
│          well-formedness and correctness.
│
*)

(*CompilerWithWF(compile) ⇔ ∀ prog input. FamilyWF(compile(prog,input)) ∧ ((∃ *)
(*   W. FMValidTrace(prog,input,W)) ⇔ CubicFamilyYes(compile(prog,input)))    *)

Definition cubic_machine_compiler_with_wf
    (compile3 : MachineProgram -> nat -> cubic_family_instance) : Prop :=
  forall prog input,
    family_wf (compile3 prog input) /\
    ((exists witness, FMValidTrace prog input witness) <->
     cubic_family_yes (compile3 prog input)).

(*
│
│          The bounded combined compiler contract packages
│          well-formedness and bounded correctness.
│
*)

(*               CompilerUpToWithWF(compile) ⇔ ∀ prog input B.                *)
(*  FamilyWF(compile(prog,input,B)) ∧ ((∃ W≤B. FMValidTrace(prog,input,W)) ⇔  *)
(*                   CubicFamilyYes(compile(prog,input,B)))                   *)

Definition cubic_machine_compiler_upto_with_wf
    (compile3 : MachineProgram -> nat -> nat -> cubic_family_instance) : Prop :=
  forall prog input bound,
    family_wf (compile3 prog input bound) /\
    ((exists witness, witness <= bound /\ FMValidTrace prog input witness) <->
     cubic_family_yes (compile3 prog input bound)).

(*
│
│          The public unbounded compiler produces well-formed
│          families.
│
*)

(*                      FamilyWF(CompileFM(prog,input))                       *)

Theorem compile_fm_family_wf :
  forall prog input,
    family_wf (compile_fm_family prog input).
Proof.
  intros prog input.
  apply emit_witness_search_family_wf.
Qed.

(*
│
│          The public bounded compiler produces well-formed families.
│
*)

(*                   FamilyWF(CompileFMUpTo(prog,input,B))                    *)

Theorem compile_fm_family_upto_wf :
  forall prog input bound,
    family_wf (compile_fm_family_upto prog input bound).
Proof.
  intros prog input bound.
  apply emit_bounded_witness_search_family_wf.
Qed.

(*
│
│          The public unbounded compiler is correct: FM witness
│          existence is equivalent to satisfiability of the emitted
│          cubic family.
│
*)

(*  ∃ W. FMValidTrace(prog,input,W) ⇔ CubicFamilyYes(CompileFM(prog,input))   *)

Theorem compile_fm_family_correct :
  forall prog input,
    (exists witness, FMValidTrace prog input witness) <->
    cubic_family_yes (compile_fm_family prog input).
Proof.
  intros prog input.
  apply witness_search_family_correct.
Qed.

(*
│
│          The public bounded compiler is correct below an explicit
│          bound.
│
*)

(*                    ∃ W≤B. FMValidTrace(prog,input,W) ⇔                     *)
(*                CubicFamilyYes(CompileFMUpTo(prog,input,B))                 *)

Theorem compile_fm_family_upto_correct :
  forall prog input bound,
    (exists witness, witness <= bound /\ FMValidTrace prog input witness) <->
    cubic_family_yes (compile_fm_family_upto prog input bound).
Proof.
  intros prog input bound.
  apply bounded_witness_search_family_correct.
Qed.

(*
│
│          FM witness existence is equivalent to satisfiability of the
│          bounded compiler for some explicit bound.
│
*)

(*                   ∃ W. FMValidTrace(prog,input,W) ⇔ ∃ B.                   *)
(*                CubicFamilyYes(CompileFMUpTo(prog,input,B))                 *)

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

(*
│
│          The public unbounded compiler satisfies the well-formedness
│          contract.
│
*)

(*                           CompilerWF(CompileFM)                            *)

Theorem compile_fm_family_meets_wf_contract :
  cubic_machine_compiler_wf compile_fm_family.
Proof.
  exact compile_fm_family_wf.
Qed.

(*
│
│          The public bounded compiler satisfies the bounded
│          well-formedness contract.
│
*)

(*                       CompilerWFUpTo(CompileFMUpTo)                        *)

Theorem compile_fm_family_upto_meets_wf_contract :
  cubic_machine_compiler_wf_upto compile_fm_family_upto.
Proof.
  exact compile_fm_family_upto_wf.
Qed.

(*
│
│          The public unbounded compiler satisfies the correctness
│          contract.
│
*)

(*                         CompilerCorrect(CompileFM)                         *)

Theorem compile_fm_family_meets_contract :
  cubic_machine_compiler_correct compile_fm_family.
Proof.
  exact compile_fm_family_correct.
Qed.

(*
│
│          The public bounded compiler satisfies the bounded
│          correctness contract.
│
*)

(*                     CompilerCorrectUpTo(CompileFMUpTo)                     *)

Theorem compile_fm_family_upto_meets_contract :
  cubic_machine_compiler_correct_upto compile_fm_family_upto.
Proof.
  exact compile_fm_family_upto_correct.
Qed.

(*
│
│          The public unbounded compiler satisfies the combined
│          contract.
│
*)

(*                         CompilerWithWF(CompileFM)                          *)

Theorem compile_fm_family_meets_contract_with_wf :
  cubic_machine_compiler_with_wf compile_fm_family.
Proof.
  intros prog input.
  split.
  - apply compile_fm_family_wf.
  - apply compile_fm_family_correct.
Qed.

(*
│
│          The public bounded compiler satisfies the combined bounded
│          contract.
│
*)

(*                     CompilerUpToWithWF(CompileFMUpTo)                      *)

Theorem compile_fm_family_upto_meets_contract_with_wf :
  cubic_machine_compiler_upto_with_wf compile_fm_family_upto.
Proof.
  intros prog input bound.
  split.
  - apply compile_fm_family_upto_wf.
  - apply compile_fm_family_upto_correct.
Qed.

(*
│
│          The unbounded combined contract projects to the unbounded
│          well-formedness contract.
│
*)

(*               CompilerWithWF(compile) ⇒ CompilerWF(compile)                *)

Lemma cubic_machine_compiler_with_wf_wf :
  forall compile3,
    cubic_machine_compiler_with_wf compile3 ->
    cubic_machine_compiler_wf compile3.
Proof.
  intros compile3 Hcontract prog input.
  exact (proj1 (Hcontract prog input)).
Qed.

(*
│
│          The unbounded combined contract projects to the unbounded
│          correctness contract.
│
*)

(*             CompilerWithWF(compile) ⇒ CompilerCorrect(compile)             *)

Lemma cubic_machine_compiler_with_wf_correct :
  forall compile3,
    cubic_machine_compiler_with_wf compile3 ->
    cubic_machine_compiler_correct compile3.
Proof.
  intros compile3 Hcontract prog input.
  exact (proj2 (Hcontract prog input)).
Qed.

(*
│
│          The bounded combined contract projects to the bounded
│          well-formedness contract.
│
*)

(*           CompilerUpToWithWF(compile) ⇒ CompilerWFUpTo(compile)            *)

Lemma cubic_machine_compiler_upto_with_wf_wf :
  forall compile3,
    cubic_machine_compiler_upto_with_wf compile3 ->
    cubic_machine_compiler_wf_upto compile3.
Proof.
  intros compile3 Hcontract prog input bound.
  exact (proj1 (Hcontract prog input bound)).
Qed.

(*
│
│          The bounded combined contract projects to the bounded
│          correctness contract.
│
*)

(*         CompilerUpToWithWF(compile) ⇒ CompilerCorrectUpTo(compile)         *)

Lemma cubic_machine_compiler_upto_with_wf_correct :
  forall compile3,
    cubic_machine_compiler_upto_with_wf compile3 ->
    cubic_machine_compiler_correct_upto compile3.
Proof.
  intros compile3 Hcontract prog input bound.
  exact (proj2 (Hcontract prog input bound)).
Qed.
