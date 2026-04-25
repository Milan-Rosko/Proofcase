(*D001_08__Universality.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / D001_08__Universality                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file records the machine-level universality targets together with a
  concrete subtraction example.

  At the instruction level, the Iterant already contains the target
  two-counter Minsky kernel, so compilation into Iterant ROM is the identity;
  the real coding work lies in the band-encoded state architecture.

*)

From D001 Require Export D001_07__Step_Arithmetization.

(*
│
│          `compile_program` is the identity translation because the
│          Iterant instruction set is already the target two-counter
│          Minsky kernel.
│
*)

Definition compile_program (prog : program) : program := prog.

Theorem compile_program_identity :
  forall prog,
    compile_program prog = prog.
Proof.
  intro prog.
  reflexivity.
Qed.

(*
│
│          `AbstractConfig` and `abstract_step` define the
│          stripped-down Minsky reference semantics for the Iterant
│          instruction set. They forget the Zeckendorf coding and
│          expose only the control-flow triple `(IP, R1, R2)`.
│
*)
(*             abstract_step(prog, (ip, r₁, r₂), (ip', r₁', r₂'))             *)
(*   is the abstract one-step transition induced by the ROM instruction at    *)
(*                               address `ip`.                                *)

Definition AbstractConfig : Type := (nat * nat * nat)%type.

Definition config_to_state (cfg : AbstractConfig) : IterantState :=
  match cfg with
  | (ip, r1, r2) => Build_IterantState ip r1 r2
  end.

Definition state_to_config (st : IterantState) : AbstractConfig :=
  (state_ip st, state_r1 st, state_r2 st).

Definition maps_to (cfg : AbstractConfig) (st : IterantState) : Prop :=
  match cfg with
  | (ip, r1, r2) =>
      state_ip st = ip /\
      state_r1 st = r1 /\
      state_r2 st = r2
  end.

Definition abstract_halted (cfg : AbstractConfig) : Prop :=
  match cfg with
  | (ip, _, _) => ip = 0
  end.

Definition abstract_well_formed_of (L : MachineLimits) (cfg : AbstractConfig) : Prop :=
  match cfg with
  | (ip, r1, r2) =>
      ip < ip_limit_of L /\
      r1 < r1_limit_of L /\
      r2 < r2_limit_of L
  end.

Inductive abstract_step (prog : program) : AbstractConfig -> AbstractConfig -> Prop :=
| abstract_step_halted :
    forall r1 r2,
      abstract_step prog (0, r1, r2) (0, r1, r2)
| abstract_step_inc_counter1 :
    forall ip r1 r2 next_ip,
      nth_error prog (S ip) = Some (INC Counter1 next_ip) ->
      abstract_step prog (S ip, r1, r2) (next_ip, S r1, r2)
| abstract_step_inc_counter2 :
    forall ip r1 r2 next_ip,
      nth_error prog (S ip) = Some (INC Counter2 next_ip) ->
      abstract_step prog (S ip, r1, r2) (next_ip, r1, S r2)
| abstract_step_jzdec_counter1_zero :
    forall ip r2 zero_ip dec_ip,
      nth_error prog (S ip) = Some (JZDEC Counter1 zero_ip dec_ip) ->
      abstract_step prog (S ip, 0, r2) (zero_ip, 0, r2)
| abstract_step_jzdec_counter1_succ :
    forall ip r1 r2 zero_ip dec_ip,
      nth_error prog (S ip) = Some (JZDEC Counter1 zero_ip dec_ip) ->
      abstract_step prog (S ip, S r1, r2) (dec_ip, r1, r2)
| abstract_step_jzdec_counter2_zero :
    forall ip r1 zero_ip dec_ip,
      nth_error prog (S ip) = Some (JZDEC Counter2 zero_ip dec_ip) ->
      abstract_step prog (S ip, r1, 0) (zero_ip, r1, 0)
| abstract_step_jzdec_counter2_succ :
    forall ip r1 r2 zero_ip dec_ip,
      nth_error prog (S ip) = Some (JZDEC Counter2 zero_ip dec_ip) ->
      abstract_step prog (S ip, r1, S r2) (dec_ip, r1, r2)
| abstract_step_halt_instruction :
    forall ip r1 r2,
      nth_error prog (S ip) = Some HALT ->
      abstract_step prog (S ip, r1, r2) (0, r1, r2)
| abstract_step_missing_instruction :
    forall ip r1 r2,
      nth_error prog (S ip) = None ->
      abstract_step prog (S ip, r1, r2) (0, r1, r2).

Lemma maps_to_config_to_state :
  forall cfg,
    maps_to cfg (config_to_state cfg).
Proof.
  intros [[ip r1] r2].
  repeat split; reflexivity.
Qed.

Lemma maps_to_state_to_config :
  forall st,
    maps_to (state_to_config st) st.
Proof.
  intros [ip r1 r2].
  repeat split; reflexivity.
Qed.

Lemma state_to_config_config_to_state :
  forall cfg,
    state_to_config (config_to_state cfg) = cfg.
Proof.
  intros [[ip r1] r2].
  reflexivity.
Qed.

Lemma config_to_state_state_to_config :
  forall st,
    config_to_state (state_to_config st) = st.
Proof.
  intros [ip r1 r2].
  reflexivity.
Qed.

(*
│
│          `abstract_well_formed_of_config_to_state` is the
│          bookkeeping bridge for limit invariants. Once a
│          `MachineLimits` package has been fixed, the abstract `(IP,
│          R1, R2)` view and the structured Iterant state carry
│          exactly the same boundedness information.
│
*)
(*     abstract_well_formed_of(L, (ip, r₁, r₂)) ⇔ state_well_formed_of(L,     *)
(*                      config_to_state((ip, r₁, r₂))).                       *)

Lemma abstract_well_formed_of_config_to_state :
  forall L cfg,
    abstract_well_formed_of L cfg <->
    state_well_formed_of L (config_to_state cfg).
Proof.
  intros L [[ip r1] r2].
  reflexivity.
Qed.

Theorem abstract_step_sound :
  forall prog cfg cfg',
    abstract_step prog cfg cfg' ->
    step_state prog (config_to_state cfg) = config_to_state cfg'.
Proof.
  intros prog cfg cfg' Hstep.
  inversion Hstep; subst; unfold step_state; simpl.
  - reflexivity.
  - replace
      (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := r2 |})
      with (Some (INC Counter1 next_ip))
      by (unfold fetch_instruction; simpl; symmetry; exact H).
    reflexivity.
  - replace
      (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := r2 |})
      with (Some (INC Counter2 next_ip))
      by (unfold fetch_instruction; simpl; symmetry; exact H).
    reflexivity.
  - replace
      (fetch_instruction prog {| state_ip := S ip; state_r1 := 0; state_r2 := r2 |})
      with (Some (JZDEC Counter1 zero_ip dec_ip))
      by (unfold fetch_instruction; simpl; symmetry; exact H).
    reflexivity.
  - replace
      (fetch_instruction prog {| state_ip := S ip; state_r1 := S r1; state_r2 := r2 |})
      with (Some (JZDEC Counter1 zero_ip dec_ip))
      by (unfold fetch_instruction; simpl; symmetry; exact H).
    reflexivity.
  - replace
      (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := 0 |})
      with (Some (JZDEC Counter2 zero_ip dec_ip))
      by (unfold fetch_instruction; simpl; symmetry; exact H).
    reflexivity.
  - replace
      (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := S r2 |})
      with (Some (JZDEC Counter2 zero_ip dec_ip))
      by (unfold fetch_instruction; simpl; symmetry; exact H).
    reflexivity.
  - replace
      (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := r2 |})
      with (Some HALT)
      by (unfold fetch_instruction; simpl; symmetry; exact H).
    reflexivity.
  - replace
      (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := r2 |})
      with (None : option instruction)
      by (unfold fetch_instruction; simpl; symmetry; exact H).
    reflexivity.
Qed.

Theorem abstract_step_complete :
  forall prog cfg,
    abstract_step prog cfg (state_to_config (step_state prog (config_to_state cfg))).
Proof.
  intros prog [[ip r1] r2].
  destruct ip as [|ip].
  - unfold step_state.
    simpl.
    apply abstract_step_halted.
  - unfold step_state.
    simpl.
    destruct (nth_error prog (S ip)) as [instr|] eqn:Hfetch.
    + destruct instr as [c next_ip | c zero_ip dec_ip |].
      * destruct c.
        -- replace
             (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := r2 |})
             with (Some (INC Counter1 next_ip))
             by (unfold fetch_instruction; simpl; symmetry; exact Hfetch).
           simpl.
           change (abstract_step prog (S ip, r1, r2) (next_ip, S r1, r2)).
           apply abstract_step_inc_counter1.
           exact Hfetch.
        -- replace
             (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := r2 |})
             with (Some (INC Counter2 next_ip))
             by (unfold fetch_instruction; simpl; symmetry; exact Hfetch).
           simpl.
           change (abstract_step prog (S ip, r1, r2) (next_ip, r1, S r2)).
           apply abstract_step_inc_counter2.
           exact Hfetch.
      * destruct c.
        -- destruct r1 as [|r1].
           ++ replace
                (fetch_instruction prog {| state_ip := S ip; state_r1 := 0; state_r2 := r2 |})
                with (Some (JZDEC Counter1 zero_ip dec_ip))
                by (unfold fetch_instruction; simpl; symmetry; exact Hfetch).
              simpl.
              change (abstract_step prog (S ip, 0, r2) (zero_ip, 0, r2)).
              eapply abstract_step_jzdec_counter1_zero.
              exact Hfetch.
           ++ replace
                (fetch_instruction prog {| state_ip := S ip; state_r1 := S r1; state_r2 := r2 |})
                with (Some (JZDEC Counter1 zero_ip dec_ip))
                by (unfold fetch_instruction; simpl; symmetry; exact Hfetch).
              simpl.
              change (abstract_step prog (S ip, S r1, r2) (dec_ip, r1, r2)).
              eapply abstract_step_jzdec_counter1_succ.
              exact Hfetch.
        -- destruct r2 as [|r2].
           ++ replace
                (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := 0 |})
                with (Some (JZDEC Counter2 zero_ip dec_ip))
                by (unfold fetch_instruction; simpl; symmetry; exact Hfetch).
              simpl.
              change (abstract_step prog (S ip, r1, 0) (zero_ip, r1, 0)).
              eapply abstract_step_jzdec_counter2_zero.
              exact Hfetch.
           ++ replace
                (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := S r2 |})
                with (Some (JZDEC Counter2 zero_ip dec_ip))
                by (unfold fetch_instruction; simpl; symmetry; exact Hfetch).
              simpl.
              change (abstract_step prog (S ip, r1, S r2) (dec_ip, r1, r2)).
              eapply abstract_step_jzdec_counter2_succ.
              exact Hfetch.
      * replace
          (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := r2 |})
          with (Some HALT)
          by (unfold fetch_instruction; simpl; symmetry; exact Hfetch).
        simpl.
        change (abstract_step prog (S ip, r1, r2) (0, r1, r2)).
        apply abstract_step_halt_instruction.
        exact Hfetch.
    + replace
        (fetch_instruction prog {| state_ip := S ip; state_r1 := r1; state_r2 := r2 |})
        with (None : option instruction)
        by (unfold fetch_instruction; simpl; symmetry; exact Hfetch).
      simpl.
      change (abstract_step prog (S ip, r1, r2) (0, r1, r2)).
      apply abstract_step_missing_instruction.
      exact Hfetch.
Qed.

(*
│
│          `abstract_step_iff_step_state` packages the soundness and
│          completeness bridge between the stripped abstract semantics
│          and the structured Iterant transition function, while
│          `Iterant_simulates_abstract` transports the same fact to
│          any mapped state.
│
*)
(*    abstract_step(prog, c, c') ⇔ step_state(prog, config_to_state(c)) =     *)
(*                            config_to_state(c').                            *)

Corollary abstract_step_iff_step_state :
  forall prog cfg cfg',
    abstract_step prog cfg cfg' <->
    step_state prog (config_to_state cfg) = config_to_state cfg'.
Proof.
  intros prog cfg cfg'.
  split.
  - apply abstract_step_sound.
  - intro Hstep.
    pose proof (f_equal state_to_config Hstep) as Hcfg.
    rewrite state_to_config_config_to_state in Hcfg.
    rewrite <- Hcfg.
    apply abstract_step_complete.
Qed.

Corollary abstract_step_total :
  forall prog cfg,
    exists cfg', abstract_step prog cfg cfg'.
Proof.
  intros prog cfg.
  exists (state_to_config (step_state prog (config_to_state cfg))).
  apply abstract_step_complete.
Qed.

Corollary abstract_step_functional :
  forall prog cfg cfg1 cfg2,
    abstract_step prog cfg cfg1 ->
    abstract_step prog cfg cfg2 ->
    cfg1 = cfg2.
Proof.
  intros prog cfg cfg1 cfg2 H1 H2.
  apply abstract_step_sound in H1.
  apply abstract_step_sound in H2.
  rewrite H1 in H2.
  apply (f_equal state_to_config) in H2.
  repeat rewrite state_to_config_config_to_state in H2.
  exact H2.
Qed.

Theorem Iterant_simulates_abstract :
  forall prog cfg cfg' st,
    abstract_step prog cfg cfg' ->
    maps_to cfg st ->
    step_state prog st = config_to_state cfg'.
Proof.
  intros prog cfg cfg' [ip r1 r2] Hstep Hmap.
  destruct cfg as [[q a] b].
  simpl in Hmap.
  destruct Hmap as [Hip [Hr1 Hr2]].
  subst.
  exact (abstract_step_sound prog (q, a, b) cfg' Hstep).
Qed.

(*
│
│          The universality target is phrased as a Σ₁-completeness
│          obligation: every recursively enumerable language in the
│          chosen meta-framework should be realized by some compiled
│          Iterant program.
│
*)
(*      MachineComputes(prog, L) ≔ ∀ n, MachineAccepts(prog, n) ⇔ L(n).       *)

Definition MachineAccepts : program -> nat -> Prop :=
  halts_on_input.

Definition MachineComputes (prog : program) (L : nat -> Prop) : Prop :=
  forall n, MachineAccepts prog n <-> L n.

Definition Sigma1CompletenessTarget
    (RELanguage : (nat -> Prop) -> Prop) : Prop :=
  forall L,
    RELanguage L ->
    exists prog, MachineComputes (compile_program prog) L.

Definition CubicCompilerReady (prog : program) : Prop :=
  forall s t,
    step_relation prog s t <-> stepb prog s t = true.

(*
│
│          `MachineAccepts_compile_program_iff` is the first
│          identity-compilation lemma: acceptance may be stated either
│          before or after compilation without changing meaning.
│
*)
(*MachineAccepts(compile_program(prog), input) ⇔ MachineAccepts(prog, input). *)

Lemma MachineAccepts_compile_program_iff :
  forall prog input,
    MachineAccepts (compile_program prog) input <->
    MachineAccepts prog input.
Proof.
  intros prog input.
  unfold MachineAccepts, compile_program.
  tauto.
Qed.

(*
│
│          `MachineComputes_compile_program_iff` lifts the same
│          identity-compilation fact from single inputs to whole
│          semantic specifications.
│
*)
(*   MachineComputes(compile_program(prog), L) ⇔ MachineComputes(prog, L).    *)

Lemma MachineComputes_compile_program_iff :
  forall prog L,
    MachineComputes (compile_program prog) L <->
    MachineComputes prog L.
Proof.
  intros prog L.
  unfold MachineComputes, compile_program.
  tauto.
Qed.

(*
│
│          `Sigma1CompletenessTarget_identity_iff` collapses the
│          machine-level target to the uncompiled semantics, because
│          `compile_program` is presently the identity.
│
*)
(*    Sigma1CompletenessTarget(RELanguage) ⇔ ∀ L, RELanguage(L) → ∃ prog,     *)
(*                         MachineComputes(prog, L).                          *)

Lemma Sigma1CompletenessTarget_identity_iff :
  forall RELanguage,
    Sigma1CompletenessTarget RELanguage <->
    forall L,
      RELanguage L ->
      exists prog, MachineComputes prog L.
Proof.
  intros RELanguage.
  split; intros Htarget L HL.
  - destruct (Htarget L HL) as [prog Hprog].
    exists prog.
    apply (proj1 (MachineComputes_compile_program_iff prog L)).
    exact Hprog.
  - destruct (Htarget L HL) as [prog Hprog].
    exists prog.
    apply (proj2 (MachineComputes_compile_program_iff prog L)).
    exact Hprog.
Qed.

Theorem cubic_compiler_ready_of_stepb :
  forall prog,
    CubicCompilerReady prog.
Proof.
  intros prog s t.
  rewrite stepb_correct.
  tauto.
Qed.

Lemma CubicCompilerReady_compile_program :
  forall prog,
    CubicCompilerReady (compile_program prog).
Proof.
  intro prog.
  unfold compile_program.
  exact (cubic_compiler_ready_of_stepb prog).
Qed.

(*
│
│          `run_steps` is the finite-iteration operator for
│          `step_state`. It is the execution-level object used in the
│          worked example and the natural bridge from local step
│          simulation to compiler-level correctness statements.
│
*)
(*                        run_steps(prog, 0, st) = st                         *)
(*run_steps(prog, fuel + 1, st) = run_steps(prog, fuel, step_state(prog, st)).*)

Fixpoint run_steps (prog : program) (fuel : nat) (st : IterantState) : IterantState :=
  match fuel with
  | 0 => st
  | S fuel' => run_steps prog fuel' (step_state prog st)
  end.

Lemma run_steps_S :
  forall prog fuel st,
    run_steps prog (S fuel) st = run_steps prog fuel (step_state prog st).
Proof.
  reflexivity.
Qed.

Lemma run_steps_plus :
  forall prog a b st,
    run_steps prog (a + b) st = run_steps prog b (run_steps prog a st).
Proof.
  intros prog a.
  induction a as [|a IH]; intros b st.
  - simpl. reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

(*
│
│          `run_steps_halted_fixed` records the inertness of halting:
│          once a run reaches a halted state, further iteration leaves
│          it unchanged.
│
*)

Lemma run_steps_halted_fixed :
  forall prog fuel st,
    halted_state st ->
    run_steps prog fuel st = st.
Proof.
  intros prog fuel st Hhalt.
  induction fuel as [|fuel IH].
  - reflexivity.
  - rewrite run_steps_S.
    rewrite halted_state_fixed by exact Hhalt.
    exact IH.
Qed.

(*
│
│          `run_respects_limits` is the hidden invariant that makes
│          the family semantics honest. It says that one chosen
│          `MachineLimits` package is wide enough for every prefix of
│          the run, so later encoded-state and decode/encode lemmas
│          may be applied at each time step without changing the
│          machine.
│
*)
(*run_respects_limits(L, prog, fuel, st) ≡ ∀ k ≤ fuel, state_well_formed_of(L,*)
(*                          run_steps(prog, k, st)).                          *)

Definition run_respects_limits
    (L : MachineLimits) (prog : program) (fuel : nat) (st : IterantState) : Prop :=
  forall k,
    k <= fuel ->
    state_well_formed_of L (run_steps prog k st).

(*
│
│          `FamilyMachineAccepts` is the first honest asymptotic
│          acceptance notion for the band-parameterized machine
│          family: there must exist a sufficiently large
│          `MachineLimits` package whose windows accommodate the whole
│          halting run.
│
*)
(*FamilyMachineAccepts(prog, input) ⇔ ∃ L, fuel, run_respects_limits(L, prog, *)
(*      fuel, initial_state(input)) ∧ halted_state(run_steps(prog, fuel,      *)
(*                          initial_state(input))).                           *)

Definition FamilyMachineAccepts (prog : program) (input : nat) : Prop :=
  exists L fuel,
    run_respects_limits L prog fuel (initial_state input) /\
    halted_state (run_steps prog fuel (initial_state input)).

(*
│
│          `FamilyRawTraceWitness` is the internalized numeric witness
│          format for the same family semantics. Instead of
│          quantifying over a Coq list of states, it asks for one
│          natural-number witness whose coded-list structure follows
│          `NextState_of L`.
│
*)
(*                 FamilyRawTraceWitness(L, prog, input, w) ⇔                 *)
(*             raw_trace_witness_from(NextState_of(L, prog), c ↦              *)
(*          halted_state(decode_state_of(L, c)), encode_state_of(L,           *)
(*                         initial_state(input)), w).                         *)

Definition FamilyRawTraceWitness
    (L : MachineLimits) (prog : program) (input witness : nat) : Prop :=
  raw_trace_witness_from
      (NextState_of L prog)
      (fun c => halted_state (decode_state_of L c))
      (encode_state_of L (initial_state input))
      witness.

Definition FamilyMachineComputes (prog : program) (Lang : nat -> Prop) : Prop :=
  forall n, FamilyMachineAccepts prog n <-> Lang n.

Definition FamilySigma1CompletenessTarget
    (RELanguage : (nat -> Prop) -> Prop) : Prop :=
  forall Lang,
    RELanguage Lang ->
    exists prog, FamilyMachineComputes (compile_program prog) Lang.

Lemma run_respects_limits_initial :
  forall L prog fuel st,
    run_respects_limits L prog fuel st ->
    state_well_formed_of L st.
Proof.
  intros L prog fuel st Hrun.
  specialize (Hrun 0).
  assert (0 <= fuel) by lia.
  exact (Hrun H).
Qed.

Lemma run_respects_limits_step :
  forall L prog fuel st,
    run_respects_limits L prog (S fuel) st ->
    run_respects_limits L prog fuel (step_state prog st).
Proof.
  intros L prog fuel st Hrun k Hk.
  rewrite <- run_steps_S.
  apply Hrun.
  lia.
Qed.

(*
│
│          `code_run_last_NextState_of` is the key compatibility lemma
│          between the numeric witness generator and the structured
│          machine execution. Under a fixed limit invariant, iterating
│          `NextState_of` on encoded states computes exactly the same
│          final code as running `run_steps` on states and encoding
│          only at the end.
│
*)
(*   run_respects_limits(L, prog, fuel, st) ⇒ code_run_last(NextState_of(L,   *)
(* prog), fuel, encode_state_of(L, st)) = encode_state_of(L, run_steps(prog,  *)
(*                                fuel, st)).                                 *)

Lemma code_run_last_NextState_of :
  forall L prog fuel st,
    run_respects_limits L prog fuel st ->
    code_run_last (NextState_of L prog) fuel (encode_state_of L st) =
    encode_state_of L (run_steps prog fuel st).
Proof.
  intros L prog fuel.
  induction fuel as [|fuel IH]; intros st Hrun.
  - reflexivity.
  - simpl.
    assert (Hwf : state_well_formed_of L st).
    + assert (H0 : 0 <= S fuel) by lia.
      specialize (Hrun 0 H0).
      simpl in Hrun.
      exact Hrun.
    + rewrite NextState_on_encoded_state_of by exact Hwf.
      change
        (code_run_last (NextState_of L prog) fuel
           (encode_state_of L (step_state prog st)) =
         encode_state_of L (run_steps prog fuel (step_state prog st))).
      apply IH.
	      apply run_respects_limits_step with (st:=st).
	      exact Hrun.
Qed.

(*
│
│          `FamilyMachineAccepts_input_fits` isolates the first
│          necessary size condition hidden inside the existential
│          family semantics: any accepting family witness must choose
│          limits large enough to place the external input into the
│          `R1` window of the initial state.
│
*)

Lemma FamilyMachineAccepts_input_fits :
  forall prog input,
    FamilyMachineAccepts prog input ->
    exists L, input < r1_limit_of L.
Proof.
  intros prog input (L & fuel & Hrun & _).
  exists L.
  pose proof (run_respects_limits_initial L prog fuel (initial_state input) Hrun)
    as [_ [Hinput _]].
  exact Hinput.
Qed.

(*
│
│          `FamilyMachineAccepts_has_raw_witness` is the first
│          internal witness theorem for the asymptotic Iterant
│          semantics. It converts an existential halting run with
│          sufficiently large limits into one natural-number trace
│          witness whose local successor relation is `NextState_of L`.
│
*)
(* FamilyMachineAccepts(prog, input) ⇒ ∃ L, w, FamilyRawTraceWitness(L, prog, *)
(*                                 input, w).                                 *)

Theorem FamilyMachineAccepts_has_raw_witness :
  forall prog input,
    FamilyMachineAccepts prog input ->
    exists L witness,
      FamilyRawTraceWitness L prog input witness.
Proof.
  intros prog input (L & fuel & Hrun & Hhalt).
  exists L.
  exists
    (encode_nat_list
       (code_run_trace
          (NextState_of L prog)
          fuel
          (encode_state_of L (initial_state input)))).
  exists fuel.
  split.
  - reflexivity.
  - rewrite code_run_last_NextState_of.
    + pose proof (Hrun fuel (Nat.le_refl fuel)) as Hwf_final.
      rewrite decode_state_encode_state_of by exact Hwf_final.
      exact Hhalt.
    + exact Hrun.
Qed.

(*
│
│          `FamilyMachineAccepts_compile_program_iff` is the
│          family-level identity-compilation lemma for single inputs.
│
*)
(*            FamilyMachineAccepts(compile_program(prog), input) ⇔            *)
(*                     FamilyMachineAccepts(prog, input).                     *)

Lemma FamilyMachineAccepts_compile_program_iff :
  forall prog input,
    FamilyMachineAccepts (compile_program prog) input <->
    FamilyMachineAccepts prog input.
Proof.
  intros prog input.
  unfold FamilyMachineAccepts, compile_program.
  tauto.
Qed.

(*
│
│          `FamilyMachineComputes_compile_program_iff` lifts the same
│          identity-compilation fact to family-level semantic
│          specifications.
│
*)
(*            FamilyMachineComputes(compile_program(prog), Lang) ⇔            *)
(*                     FamilyMachineComputes(prog, Lang).                     *)

Lemma FamilyMachineComputes_compile_program_iff :
  forall prog Lang,
    FamilyMachineComputes (compile_program prog) Lang <->
    FamilyMachineComputes prog Lang.
Proof.
  intros prog Lang.
  unfold FamilyMachineComputes, compile_program.
  tauto.
Qed.

(*
│
│          `FamilySigma1CompletenessTarget_identity_iff` collapses the
│          family-level universality target to the uncompiled
│          semantics, again because `compile_program` is the identity.
│
*)
(* FamilySigma1CompletenessTarget(RELanguage) ⇔ ∀ Lang, RELanguage(Lang) → ∃  *)
(*                  prog, FamilyMachineComputes(prog, Lang).                  *)

Lemma FamilySigma1CompletenessTarget_identity_iff :
  forall RELanguage,
    FamilySigma1CompletenessTarget RELanguage <->
    forall Lang,
      RELanguage Lang ->
      exists prog, FamilyMachineComputes prog Lang.
Proof.
  intros RELanguage.
  split; intros Htarget Lang HLang.
  - destruct (Htarget Lang HLang) as [prog Hprog].
    exists prog.
    apply (proj1 (FamilyMachineComputes_compile_program_iff prog Lang)).
    exact Hprog.
  - destruct (Htarget Lang HLang) as [prog Hprog].
    exists prog.
    apply (proj2 (FamilyMachineComputes_compile_program_iff prog Lang)).
    exact Hprog.
Qed.

(*
│
│          `subtraction_program` is the canonical worked example: it
│          alternates between decrementing `R2` and decrementing `R1`
│          until `R2` hits zero, then halts with `R1 = n - m`.
│
*)

Definition subtraction_program : program :=
  [HALT;
   JZDEC Counter2 0 2;
   JZDEC Counter1 0 1].

Lemma subtraction_step_r2 :
  forall n m,
    step_state subtraction_program (Build_IterantState 1 n (S m)) =
    Build_IterantState 2 n m.
Proof.
  intros n m.
  reflexivity.
Qed.

Lemma subtraction_step_r1 :
  forall n m,
    step_state subtraction_program (Build_IterantState 2 (S n) m) =
    Build_IterantState 1 n m.
Proof.
  intros n m.
  reflexivity.
Qed.

Lemma subtraction_halt_step :
  forall n,
    step_state subtraction_program (Build_IterantState 1 n 0) =
    Build_IterantState 0 n 0.
Proof.
  intro n.
  reflexivity.
Qed.

Lemma run_subtraction_loop :
  forall n m,
    m <= n ->
    run_steps subtraction_program (2 * m) (initial_state2 n m) =
    Build_IterantState 1 (n - m) 0.
Proof.
  intros n m.
  revert n.
  induction m as [|m IH]; intros n Hle.
  - simpl.
    replace (n - 0) with n by lia.
    reflexivity.
  - destruct n as [|n']; [lia|].
    replace (2 * S m) with (S (S (2 * m))) by lia.
    simpl.
    rewrite subtraction_step_r2.
    rewrite subtraction_step_r1.
    apply IH.
    lia.
Qed.

(*
│
│          `subtraction_program_halts` is the worked halting theorem
│          for the subtraction example: after `2m + 1` steps, the
│          program reaches the halted state with register content `n -
│          m`, provided `m ≤ n`.
│
*)
(*m ≤ n ⇒ run_steps(subtraction_program, 2m + 1, initial_state2(n, m)) = (0, n*)
(*                                  - m, 0).                                  *)

Theorem subtraction_program_halts :
  forall n m,
    m <= n ->
    run_steps subtraction_program (S (2 * m)) (initial_state2 n m) =
    Build_IterantState 0 (n - m) 0.
Proof.
  intros n m Hle.
  replace (S (2 * m)) with (2 * m + 1) by lia.
  rewrite run_steps_plus.
  rewrite run_subtraction_loop by exact Hle.
  apply subtraction_halt_step.
Qed.

(*
│
│          The subtraction example is the first concrete place where
│          the abstract step semantics, the structured Iterant
│          execution function, and the family-level acceptance
│          viewpoint line up on an explicit program.
│
*)

Corollary subtraction_program_correct :
  forall n m,
    m <= n ->
    state_ip (run_steps subtraction_program (S (2 * m)) (initial_state2 n m)) = 0 /\
    state_r1 (run_steps subtraction_program (S (2 * m)) (initial_state2 n m)) = n - m.
Proof.
  intros n m Hle.
  rewrite subtraction_program_halts by exact Hle.
  split; reflexivity.
Qed.
