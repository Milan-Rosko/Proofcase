(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This file isolates the classical abstract universality layer of the Fibonacci Machine. We no longer speaks about Zeckendorf bands directly: it works over the abstract Minsky-style configurations and traces induced by `D001_08`, while remaining self-contained inside the D001 development.]]@*)

(*@head.end@*)

From D001 Require Export D001_08__Universality.

(*@inline@[[`abstract_initial_config`, `abstract_next`, and `abstract_run_steps` form the self-contained abstract execution model. They forget the band-coded realization and iterate only the Minsky-style configuration transformer.]]@*)
(*@unicodemath@[[abstract_initial_config(input) = (1, input, 0)]][[abstract_run_steps(prog, fuel + 1, cfg) = abstract_run_steps(prog, fuel, abstract_next(prog, cfg)).]]@*)

Definition abstract_initial_config (input : nat) : AbstractConfig :=
  (1, input, 0).

Definition abstract_next (prog : program) (cfg : AbstractConfig) : AbstractConfig :=
  state_to_config (step_state prog (config_to_state cfg)).

(*@inline@[[`config_to_state_state_to_config` records the trivial retraction from structured FM states to abstract configurations and back. Making it explicit keeps the classical proofs honest: no dynamics are hidden inside the transport.]]@*)
(*@unicodemath@[[config_to_state(state_to_config(st)) = st.]]@*)

Lemma config_to_state_state_to_config :
  forall st,
    config_to_state (state_to_config st) = st.
Proof.
  intros [ip r1 r2].
  reflexivity.
Qed.

Fixpoint abstract_run_steps (prog : program) (fuel : nat) (cfg : AbstractConfig)
  : AbstractConfig :=
  match fuel with
  | 0 => cfg
  | S fuel' => abstract_run_steps prog fuel' (abstract_next prog cfg)
  end.

(*@inline@[[`abstract_next_state` is the one-step version of the later run bridge. It says that the classical successor map is not a new dynamics at all: it is exactly the FM `step_state` seen through the configuration-state transport.]]@*)
(*@unicodemath@[[config_to_state(abstract_next(prog, cfg)) = step_state(prog, config_to_state(cfg)).]]@*)

Lemma abstract_next_state :
  forall prog cfg,
    config_to_state (abstract_next prog cfg) =
    step_state prog (config_to_state cfg).
Proof.
  intros prog cfg.
  unfold abstract_next.
  rewrite config_to_state_state_to_config.
  reflexivity.
Qed.

(*@inline@[[`abstract_run_steps_S` is the unfold equation for the classical run iterator. It is trivial definitionally, but documenting it matters because nearly every inductive proof over abstract runs starts by rewriting with exactly this shape.]]@*)
(*@unicodemath@[[abstract_run_steps(prog, fuel + 1, cfg) = abstract_run_steps(prog, fuel, abstract_next(prog, cfg)).]]@*)

Lemma abstract_run_steps_S :
  forall prog fuel cfg,
    abstract_run_steps prog (S fuel) cfg =
    abstract_run_steps prog fuel (abstract_next prog cfg).
Proof.
  reflexivity.
Qed.

(*@inline@[[`abstract_run_steps_state_bridge` is the core compatibility theorem for the classical layer: abstract runs and structured FM runs compute the same sequence of configurations after transport through `config_to_state`.]]@*)
(*@unicodemath@[[config_to_state(abstract_run_steps(prog, fuel, cfg)) = run_steps(prog, fuel, config_to_state(cfg)).]]@*)

Lemma abstract_run_steps_state_bridge :
  forall prog fuel cfg,
    config_to_state (abstract_run_steps prog fuel cfg) =
    run_steps prog fuel (config_to_state cfg).
Proof.
  intros prog fuel.
  induction fuel as [|fuel IH]; intro cfg.
  - reflexivity.
  - rewrite abstract_run_steps_S.
    rewrite IH.
    rewrite abstract_next_state.
    reflexivity.
Qed.

(*@inline@[[This layer is intentionally thin. It keeps only the abstract run model, the classical acceptance and computability targets, and the bridge back from the band-parameterized family semantics.]]@*)
(*@inline@[[`ClassicMachineAccepts` is the abstract halting predicate for the classical layer. It is the machine-theoretic notion that a later standalone universality theorem should target, before any external computability library is invoked.]]@*)
(*@unicodemath@[[ClassicMachineAccepts(prog, input) ⇔ ∃ fuel, abstract_halted(abstract_run_steps(prog, fuel, abstract_initial_config(input))).]]@*)
(*@inline@[[`ClassicSigma1CompletenessTarget` is the exact schema for the standalone classical universality theorem. It asks for one FM program per recursively enumerable language, but speaks only in the abstract halting vocabulary of this file.]]@*)
(*@unicodemath@[[ClassicSigma1CompletenessTarget(RELanguage) ≡ ∀ Lang, RELanguage(Lang) → ∃ prog, ClassicMachineComputes(compile_program(prog), Lang).]]@*)

Definition ClassicMachineAccepts (prog : program) (input : nat) : Prop :=
  exists fuel,
    abstract_halted
      (abstract_run_steps prog fuel (abstract_initial_config input)).

Definition ClassicMachineComputes (prog : program) (Lang : nat -> Prop) : Prop :=
  forall n, ClassicMachineAccepts prog n <-> Lang n.

Definition ClassicSigma1CompletenessTarget
    (RELanguage : (nat -> Prop) -> Prop) : Prop :=
  forall Lang,
    RELanguage Lang ->
    exists prog, ClassicMachineComputes (compile_program prog) Lang.

(*@inline@[[`ClassicMachineAccepts_compile_program_iff` is the classical identity-compilation lemma for single inputs.]]@*)
(*@unicodemath@[[ClassicMachineAccepts(compile_program(prog), input) ⇔ ClassicMachineAccepts(prog, input).]]@*)

Lemma ClassicMachineAccepts_compile_program_iff :
  forall prog input,
    ClassicMachineAccepts (compile_program prog) input <->
    ClassicMachineAccepts prog input.
Proof.
  intros prog input.
  unfold ClassicMachineAccepts, compile_program.
  tauto.
Qed.

(*@inline@[[`ClassicMachineComputes_compile_program_iff` lifts the same identity-compilation fact from single inputs to whole semantic specifications.]]@*)
(*@unicodemath@[[ClassicMachineComputes(compile_program(prog), Lang) ⇔ ClassicMachineComputes(prog, Lang).]]@*)

Lemma ClassicMachineComputes_compile_program_iff :
  forall prog Lang,
    ClassicMachineComputes (compile_program prog) Lang <->
    ClassicMachineComputes prog Lang.
Proof.
  intros prog Lang.
  unfold ClassicMachineComputes, compile_program.
  tauto.
Qed.

(*@inline@[[`ClassicSigma1CompletenessTarget_identity_iff` collapses the classical universality target to the uncompiled semantics, since `compile_program` is still the identity.]]@*)
(*@unicodemath@[[ClassicSigma1CompletenessTarget(RELanguage) ⇔ ∀ Lang, RELanguage(Lang) → ∃ prog, ClassicMachineComputes(prog, Lang).]]@*)

Lemma ClassicSigma1CompletenessTarget_identity_iff :
  forall RELanguage,
    ClassicSigma1CompletenessTarget RELanguage <->
    forall Lang,
      RELanguage Lang ->
      exists prog, ClassicMachineComputes prog Lang.
Proof.
  intros RELanguage.
  split; intros Htarget Lang HLang.
  - destruct (Htarget Lang HLang) as [prog Hprog].
    exists prog.
    apply (proj1 (ClassicMachineComputes_compile_program_iff prog Lang)).
    exact Hprog.
  - destruct (Htarget Lang HLang) as [prog Hprog].
    exists prog.
    apply (proj2 (ClassicMachineComputes_compile_program_iff prog Lang)).
    exact Hprog.
Qed.

(*@inline@[[`FamilyMachineAccepts_implies_Classic` is the main bridge from the band-parameterized family semantics back to the classical abstract view: every sufficiently large concrete halting run yields an abstract halting run on the same program and input.]]@*)
(*@inline@[[Its proof uses no new machine argument beyond the bridge developed in `D001_08`: a family witness already contains a concrete halting run, and the classical layer simply forgets the chosen `MachineLimits` package while preserving the same fuel and abstract endpoint.]]@*)
(*@unicodemath@[[FamilyMachineAccepts(prog, input) ⇒ ClassicMachineAccepts(prog, input).]]@*)

Theorem FamilyMachineAccepts_implies_Classic :
  forall prog input,
    FamilyMachineAccepts prog input ->
    ClassicMachineAccepts prog input.
Proof.
  intros prog input (L & fuel & _ & Hhalt).
  exists fuel.
  unfold abstract_halted, abstract_initial_config.
  destruct (abstract_run_steps prog fuel (1, input, 0)) as [[ip r1] r2] eqn:Hrun.
  simpl.
  pose proof (abstract_run_steps_state_bridge prog fuel (1, input, 0)) as Hbridge.
  rewrite Hrun in Hbridge.
  simpl in Hbridge.
  unfold halted_state in Hhalt.
  unfold initial_state in Hhalt.
  rewrite <- Hbridge in Hhalt.
  exact Hhalt.
Qed.

(*@inline@[[`abstract_subtraction_program_halts` transports the worked subtraction example entirely into the classical configuration language. It is the first concrete sanity check showing that the abstract execution model is not merely definitional scaffolding, but computes the expected result on an explicit program.]]@*)
(*@unicodemath@[[m ≤ n ⇒ abstract_run_steps(subtraction_program, 2m + 1, (1, n, m)) = (0, n - m, 0).]]@*)

Lemma abstract_subtraction_program_halts :
  forall n m,
    m <= n ->
    abstract_run_steps subtraction_program (S (2 * m))
      (1, n, m) =
    (0, n - m, 0).
Proof.
  intros n m Hle.
  pose proof
    (abstract_run_steps_state_bridge subtraction_program (S (2 * m)) (1, n, m))
    as Hbridge.
  change (config_to_state (1, n, m)) with (initial_state2 n m) in Hbridge.
  rewrite subtraction_program_halts in Hbridge by exact Hle.
  apply (f_equal state_to_config) in Hbridge.
  repeat rewrite state_to_config_config_to_state in Hbridge.
  exact Hbridge.
Qed.

(*@inline@[[`subtraction_program_classic_accepts` is the final classical-layer witness that the abstract halting predicate is inhabited by a real FM program. It keeps the file grounded in an explicit execution example while the broader universality theorem remains a target schema.]]@*)
(*@unicodemath@[[m ≤ n ⇒ abstract_halted(abstract_run_steps(subtraction_program, 2m + 1, (1, n, m))).]]@*)

Corollary subtraction_program_classic_accepts :
  forall n m,
    m <= n ->
    abstract_halted
      (abstract_run_steps subtraction_program (S (2 * m))
         (1, n, m)).
Proof.
  intros n m Hle.
  unfold abstract_halted.
  rewrite abstract_subtraction_program_halts by exact Hle.
  reflexivity.
Qed.
