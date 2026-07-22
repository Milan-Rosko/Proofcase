(*M001_09__Regulated_Execution.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                   Proofcase / M001_09__Regulated_Execution                   │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Regulated execution for the frozen symbolic-regulator interface. The M001
  checker is packaged as the canonical proof regulator, while a generic
  Boolean gate releases a proposed output exactly when its supplied
  instruction is accepted. Release is pure symbolic computation: an external
  listener may interpret the released output, but M001 adds no actuator,
  environment, proof search, or semantic truth predicate.

*)

From M001 Require Export M001_08__Regulation.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          CANONICAL PROOF REGULATOR                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A regulator theory and context determine the canonical M001
│          symbolic regulator: finite proof scripts are instructions,
│          formulas are outputs, and the existing Boolean proof
│          checker is the acceptance function.
│
*)

Definition regulator_theory_symbolic_regulator
    (R : RegulatorTheory)
    (Gamma : Context) : S_λ :=
  {|
    symbolic_regulator_output := Formula;
    symbolic_regulator_instruction := Proof;
    symbolic_regulator_accepts_bool :=
      regulator_theory_check_bool R Gamma
  |}.

(*
│
│          Symbolic derivability for the canonical proof regulator is
│          definitionally the existing existential
│          checked-derivability predicate.
│
*)

Theorem regulator_theory_symbolic_regulator_derivable_iff :
  forall (R : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    symbolic_regulator_derivable
      (regulator_theory_symbolic_regulator R Gamma) A <->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  intros R Gamma A.
  reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             BOOLEAN RELEASE GATE                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The release gate preserves the proposed output on
│          acceptance and blocks it on rejection. It does not
│          synthesize an output or interpret the output as an external
│          action.
│
*)

Definition symbolic_regulator_release
    (S : S_λ)
    (i : symbolic_regulator_instruction S)
    (b : symbolic_regulator_output S)
    : option (symbolic_regulator_output S) :=
  if symbolic_regulator_accepts_bool S i b
  then Some b
  else None.

Lemma symbolic_regulator_release_sound :
  forall (S : S_λ)
         (i : symbolic_regulator_instruction S)
         (b : symbolic_regulator_output S),
    symbolic_regulator_release S i b = Some b ->
    symbolic_regulator_accepts_bool S i b = true.
Proof.
  intros S i b Hrelease.
  unfold symbolic_regulator_release in Hrelease.
  destruct (symbolic_regulator_accepts_bool S i b) eqn:Haccepted.
  - exact Haccepted.
  - discriminate Hrelease.
Qed.

Lemma symbolic_regulator_release_complete :
  forall (S : S_λ)
         (i : symbolic_regulator_instruction S)
         (b : symbolic_regulator_output S),
    symbolic_regulator_accepts_bool S i b = true ->
    symbolic_regulator_release S i b = Some b.
Proof.
  intros S i b Haccepted.
  unfold symbolic_regulator_release.
  rewrite Haccepted.
  reflexivity.
Qed.

Theorem symbolic_regulator_release_acceptance_iff :
  forall (S : S_λ)
         (i : symbolic_regulator_instruction S)
         (b : symbolic_regulator_output S),
    symbolic_regulator_release S i b = Some b <->
    symbolic_regulator_accepts_bool S i b = true.
Proof.
  intros S i b.
  split.
  - exact (symbolic_regulator_release_sound S i b).
  - exact (symbolic_regulator_release_complete S i b).
Qed.

(*
│
│          An output is symbolically derivable exactly when some
│          instruction causes the gate to release it.
│
*)

Theorem symbolic_regulator_derivable_release_iff :
  forall (S : S_λ)
         (b : symbolic_regulator_output S),
    symbolic_regulator_derivable S b <->
    exists i : symbolic_regulator_instruction S,
      symbolic_regulator_release S i b = Some b.
Proof.
  intros S b.
  unfold symbolic_regulator_derivable.
  split.
  - intros [i Haccepted].
    exists i.
    exact (symbolic_regulator_release_complete S i b Haccepted).
  - intros [i Hrelease].
    exists i.
    exact (symbolic_regulator_release_sound S i b Hrelease).
Qed.

(*
│
│          Specializing the release characterization to the canonical
│          proof regulator identifies released formulas with ordinary
│          M001 checked derivability.
│
*)

Theorem regulator_theory_symbolic_regulator_release_iff :
  forall (R : RegulatorTheory)
         (Gamma : Context)
         (A : Formula),
    regulator_theory_checked_derivable R Gamma A <->
    exists p : Proof,
      symbolic_regulator_release
        (regulator_theory_symbolic_regulator R Gamma) p A = Some A.
Proof.
  intros R Gamma A.
  split.
  - intros [p Haccepted].
    exists p.
    apply symbolic_regulator_release_complete.
    exact Haccepted.
  - intros [p Hrelease].
    exists p.
    apply symbolic_regulator_release_sound in Hrelease.
    exact Hrelease.
Qed.
