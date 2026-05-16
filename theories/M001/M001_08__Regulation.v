(*M001_08__Regulation.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / M001_08__Regulation                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Regulation interface for regulator-theory checking. The earlier layers
  define proof lines, finite scripts, a Boolean checker, checked
  derivability, syntactic adequacy, and monotonicity. This layer reifies one
  proof line as a first-class regulator instruction, proves that
  instruction-level regulation is exactly the line checker, lifts that
  equivalence to regulated proof scripts, packages the checker as an abstract
  `SymbolicRegulator`, and exposes the minimal closure/equivalence vocabulary
  needed by evaluation and L001.

  The regulator remains operational. Its acceptance predicate is a Boolean
  function on instructions and outputs, and the regulator-theory instance is
  definitionally the existing `regulator_theory_check_bool`. The paper-facing
  symbol `S_λ` is used here only for this constructive interface: a carrier
  of instructions, a carrier of outputs, and a Boolean acceptance relation.
  The closure view is checked derivability, equivalence is implication in
  both directions inside that closure, and the one exported closure principle
  is modus ponens. No semantic interpretation, model carrier, truth
  predicate, modal provability operator, arithmetic coding, diagonal
  obstruction, self-token, or self-recognition principle is introduced here.

*)

From M001 Require Export M001_07__Obstruction.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            REGULATOR INSTRUCTIONS                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A `RegulatorInstruction` is the native instruction syntax
│          corresponding to one proof line. Assumption and axiom
│          instructions carry their produced formula; MP instructions
│          carry two prefix references together with the claimed
│          output formula.
│
*)

(*                 instr ::= assume(A) ∣ axiom(A) ∣ mp(i,j,B)                 *)

(*               regulator_instruction_output(assume(A)) = A ∧                *)
(*                regulator_instruction_output(axiom(A)) = A ∧                *)
(*                regulator_instruction_output(mp(i,j,B)) = B                 *)

Inductive RegulatorInstruction : Type :=
| regulator_instruction_assumption : Formula -> RegulatorInstruction
| regulator_instruction_axiom : Formula -> RegulatorInstruction
| regulator_instruction_mp : nat -> nat -> Formula -> RegulatorInstruction.

Inductive RegulatorInstructionTag : Type :=
| regulator_instruction_tag_assumption
| regulator_instruction_tag_axiom
| regulator_instruction_tag_mp.

Definition regulator_instruction_output
    (instr : RegulatorInstruction) : Formula :=
  match instr with
  | regulator_instruction_assumption A => A
  | regulator_instruction_axiom A => A
  | regulator_instruction_mp _ _ B => B
  end.

Definition regulator_instruction_tag
    (instr : RegulatorInstruction) : RegulatorInstructionTag :=
  match instr with
  | regulator_instruction_assumption _ =>
      regulator_instruction_tag_assumption
  | regulator_instruction_axiom _ =>
      regulator_instruction_tag_axiom
  | regulator_instruction_mp _ _ _ =>
      regulator_instruction_tag_mp
  end.

(*
│
│          The instruction/proof-line translations are mechanical.
│          They do not check an instruction; they only move between
│          the native regulator vocabulary and the proof-line grammar
│          consumed by the kernel checker.
│
*)

(*        regulator_instruction_to_line(assume(A)) = pl_assumption(A)         *)
(*           regulator_instruction_to_line(axiom(A)) = pl_axiom(A)            *)
(*          regulator_instruction_to_line(mp(i,j,B)) = pl_mp(B,i,j)           *)

Definition regulator_instruction_to_line
    (instr : RegulatorInstruction) : ProofLine :=
  match instr with
  | regulator_instruction_assumption A => pl_assumption A
  | regulator_instruction_axiom A => pl_axiom A
  | regulator_instruction_mp i j B => pl_mp B i j
  end.

Definition proof_line_to_regulator_instruction
    (line : ProofLine) : RegulatorInstruction :=
  match line.(line_justification) with
  | J_Assumption =>
      regulator_instruction_assumption line.(line_formula)
  | J_Axiom =>
      regulator_instruction_axiom line.(line_formula)
  | J_MP i j =>
      regulator_instruction_mp i j line.(line_formula)
  end.

(* regulator_instruction_to_line(proof_line_to_regulator_instruction(line)) = *)
(*                                    line                                    *)

Lemma regulator_instruction_to_line_to_instruction_lemma :
  forall line,
    regulator_instruction_to_line
      (proof_line_to_regulator_instruction line) = line.
Proof.
  intros [A just].
  destruct just as [| |i j];
    reflexivity.
Qed.

Lemma line_formula_regulator_instruction_to_line_lemma :
  forall instr,
    line_formula (regulator_instruction_to_line instr) =
    regulator_instruction_output instr.
Proof.
  destruct instr as [A|A|i j B];
    reflexivity.
Qed.

Definition regulator_instruction_matches_line
    (instr : RegulatorInstruction)
    (line : ProofLine) : Prop :=
  regulator_instruction_to_line instr = line.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             ONE-STEP REGULATION                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `regulator_instruction_valid R Γ prefix instr B` is the
│          Prop-level one-step regulator relation. It validates a
│          native instruction against an already accepted prefix and
│          an advertised output. MP keeps the certificate convention
│          from the checker: either reference order is accepted as
│          long as the prefix contains an antecedent and a matching
│          implication.
│
*)

(*              regulator_instruction_valid(R,Γ,prefix,instr,B)               *)

Inductive regulator_instruction_valid
    (R : RegulatorTheory)
    (Gamma : Context)
    (prefix : list ProofLine)
    : RegulatorInstruction -> Formula -> Prop :=

(*        A ∈ Γ ⇒ regulator_instruction_valid(R,Γ,prefix,assume(A),A)         *)

| regulator_instruction_valid_assumption :
    forall A,
      In A Gamma ->
      regulator_instruction_valid R Gamma prefix
        (regulator_instruction_assumption A)
        A

(*                      available_axiom_bool(R,A)=true ⇒                      *)
(*             regulator_instruction_valid(R,Γ,prefix,axiom(A),A)             *)

| regulator_instruction_valid_axiom :
    forall A,
      available_axiom_bool R A = true ->
      regulator_instruction_valid R Gamma prefix
        (regulator_instruction_axiom A)
        A

(*                       prefix[i]=A ∧ prefix[j]=A→B ⇒                        *)
(*            regulator_instruction_valid(R,Γ,prefix,mp(i,j,B),B)             *)

| regulator_instruction_valid_mp_left :
    forall i j A B,
      nth_formula prefix i = Some A ->
      nth_formula prefix j = Some (Imp A B) ->
      regulator_instruction_valid R Gamma prefix
        (regulator_instruction_mp i j B)
        B

(*                       prefix[i]=A→B ∧ prefix[j]=A ⇒                        *)
(*            regulator_instruction_valid(R,Γ,prefix,mp(i,j,B),B)             *)

| regulator_instruction_valid_mp_right :
    forall i j A B,
      nth_formula prefix i = Some (Imp A B) ->
      nth_formula prefix j = Some A ->
      regulator_instruction_valid R Gamma prefix
        (regulator_instruction_mp i j B)
        B.

Lemma regulator_instruction_valid_output_lemma :
  forall R Gamma prefix instr B,
    regulator_instruction_valid R Gamma prefix instr B ->
    regulator_instruction_output instr = B.
Proof.
  intros R Gamma prefix instr B Hvalid.
  destruct Hvalid;
    reflexivity.
Qed.

Definition regulator_instruction_valid_bool
    (R : RegulatorTheory)
    (Gamma : Context)
    (prefix : list ProofLine)
    (instr : RegulatorInstruction)
    (B : Formula) : bool :=
  match instr with
  | regulator_instruction_assumption A =>
      formula_eq_bool A B && ctx_mem_bool A Gamma
  | regulator_instruction_axiom A =>
      formula_eq_bool A B && available_axiom_bool R A
  | regulator_instruction_mp i j A =>
      ((formula_eq_bool A B &&
        Nat.ltb i (length prefix)) &&
       Nat.ltb j (length prefix)) &&
      mp_valid_bool prefix i j A
  end.

(*
│
│          The Boolean one-step checker is equivalent to the
│          Prop-level instruction relation. Soundness decodes
│          successful Boolean checks into assumption, axiom, or one of
│          the two unordered MP orientations; completeness rebuilds
│          exactly the Boolean checks required by the executable
│          regulator.
│
*)

(*        regulator_instruction_valid_bool(R,Γ,prefix,instr,B)=true ⇔         *)
(*              regulator_instruction_valid(R,Γ,prefix,instr,B)               *)

Lemma regulator_instruction_valid_bool_sound_lemma :
  forall R Gamma prefix instr B,
    regulator_instruction_valid_bool R Gamma prefix instr B = true ->
    regulator_instruction_valid R Gamma prefix instr B.
Proof.
  intros R Gamma prefix instr B Hvalid.
  destruct instr as [A|A|i j A]; simpl in Hvalid.
  - pose proof (bool_and_true_left_lemma _ _ Hvalid) as Heq.
    pose proof (bool_and_true_right_lemma _ _ Hvalid) as Hmem.
    apply formula_eq_bool_true_lemma in Heq.
    subst B.
    apply regulator_instruction_valid_assumption.
    apply ctx_mem_bool_sound_lemma.
    exact Hmem.
  - pose proof (bool_and_true_left_lemma _ _ Hvalid) as Heq.
    pose proof (bool_and_true_right_lemma _ _ Hvalid) as Haxiom.
    apply formula_eq_bool_true_lemma in Heq.
    subst B.
    apply regulator_instruction_valid_axiom.
    exact Haxiom.
  - pose proof (bool_and_true_left_lemma _ _ Hvalid) as Heq.
    pose proof (bool_and_true_right_lemma _ _ Hvalid) as Hmp.
    pose proof (bool_and_true_left_lemma _ _ Heq) as Heq_and_i.
    pose proof (bool_and_true_left_lemma _ _ Heq_and_i) as Heq_formula.
    apply formula_eq_bool_true_lemma in Heq_formula.
    subst B.
    apply mp_valid_bool_sound_unordered_lemma in Hmp.
    destruct Hmp as [C [[Hi Hj] | [Hi Hj]]].
    + apply regulator_instruction_valid_mp_left with (A := C).
      * exact Hi.
      * exact Hj.
    + apply regulator_instruction_valid_mp_right with (A := C).
      * exact Hi.
      * exact Hj.
Qed.

Lemma regulator_instruction_valid_bool_complete_lemma :
  forall R Gamma prefix instr B,
    regulator_instruction_valid R Gamma prefix instr B ->
    regulator_instruction_valid_bool R Gamma prefix instr B = true.
Proof.
  intros R Gamma prefix instr B Hvalid.
  destruct Hvalid as
    [A Hin
    |A Haxiom
    |i j A B Hi Hj
    |i j A B Hi Hj];
    simpl.
  - rewrite formula_eq_bool_refl_lemma.
    apply ctx_mem_bool_complete_lemma.
    exact Hin.
  - rewrite formula_eq_bool_refl_lemma.
    exact Haxiom.
  - rewrite formula_eq_bool_refl_lemma.
    rewrite (nth_formula_some_ltb_lemma _ _ _ Hi).
    rewrite (nth_formula_some_ltb_lemma _ _ _ Hj).
    simpl.
    apply mp_valid_bool_direct_lemma with (C := A);
      assumption.
  - rewrite formula_eq_bool_refl_lemma.
    rewrite (nth_formula_some_ltb_lemma _ _ _ Hi).
    rewrite (nth_formula_some_ltb_lemma _ _ _ Hj).
    simpl.
    apply mp_valid_bool_reverse_lemma with (C := A);
      assumption.
Qed.

Lemma regulator_instruction_valid_bool_instruction_to_line_lemma :
  forall R Gamma prefix instr,
    regulator_instruction_valid_bool
      R Gamma prefix instr
      (regulator_instruction_output instr) =
    proof_line_check_bool
      R Gamma prefix
      (regulator_instruction_to_line instr).
Proof.
  intros R Gamma prefix instr.
  destruct instr as [A|A|i j B];
    unfold regulator_instruction_valid_bool,
      proof_line_check_bool,
      proof_line_valid_bool;
    simpl;
    rewrite formula_eq_bool_refl_lemma;
    reflexivity.
Qed.

Lemma regulator_instruction_valid_bool_line_to_instruction_lemma :
  forall R Gamma prefix line,
    regulator_instruction_valid_bool
      R Gamma prefix
      (proof_line_to_regulator_instruction line)
      line.(line_formula) =
    proof_line_check_bool R Gamma prefix line.
Proof.
  intros R Gamma prefix [A just].
  destruct just as [| |i j];
    unfold regulator_instruction_valid_bool,
      proof_line_check_bool,
      proof_line_valid_bool;
    simpl;
    rewrite formula_eq_bool_refl_lemma;
    reflexivity.
Qed.

Lemma regulator_instruction_valid_line_lemma :
  forall R Gamma prefix line,
    regulator_instruction_valid
      R Gamma prefix
      (proof_line_to_regulator_instruction line)
      line.(line_formula)
    <->
    proof_line_valid_bool R Gamma prefix line = true.
Proof.
  intros R Gamma prefix line.
  split.
  - intro Hvalid.
    pose proof
      (regulator_instruction_valid_bool_complete_lemma
        R Gamma prefix
        (proof_line_to_regulator_instruction line)
        line.(line_formula)
        Hvalid) as Hbool.
    rewrite regulator_instruction_valid_bool_line_to_instruction_lemma
      in Hbool.
    unfold proof_line_check_bool in Hbool.
    exact Hbool.
  - intro Hline.
    apply regulator_instruction_valid_bool_sound_lemma.
    rewrite regulator_instruction_valid_bool_line_to_instruction_lemma.
    unfold proof_line_check_bool.
    exact Hline.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                       COMPONENTS AND REGULATED SCRIPTS                       │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A component packages one accepted instruction/output pair
│          at a fixed regulator theory, context, and prefix. A
│          regulated suffix is the trace-level lift: each head line is
│          reified as its native instruction, validated against the
│          current prefix, and then appended before the remaining
│          suffix is checked.
│
*)

(*            RegulatorTheoryComponent(R,Γ,prefix) ≔ { (instr,B) ∣            *)
(*             regulator_instruction_valid(R,Γ,prefix,instr,B) }              *)
(*        CheckedRegulatorTheoryComponent(R,Γ,prefix) ≔ { (instr,B) ∣         *)
(*        regulator_instruction_valid_bool(R,Γ,prefix,instr,B)=true }         *)

Record RegulatorTheoryComponent
    (R : RegulatorTheory)
    (Gamma : Context)
    (prefix : list ProofLine)
    : Type := {
  regulator_component_instruction : RegulatorInstruction;
  regulator_component_output : Formula;
  regulator_component_valid :
    regulator_instruction_valid R Gamma prefix
      regulator_component_instruction
      regulator_component_output
}.

Record CheckedRegulatorTheoryComponent
    (R : RegulatorTheory)
    (Gamma : Context)
    (prefix : list ProofLine)
    : Type := {
  checked_regulator_component_instruction : RegulatorInstruction;
  checked_regulator_component_output : Formula;
  checked_regulator_component_valid :
    regulator_instruction_valid_bool R Gamma prefix
      checked_regulator_component_instruction
      checked_regulator_component_output = true
}.

Definition regulator_theory_component_family
    (R : RegulatorTheory)
    (Gamma : Context)
    (prefix : list ProofLine) : Type :=
  RegulatorTheoryComponent R Gamma prefix.

Definition regulator_instruction_pair_member
    (R : RegulatorTheory)
    (Gamma : Context)
    (prefix : list ProofLine)
    (c : RegulatorInstruction * Formula) : Prop :=
  regulator_instruction_valid R Gamma prefix (fst c) (snd c).

Inductive regulator_theory_regulated_suffix
    (R : RegulatorTheory)
    (Gamma : Context)
    : list ProofLine -> list ProofLine -> Prop :=
| regulator_theory_regulated_suffix_nil :
    forall prefix,
      regulator_theory_regulated_suffix R Gamma prefix nil
| regulator_theory_regulated_suffix_cons :
    forall prefix line rest,
      regulator_instruction_valid
        R Gamma prefix
        (proof_line_to_regulator_instruction line)
        line.(line_formula) ->
      regulator_theory_regulated_suffix
        R Gamma
        (prefix ++ cons line nil)
        rest ->
      regulator_theory_regulated_suffix
        R Gamma prefix (cons line rest).

Definition regulator_theory_regulated_proof
    (R : RegulatorTheory)
    (Gamma : Context)
    (p : Proof) : Prop :=
  regulator_theory_regulated_suffix R Gamma nil p.

(*
│
│          Regulated suffixes are exactly successful runs of
│          `proof_script_check_from_bool`. The proof is a structural
│          reification argument: the forward direction turns each
│          native line validation into the Boolean line checker, and
│          the reverse direction turns each accepted checker line back
│          into its native instruction.
│
*)

(*                      RegulatedSuffix(R,Γ,prefix,p) ⇔                       *)
(*              proof_script_check_from_bool(R,Γ,prefix,p)=true               *)

Lemma regulator_theory_regulated_suffix_iff_checker_lemma :
  forall R Gamma prefix p,
    regulator_theory_regulated_suffix R Gamma prefix p <->
    proof_script_check_from_bool R Gamma prefix p = true.
Proof.
  intros R Gamma prefix p.
  revert prefix.
  induction p as [|line rest IH]; intro prefix.
  - split; intro H.
    + reflexivity.
    + constructor.
  - split; intro H.
    + inversion H as
        [|prefix' line' rest' Hline Hrest];
        subst.
      simpl.
      apply regulator_instruction_valid_line_lemma in Hline.
      rewrite Hline.
      simpl.
      apply IH.
      exact Hrest.
    + simpl in H.
      pose proof (bool_and_true_left_lemma _ _ H) as Hline.
      pose proof (bool_and_true_right_lemma _ _ H) as Hrest.
      apply regulator_theory_regulated_suffix_cons.
      * apply regulator_instruction_valid_line_lemma.
        exact Hline.
      * apply IH.
        exact Hrest.
Qed.

Lemma regulator_theory_regulated_proof_iff_checker_lemma :
  forall R Gamma p,
    regulator_theory_regulated_proof R Gamma p <->
    proof_script_check_from_bool R Gamma nil p = true.
Proof.
  intros R Gamma p.
  unfold regulator_theory_regulated_proof.
  apply regulator_theory_regulated_suffix_iff_checker_lemma.
Qed.

(*    RegulatedProof(R,Γ,p) ⇔ proof_script_check_from_bool(R,Γ,[],p)=true     *)

(*
│
│          The regulated-proof view and checked-derivability view are
│          the same proof-script evidence packaged in two different
│          ways. A checked derivation gives a regulated proof with the
│          same last formula; a regulated proof with last formula `A`
│          rebuilds the Boolean checker certificate for `A`.
│
*)

(*       R; Γ ⊢check A ⇔ ∃p. RegulatedProof(R,Γ,p) ∧ last_formula(p)=A        *)

Lemma regulator_theory_regulated_derivability_iff_checked_derivability_lemma :
  forall R Gamma A,
    regulator_theory_checked_derivable R Gamma A <->
    exists p,
      regulator_theory_regulated_proof R Gamma p /\
      last_formula p = Some A.
Proof.
  intros R Gamma A.
  split.
  - intros [p Hcheck].
    exists p.
    split.
    + apply regulator_theory_regulated_proof_iff_checker_lemma.
      apply regulator_theory_check_true_lines_lemma
        with (A := A).
      exact Hcheck.
    + apply regulator_theory_check_true_last_lemma
        with (R := R)
        (Gamma := Gamma).
      exact Hcheck.
  - intros [p [Hregulated Hlast]].
    exists p.
    unfold regulator_theory_check_bool.
    apply regulator_theory_regulated_proof_iff_checker_lemma in Hregulated.
    rewrite Hregulated.
    rewrite Hlast.
    simpl.
    rewrite formula_eq_bool_refl_lemma.
    reflexivity.
Qed.

Definition regulator_theory_component_sound_property
    (R : RegulatorTheory)
    (Gamma : Context)
    (prefix : list ProofLine)
    (c : RegulatorTheoryComponent R Gamma prefix) : Prop :=
  proof_script_check_from_bool R Gamma nil prefix = true ->
  regulator_theory_checked_derivable
    R Gamma
    (regulator_component_output R Gamma prefix c).

(*         regulator_theory_component_sound_property(R,Γ,prefix,c) ≔          *)
(*       proof_script_check_from_bool(R,Γ,[],prefix)=true ⇒ R; Γ ⊢check       *)
(*                  regulator_component_output(R,Γ,prefix,c)                  *)

(*
│
│          Component soundness is still a finite script construction.
│          Given a checked prefix and one valid native component after
│          that prefix, append the component's proof line and use the
│          kernel append lemma to obtain a checked derivation of the
│          component output.
│
*)

(*             proof_script_check_from_bool(R,Γ,[],prefix)=true ∧             *)
(*      regulator_instruction_valid(R,Γ,prefix,instr,B) ⇒ R; Γ ⊢check B       *)

Lemma regulator_theory_component_sound_lemma :
  forall R Gamma prefix instr B,
    proof_script_check_from_bool R Gamma nil prefix = true ->
    regulator_instruction_valid R Gamma prefix instr B ->
    regulator_theory_checked_derivable R Gamma B.
Proof.
  intros R Gamma prefix instr B Hprefix Hvalid.
  pose proof
    (regulator_instruction_valid_output_lemma
      R Gamma prefix instr B Hvalid) as Hout.
  pose proof
    (regulator_instruction_valid_bool_complete_lemma
      R Gamma prefix instr B Hvalid) as Hbool.
  rewrite <- Hout in Hbool.
  rewrite regulator_instruction_valid_bool_instruction_to_line_lemma
    in Hbool.
  unfold proof_line_check_bool in Hbool.
  exists (prefix ++ cons (regulator_instruction_to_line instr) nil).
  unfold regulator_theory_check_bool.
  assert (Hline :
    proof_script_check_from_bool R Gamma prefix
      (cons (regulator_instruction_to_line instr) nil) = true).
  {
    simpl.
    rewrite Hbool.
    reflexivity.
  }
  pose proof
    (proof_script_check_append_true_lemma
      R Gamma prefix
      (cons (regulator_instruction_to_line instr) nil)
      Hprefix Hline) as Hfull.
  rewrite Hfull.
  rewrite last_formula_app_single_lemma.
  rewrite line_formula_regulator_instruction_to_line_lemma.
  rewrite Hout.
  simpl.
  rewrite formula_eq_bool_refl_lemma.
  reflexivity.
Qed.

Lemma regulator_theory_component_record_sound_lemma :
  forall R Gamma prefix
      (c : RegulatorTheoryComponent R Gamma prefix),
    regulator_theory_component_sound_property R Gamma prefix c.
Proof.
  intros R Gamma prefix c Hprefix.
  destruct c as [instr B Hvalid].
  apply regulator_theory_component_sound_lemma
    with (prefix := prefix) (instr := instr).
  - exact Hprefix.
  - exact Hvalid.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         ABSTRACT SYMBOLIC REGULATORS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A `SymbolicRegulator` records exactly the operational
│          interface needed later: an output type, an instruction
│          type, and a Boolean acceptance relation from instructions
│          to outputs. It has no semantic fields and no hidden
│          proof-search procedure.
│
*)

(*   SymbolicRegulator ≔ (Output, Instruction, accepts_bool : Instruction →   *)
(*                               Output → bool)                               *)
(*                          S_λ ≔ SymbolicRegulator                           *)

Record SymbolicRegulator : Type := {
  symbolic_regulator_output : Type;
  symbolic_regulator_instruction : Type;
  symbolic_regulator_accepts_bool :
    symbolic_regulator_instruction -> symbolic_regulator_output -> bool
}.

(*
│
│          `S_λ` is the symbolic-regulator alias used by the
│          paper-facing notation. It is definitionally the same type
│          as `SymbolicRegulator`; the alias does not add arithmetic
│          coding, a provability predicate, or a semantic model.
│
*)

Definition S_λ : Type := SymbolicRegulator.

Definition symbolic_regulator_derivable
    (S : S_λ)
    (b : symbolic_regulator_output S) : Prop :=
  exists i : symbolic_regulator_instruction S,
    symbolic_regulator_accepts_bool S i b = true.

(*                  symbolic_regulator_derivable(S,b) ≔ ∃i.                   *)
(*                symbolic_regulator_accepts_bool(S,i,b)=true                 *)

Definition symbolic_regulator_not_derivable
    (S : S_λ)
    (b : symbolic_regulator_output S) : Prop :=
  symbolic_regulator_derivable S b -> False.

(*symbolic_regulator_not_derivable(S,b) ≔ symbolic_regulator_derivable(S,b) → *)
(*                                   False                                    *)

Record SymbolicRegulatorWorld : Type := {
  symbolic_regulator_world_regulator : S_λ
}.

Definition symbolic_regulator_world_derivable
    (V : SymbolicRegulatorWorld)
    (b : symbolic_regulator_output V.(symbolic_regulator_world_regulator))
    : Prop :=
  symbolic_regulator_derivable
    V.(symbolic_regulator_world_regulator)
    b.

Definition symbolic_regulator_world_not_derivable
    (V : SymbolicRegulatorWorld)
    (b : symbolic_regulator_output V.(symbolic_regulator_world_regulator))
    : Prop :=
  symbolic_regulator_not_derivable
    V.(symbolic_regulator_world_regulator)
    b.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          REGULATOR-THEORY INSTANCE                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The regulator-theory symbolic regulator is the checker
│          itself viewed through the abstract interface: instructions
│          are finite proof scripts, outputs are formulas, and
│          acceptance is exactly `regulator_theory_check_bool`. The
│          finite axiom-set instance is the same interface with
│          `finite_axiom_set_check_bool` as the acceptance function.
│
*)

(*                 regulator_theory_regulates_bool(R,Γ,p,A) =                 *)
(*                    regulator_theory_check_bool(R,Γ,p,A)                    *)

Definition regulator_theory_regulates_bool
    (R : RegulatorTheory)
    (Gamma : Context)
    (p : Proof)
    (A : Formula) : bool :=
  regulator_theory_check_bool R Gamma p A.

(*        regulator_theory_symbolic_regulator(R,Γ) ≔ (Formula, Proof,         *)
(*                   regulator_theory_regulates_bool(R,Γ))                    *)

Definition regulator_theory_symbolic_regulator
    (R : RegulatorTheory)
    (Gamma : Context)
    : S_λ :=
  {|
    symbolic_regulator_output := Formula;
    symbolic_regulator_instruction := Proof;
    symbolic_regulator_accepts_bool :=
      regulator_theory_regulates_bool R Gamma
  |}.

Definition regulator_theory_symbolic_world
    (R : RegulatorTheory)
    (Gamma : Context)
    : SymbolicRegulatorWorld :=
  {|
    symbolic_regulator_world_regulator :=
      regulator_theory_symbolic_regulator R Gamma
  |}.

Definition finite_axiom_set_regulates_bool
    (profile : RegulatorLogicProfile)
    (T : FiniteAxiomSet)
    (Gamma : Context)
    (p : Proof)
    (A : Formula) : bool :=
  finite_axiom_set_check_bool profile T Gamma p A.

(*    finite_axiom_set_symbolic_regulator(profile,FT,Γ) ≔ (Formula, Proof,    *)
(*               finite_axiom_set_regulates_bool(profile,FT,Γ))               *)

Definition finite_axiom_set_symbolic_regulator
    (profile : RegulatorLogicProfile)
    (T : FiniteAxiomSet)
    (Gamma : Context)
    : S_λ :=
  {|
    symbolic_regulator_output := Formula;
    symbolic_regulator_instruction := Proof;
    symbolic_regulator_accepts_bool :=
      finite_axiom_set_regulates_bool profile T Gamma
  |}.

Definition finite_axiom_set_symbolic_world
    (profile : RegulatorLogicProfile)
    (T : FiniteAxiomSet)
    (Gamma : Context)
    : SymbolicRegulatorWorld :=
  {|
    symbolic_regulator_world_regulator :=
      finite_axiom_set_symbolic_regulator profile T Gamma
  |}.

(*
│
│          The symbolic-regulator derivability identities are
│          definitional: existential acceptance by the packaged
│          regulator is the same existential proof script already
│          named by checked derivability. The negative identities are
│          the corresponding contraposition over those positive
│          identities.
│
*)

(* symbolic_regulator_derivable(regulator_theory_symbolic_regulator(R,Γ),A) ⇔ *)
(*                               R; Γ ⊢check A                                *)

Lemma regulator_theory_symbolic_derivable_iff_checked_derivable_lemma :
  forall R Gamma A,
    symbolic_regulator_derivable
      (regulator_theory_symbolic_regulator R Gamma)
      A
    <->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  intros R Gamma A.
  unfold symbolic_regulator_derivable,
    regulator_theory_symbolic_regulator,
    regulator_theory_regulates_bool,
    regulator_theory_checked_derivable.
  simpl.
  split; intro H; exact H.
Qed.

(*symbolic_regulator_derivable(finite_axiom_set_symbolic_regulator(profile,FT,Γ),A)*)
(*                         ⇔ profile, FT; Γ ⊢check A                          *)

Lemma finite_axiom_set_symbolic_derivable_iff_checked_derivable_lemma :
  forall profile T Gamma A,
    symbolic_regulator_derivable
      (finite_axiom_set_symbolic_regulator profile T Gamma)
      A
    <->
    finite_axiom_set_checked_derivable profile T Gamma A.
Proof.
  intros profile T Gamma A.
  unfold symbolic_regulator_derivable,
    finite_axiom_set_symbolic_regulator,
    finite_axiom_set_regulates_bool,
    finite_axiom_set_checked_derivable.
  simpl.
  split; intro H; exact H.
Qed.

(*symbolic_regulator_world_derivable(regulator_theory_symbolic_world(R,Γ),A) ⇔*)
(*                               R; Γ ⊢check A                                *)

Lemma regulator_theory_symbolic_world_derivable_iff_checked_derivable_lemma :
  forall R Gamma A,
    symbolic_regulator_world_derivable
      (regulator_theory_symbolic_world R Gamma)
      A
    <->
    regulator_theory_checked_derivable R Gamma A.
Proof.
  intros R Gamma A.
  unfold symbolic_regulator_world_derivable,
    regulator_theory_symbolic_world.
  simpl.
  apply regulator_theory_symbolic_derivable_iff_checked_derivable_lemma.
Qed.

(*symbolic_regulator_world_derivable(finite_axiom_set_symbolic_world(profile,FT,Γ),A)*)
(*                         ⇔ profile, FT; Γ ⊢check A                          *)

Lemma finite_axiom_set_symbolic_world_derivable_iff_checked_derivable_lemma :
  forall profile T Gamma A,
    symbolic_regulator_world_derivable
      (finite_axiom_set_symbolic_world profile T Gamma)
      A
    <->
    finite_axiom_set_checked_derivable profile T Gamma A.
Proof.
  intros profile T Gamma A.
  unfold symbolic_regulator_world_derivable,
    finite_axiom_set_symbolic_world.
  simpl.
  apply finite_axiom_set_symbolic_derivable_iff_checked_derivable_lemma.
Qed.

(*symbolic_regulator_not_derivable(regulator_theory_symbolic_regulator(R,Γ),A)*)
(*                              ⇔ R; Γ ⊬check A                               *)

Lemma regulator_theory_symbolic_not_derivable_iff_not_checked_derivable_lemma :
  forall R Gamma A,
    symbolic_regulator_not_derivable
      (regulator_theory_symbolic_regulator R Gamma)
      A
    <->
    regulator_theory_not_checked_derivable R Gamma A.
Proof.
  intros R Gamma A.
  unfold symbolic_regulator_not_derivable,
    regulator_theory_not_checked_derivable.
  split; intros Hnot Hpos.
  - apply Hnot.
    apply regulator_theory_symbolic_derivable_iff_checked_derivable_lemma.
    exact Hpos.
  - apply Hnot.
    apply regulator_theory_symbolic_derivable_iff_checked_derivable_lemma.
    exact Hpos.
Qed.

(*symbolic_regulator_not_derivable(finite_axiom_set_symbolic_regulator(profile,FT,Γ),A)*)
(*                         ⇔ profile, FT; Γ ⊬check A                          *)

Lemma finite_axiom_set_symbolic_not_derivable_iff_not_checked_derivable_lemma :
  forall profile T Gamma A,
    symbolic_regulator_not_derivable
      (finite_axiom_set_symbolic_regulator profile T Gamma)
      A
    <->
    finite_axiom_set_not_checked_derivable profile T Gamma A.
Proof.
  intros profile T Gamma A.
  unfold symbolic_regulator_not_derivable,
    finite_axiom_set_not_checked_derivable.
  split; intros Hnot Hpos.
  - apply Hnot.
    apply finite_axiom_set_symbolic_derivable_iff_checked_derivable_lemma.
    exact Hpos.
  - apply Hnot.
    apply finite_axiom_set_symbolic_derivable_iff_checked_derivable_lemma.
    exact Hpos.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           REGULATOR-THEORY CLOSURE                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `regulator_theory_closure R Γ` is the output-side predicate
│          induced by the checker: a formula belongs to the closure
│          exactly when it is checked-derivable from `Γ` under
│          regulator theory `R`.
│
*)

(*                       closure_R,Γ(A) ≔ R; Γ ⊢check A                       *)

Definition regulator_theory_closure
    (R : RegulatorTheory)
    (Gamma : Context)
    : Formula -> Prop :=
  fun A => regulator_theory_checked_derivable R Gamma A.

(*
│
│          `regulator_theory_equivalent R Γ A B` is closure
│          equivalence: each implication direction is accepted by the
│          regulator-theory closure. This is the equivalence relation
│          used by regulated evaluation frames in `M001_09`.
│
*)

(*           A ≃_{R,Γ} B ≔ closure_R,Γ(A → B) ∧ closure_R,Γ(B → A)            *)

Definition regulator_theory_equivalent
    (R : RegulatorTheory)
    (Gamma : Context)
    (A B : Formula) : Prop :=
  regulator_theory_closure R Gamma (Imp A B) /\
  regulator_theory_closure R Gamma (Imp B A).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CLOSURE PRINCIPLES                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The sole closure principle exported here is modus ponens.
│          It is the checked MP composition theorem restated under the
│          closure predicate, and it is the regulator instance
│          consumed by L001's collapse argument.
│
*)

(*             closure_R,Γ(A→B) ∧ closure_R,Γ(A) ⇒ closure_R,Γ(B)             *)

Lemma regulator_theory_closure_closed_under_mp_lemma :
  forall R Gamma A B,
    regulator_theory_closure R Gamma (Imp A B) ->
    regulator_theory_closure R Gamma A ->
    regulator_theory_closure R Gamma B.
Proof.
  intros R Gamma A B Himp Harg.
  unfold regulator_theory_closure in *.
  apply regulator_theory_checked_derivable_mp_lemma
    with (A := A);
    assumption.
Qed.
