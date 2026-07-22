
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val pred : nat -> nat

val add : nat -> nat -> nat

module Nat :
 sig
  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val nth_error : 'a1 list -> nat -> 'a1 option

type formula =
| Bot
| Imp of formula * formula

type context = formula list

type axiomSet =
  formula -> bool
  (* singleton inductive, whose constructor was Build_AxiomSet *)

type finiteAxiomSet =
  formula list
  (* singleton inductive, whose constructor was Build_FiniteAxiomSet *)

type regulatorLogicProfile =
| Regulator_profile_minimal
| Regulator_profile_with_efq

type regulatorTheory = { regulator_theory_profile : regulatorLogicProfile;
                         regulator_theory_axiom_set : axiomSet }

val regulator_theory_with_axiom_set :
  regulatorLogicProfile -> axiomSet -> regulatorTheory

type justification =
| J_Assumption
| J_Axiom
| J_MP of nat * nat

type proofLine = { line_formula : formula; line_justification : justification }

type proof = proofLine list

val formula_eq_bool : formula -> formula -> bool

val ctx_mem_bool : formula -> context -> bool

val finite_axiom_set_contains_bool : finiteAxiomSet -> formula -> bool

val finite_axiom_set_to_axiom_set : finiteAxiomSet -> axiomSet

val k_axiom_bool : formula -> bool

val s_axiom_bool : formula -> bool

val efq_axiom_bool : formula -> bool

val logical_axiom_bool : regulatorLogicProfile -> formula -> bool

val available_axiom_bool : regulatorTheory -> formula -> bool

val nth_formula : proofLine list -> nat -> formula option

val pl_assumption : formula -> proofLine

val pl_axiom : formula -> proofLine

val pl_mp : formula -> nat -> nat -> proofLine

val last_formula : proof -> formula option

val mp_orientation_left_bool : formula -> formula -> formula -> bool

val mp_orientation_right_bool : formula -> formula -> formula -> bool

val mp_valid_bool : proofLine list -> nat -> nat -> formula -> bool

val proof_line_valid_bool :
  regulatorTheory -> context -> proofLine list -> proofLine -> bool

val proof_script_check_from_bool :
  regulatorTheory -> context -> proofLine list -> proofLine list -> bool

val regulator_theory_check_bool :
  regulatorTheory -> context -> proof -> formula -> bool

val finite_axiom_set_to_regulator_theory :
  regulatorLogicProfile -> finiteAxiomSet -> regulatorTheory

val finite_axiom_set_check_bool :
  regulatorLogicProfile -> finiteAxiomSet -> context -> proof -> formula ->
  bool

val k_axiom_formula : formula -> formula -> formula

val s_axiom_formula : formula -> formula -> formula -> formula

val deduction_identity_block_from : nat -> formula -> proof

val deduction_assumption_lift_block_from : nat -> formula -> formula -> proof

val deduction_axiom_lift_block_from : nat -> formula -> formula -> proof

val deduction_mp_lift_block_from :
  nat -> formula -> formula -> formula -> nat -> nat -> proof

type deductionState = { deduction_state_output : proof;
                        deduction_state_index_map : nat list }

val deduction_state_empty : deductionState

val deduction_state_next_index : deductionState -> nat

val deduction_state_append_block :
  deductionState -> proof -> nat -> deductionState

val deduction_state_append_identity :
  formula -> deductionState -> deductionState

val deduction_state_append_assumption_lift :
  formula -> formula -> deductionState -> deductionState

val deduction_state_append_axiom_lift :
  formula -> formula -> deductionState -> deductionState

val deduction_state_append_mp_lift :
  formula -> formula -> formula -> nat -> nat -> deductionState ->
  deductionState

val deduction_transform_mp_line :
  formula -> formula -> proofLine list -> nat -> nat -> deductionState ->
  deductionState

val deduction_transform_line :
  formula -> proofLine list -> proofLine -> deductionState -> deductionState

val deduction_transform_lines :
  formula -> proofLine list -> proofLine list -> deductionState ->
  deductionState

val regulator_theory_deduction_transform : formula -> proof -> proof

val regulator_theory_reductio_transform : formula -> proof -> proof

val proof_script_shift_index : nat -> nat -> nat

val proof_script_shift_justification : nat -> justification -> justification

val proof_script_shift_line : nat -> proofLine -> proofLine

val proof_script_shift : nat -> proof -> proof

val proof_script_last_index : proof -> nat

val regulator_theory_mp_compose : formula -> proof -> proof -> proof
