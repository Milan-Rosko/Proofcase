
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> Big_int_Z.big_int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

module Nat :
 sig
  val pred : Big_int_Z.big_int -> Big_int_Z.big_int

  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val max : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val nth_error : 'a1 list -> Big_int_Z.big_int -> 'a1 option

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type monomial =
| M_const
| M_linear of Big_int_Z.big_int
| M_quadratic of Big_int_Z.big_int * Big_int_Z.big_int
| M_cubic of Big_int_Z.big_int * Big_int_Z.big_int * Big_int_Z.big_int

type term = { coeff : Big_int_Z.big_int; mono : monomial }

type h10_nd3n_equation = { var_count : Big_int_Z.big_int;
                           lhs_terms : term list; rhs_terms : term list }

type cubic_family_instance = h10_nd3n_equation list

val fib_pair : Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

val fib : Big_int_Z.big_int -> Big_int_Z.big_int

val sum_fib : Big_int_Z.big_int list -> Big_int_Z.big_int

val two : Big_int_Z.big_int -> Big_int_Z.big_int

val two_j_minus1 : Big_int_Z.big_int -> Big_int_Z.big_int

val is_even : Big_int_Z.big_int -> bool

val is_odd : Big_int_Z.big_int -> bool

val div2 : Big_int_Z.big_int -> Big_int_Z.big_int

type params =
| Build_Params of (Big_int_Z.big_int -> Big_int_Z.big_int list)
   * (Big_int_Z.big_int -> Big_int_Z.big_int)

val z : params -> Big_int_Z.big_int -> Big_int_Z.big_int list

val r : params -> Big_int_Z.big_int -> Big_int_Z.big_int

val b : params -> Big_int_Z.big_int -> Big_int_Z.big_int

val even_band : params -> Big_int_Z.big_int -> Big_int_Z.big_int list

val odd_band :
  params -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list

val half_even_indices : Big_int_Z.big_int list -> Big_int_Z.big_int list

val odd_ge_B1 : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val decode_odd_index :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val y_indices :
  Big_int_Z.big_int -> Big_int_Z.big_int list -> Big_int_Z.big_int list

val find_r_aux :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int

val r0 : Big_int_Z.big_int -> Big_int_Z.big_int

val zeck_greedy_down :
  Big_int_Z.big_int -> Big_int_Z.big_int -> bool -> Big_int_Z.big_int
  list * Big_int_Z.big_int

val z0 : Big_int_Z.big_int -> Big_int_Z.big_int list

val base_params : params

val boundary : Big_int_Z.big_int -> Big_int_Z.big_int

val even_band_of : Big_int_Z.big_int -> Big_int_Z.big_int list

val odd_band_of :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list

val encode : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val half_even_support : Big_int_Z.big_int list -> Big_int_Z.big_int list

val odd_support_indices :
  Big_int_Z.big_int -> Big_int_Z.big_int list -> Big_int_Z.big_int list

val decode : Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

val k_IP : Big_int_Z.big_int

val k_R1 : Big_int_Z.big_int

val k_R2 : Big_int_Z.big_int

val iP_offset : Big_int_Z.big_int

val r1_offset : Big_int_Z.big_int

val r2_offset : Big_int_Z.big_int

val band_support :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list

val band_pred :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val band_indices :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list ->
  Big_int_Z.big_int list

val ip_support : Big_int_Z.big_int -> Big_int_Z.big_int list

val r1_support : Big_int_Z.big_int -> Big_int_Z.big_int list

val r2_support : Big_int_Z.big_int -> Big_int_Z.big_int list

type iterantState = { state_ip : Big_int_Z.big_int;
                      state_r1 : Big_int_Z.big_int;
                      state_r2 : Big_int_Z.big_int }

val state_support : iterantState -> Big_int_Z.big_int list

val encode_state : iterantState -> Big_int_Z.big_int

val decode_ip_from_support : Big_int_Z.big_int list -> Big_int_Z.big_int

val decode_r1_from_support : Big_int_Z.big_int list -> Big_int_Z.big_int

val decode_r2_from_support : Big_int_Z.big_int list -> Big_int_Z.big_int

val decode_state_from_support : Big_int_Z.big_int list -> iterantState

val decode_state : Big_int_Z.big_int -> iterantState

type counter =
| Counter1
| Counter2

type instruction =
| INC of counter * Big_int_Z.big_int
| JZDEC of counter * Big_int_Z.big_int * Big_int_Z.big_int
| HALT

type program = instruction list

val read_counter : counter -> iterantState -> Big_int_Z.big_int

val write_counter :
  counter -> Big_int_Z.big_int -> iterantState -> iterantState

val set_ip : Big_int_Z.big_int -> iterantState -> iterantState

val initial_state : Big_int_Z.big_int -> iterantState

val fetch_instruction : program -> iterantState -> instruction option

val step_state : program -> iterantState -> iterantState

val nextState : program -> Big_int_Z.big_int -> Big_int_Z.big_int

val stepb : program -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val encode_nat_list : Big_int_Z.big_int list -> Big_int_Z.big_int

val coded_list_head : Big_int_Z.big_int -> Big_int_Z.big_int

val coded_list_tail : Big_int_Z.big_int -> Big_int_Z.big_int

val coded_nth : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

type machineState = iterantState

type machineProgram = program

type encodedState = Big_int_Z.big_int

val current_state : encodedState -> machineState

val halted_state_b : machineState -> bool

val halted_code_b : encodedState -> bool

val stepCode : machineProgram -> encodedState -> encodedState

val step_matches_b : machineProgram -> encodedState -> encodedState -> bool

type codeTrace = encodedState list

val encode_code_trace : codeTrace -> Big_int_Z.big_int

val code_trace_head : Big_int_Z.big_int -> Big_int_Z.big_int

val code_trace_tail : Big_int_Z.big_int -> Big_int_Z.big_int

val code_trace_nth :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val decode_code_trace_bounded :
  Big_int_Z.big_int -> Big_int_Z.big_int -> codeTrace

val decode_code_trace : Big_int_Z.big_int -> codeTrace

val start_code : Big_int_Z.big_int -> encodedState

val codeTraceStartsFrom_b : encodedState -> codeTrace -> bool

val validCodeTrace_b : machineProgram -> codeTrace -> bool

val codeTraceStartsWith_b : Big_int_Z.big_int -> codeTrace -> bool

val codeTraceWitness_b :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val fMValidTrace_b :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool

type equation_family = cubic_family_instance

val cubic_monomial_count : monomial -> Big_int_Z.big_int

val cubic_term_count : term -> Big_int_Z.big_int

val cubic_poly_count : term list -> Big_int_Z.big_int

val cubic_equation_count : h10_nd3n_equation -> Big_int_Z.big_int

val cubic_family_count : cubic_family_instance -> Big_int_Z.big_int

val family_var_bound : cubic_family_instance -> Big_int_Z.big_int

type traceConstraintFamily = equation_family

val trace_witness_length : Big_int_Z.big_int -> Big_int_Z.big_int

val trace_witness_step_count : Big_int_Z.big_int -> Big_int_Z.big_int

val trace_witness_last_code : Big_int_Z.big_int -> Big_int_Z.big_int

val emit_linear_const_equation :
  Big_int_Z.big_int -> Big_int_Z.big_int -> h10_nd3n_equation

val emit_false_equation : h10_nd3n_equation

val emit_trace_shape_family_upto :
  Big_int_Z.big_int -> Big_int_Z.big_int -> equation_family

val emit_trace_shape_family :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int -> equation_family

val emit_trace_start_family :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int -> equation_family

val emit_trace_step_family_upto :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int -> equation_family

val emit_trace_step_family :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int -> equation_family

val emit_trace_halt_family :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int -> equation_family

val emit_trace_family :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  traceConstraintFamily

val search_FMValidTrace_upto :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int option

val emit_bounded_witness_search_family :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  traceConstraintFamily

val compile_fm_family_upto :
  machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  cubic_family_instance
