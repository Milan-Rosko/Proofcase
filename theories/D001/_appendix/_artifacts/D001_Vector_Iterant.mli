
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

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
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val nth_error : 'a1 list -> Big_int_Z.big_int -> 'a1 option

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

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

val normalize_state_code : Big_int_Z.big_int -> Big_int_Z.big_int

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

val initial_state2 : Big_int_Z.big_int -> Big_int_Z.big_int -> iterantState

val fetch_instruction : program -> iterantState -> instruction option

val step_state : program -> iterantState -> iterantState

val nextState : program -> Big_int_Z.big_int -> Big_int_Z.big_int

val stepb : program -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val encode_nat_list : Big_int_Z.big_int list -> Big_int_Z.big_int

val coded_list_head : Big_int_Z.big_int -> Big_int_Z.big_int

val coded_list_tail : Big_int_Z.big_int -> Big_int_Z.big_int

val coded_nth : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val code_run_last :
  (Big_int_Z.big_int -> Big_int_Z.big_int) -> Big_int_Z.big_int ->
  Big_int_Z.big_int -> Big_int_Z.big_int

val code_run_trace :
  (Big_int_Z.big_int -> Big_int_Z.big_int) -> Big_int_Z.big_int ->
  Big_int_Z.big_int -> Big_int_Z.big_int list

type abstractConfig =
  (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int

val config_to_state : abstractConfig -> iterantState

val state_to_config : iterantState -> abstractConfig

val run_steps : program -> Big_int_Z.big_int -> iterantState -> iterantState

val subtraction_program : program

val abstract_initial_config : Big_int_Z.big_int -> abstractConfig

val abstract_next : program -> abstractConfig -> abstractConfig

val abstract_run_steps :
  program -> Big_int_Z.big_int -> abstractConfig -> abstractConfig
