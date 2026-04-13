
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val pred : int -> int

  val ltb : int -> int -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val fib_pair : int -> int * int

val fib : int -> int

val sum_fib : int list -> int

val two : int -> int

val two_j_minus1 : int -> int

val is_even : int -> bool

val is_odd : int -> bool

val div2 : int -> int

type params =
| Build_Params of (int -> int list) * (int -> int)

val even_band : params -> int -> int list

val odd_band : params -> int -> int -> int list

val half_even_indices : int list -> int list

val odd_ge_B1 : int -> int -> bool

val decode_odd_index : int -> int -> int

val y_indices : int -> int list -> int list

val find_r_aux : int -> int -> int -> int

val r0 : int -> int

val zeck_greedy_down : int -> int -> bool -> int list * int

val z0 : int -> int list

val boundary : int -> int

val even_band_of : int -> int list

val odd_band_of : int -> int -> int list

val encode : int -> int -> int

val half_even_support : int list -> int list

val odd_support_indices : int -> int list -> int list

val decode : int -> int * int

type iO_Query =
| Pair_Query of int * int
| Inspect_Query of int

type code_Status =
| Part_Of_Injective_Function
| Dead_End

type iO_Result =
| Pair_Result of int
| Inspect_Result of (int * int) * int * code_Status

val check_Pairing : int -> int

val in_Imageb : int -> bool

val status_Of_Code : int -> code_Status

val pair_IO : int -> int -> iO_Result

val unpair_IO : int -> iO_Result

val a001_IO : iO_Query -> iO_Result
