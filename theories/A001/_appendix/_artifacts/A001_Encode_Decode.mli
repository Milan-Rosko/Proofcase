
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

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val even : Big_int_Z.big_int -> bool

  val odd : Big_int_Z.big_int -> bool

  val div2 : Big_int_Z.big_int -> Big_int_Z.big_int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val fib_pair : Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

val fib : Big_int_Z.big_int -> Big_int_Z.big_int

val sum_fib : Big_int_Z.big_int list -> Big_int_Z.big_int

val two : Big_int_Z.big_int -> Big_int_Z.big_int

val two_j_minus1 : Big_int_Z.big_int -> Big_int_Z.big_int

type params =
| Build_Params of (Big_int_Z.big_int -> Big_int_Z.big_int list)
   * (Big_int_Z.big_int -> Big_int_Z.big_int)

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

val boundary : Big_int_Z.big_int -> Big_int_Z.big_int

val even_band_of : Big_int_Z.big_int -> Big_int_Z.big_int list

val odd_band_of :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list

val encode : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val half_even_support : Big_int_Z.big_int list -> Big_int_Z.big_int list

val odd_support_indices :
  Big_int_Z.big_int -> Big_int_Z.big_int list -> Big_int_Z.big_int list

val decode : Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int
