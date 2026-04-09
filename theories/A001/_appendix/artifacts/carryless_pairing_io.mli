
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

module Nat :
 sig
  val pred : nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val fib_pair : nat -> (nat, nat) prod

val fib : nat -> nat

val sum_fib : nat list -> nat

val two : nat -> nat

val two_j_minus1 : nat -> nat

val is_even : nat -> bool

val is_odd : nat -> bool

val div2 : nat -> nat

type params =
| Build_Params of (nat -> nat list) * (nat -> nat)

val z : params -> nat -> nat list

val r : params -> nat -> nat

val b : params -> nat -> nat

val even_band : params -> nat -> nat list

val odd_band : params -> nat -> nat -> nat list

val half_even_indices : nat list -> nat list

val odd_ge_B1 : nat -> nat -> bool

val decode_odd_index : nat -> nat -> nat

val y_indices : nat -> nat list -> nat list

val find_r_aux : nat -> nat -> nat -> nat

val r0 : nat -> nat

val zeck_greedy_down : nat -> nat -> bool -> (nat list, nat) prod

val z0 : nat -> nat list

val base_params : params

val boundary : nat -> nat

val even_band_of : nat -> nat list

val odd_band_of : nat -> nat -> nat list

val encode : nat -> nat -> nat

val half_even_support : nat list -> nat list

val odd_support_indices : nat -> nat list -> nat list

val decode : nat -> (nat, nat) prod

type iO_Query =
| Pair_Query of nat * nat
| Inspect_Query of nat

type code_Status =
| Part_Of_Injective_Function
| Dead_End

type iO_Result =
| Pair_Result of nat
| Inspect_Result of (nat, nat) prod * nat * code_Status

val paired_AB : nat -> nat -> nat

val unpaired_C : nat -> (nat, nat) prod

val check_Pairing : nat -> nat

val in_Imageb : nat -> bool

val status_Of_Code : nat -> code_Status

val pair_IO : nat -> nat -> iO_Result

val unpair_IO : nat -> iO_Result

val e001_IO : iO_Query -> iO_Result
