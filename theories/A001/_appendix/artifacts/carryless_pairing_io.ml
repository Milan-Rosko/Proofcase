
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

module Nat =
 struct
  (** val pred : nat -> nat **)

  let pred n = match n with
  | O -> n
  | S u -> u

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f a), (map f l0))

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| Nil -> Nil
| Cons (x, l0) ->
  (match f x with
   | True -> Cons (x, (filter f l0))
   | False -> filter f l0)

(** val fib_pair : nat -> (nat, nat) prod **)

let rec fib_pair = function
| O -> Pair (O, (S O))
| S n' -> let Pair (a, b0) = fib_pair n' in Pair (b0, (add a b0))

(** val fib : nat -> nat **)

let fib n =
  fst (fib_pair n)

(** val sum_fib : nat list -> nat **)

let rec sum_fib = function
| Nil -> O
| Cons (k, xs') -> add (fib k) (sum_fib xs')

(** val two : nat -> nat **)

let two n =
  add n n

(** val two_j_minus1 : nat -> nat **)

let two_j_minus1 j =
  Nat.pred (two j)

(** val is_even : nat -> bool **)

let rec is_even = function
| O -> True
| S n0 -> (match n0 with
           | O -> False
           | S k -> is_even k)

(** val is_odd : nat -> bool **)

let is_odd n =
  negb (is_even n)

(** val div2 : nat -> nat **)

let rec div2 = function
| O -> O
| S n0 -> (match n0 with
           | O -> O
           | S k -> S (div2 k))

type params =
| Build_Params of (nat -> nat list) * (nat -> nat)

(** val z : params -> nat -> nat list **)

let z = function
| Build_Params (z1, _) -> z1

(** val r : params -> nat -> nat **)

let r = function
| Build_Params (_, r1) -> r1

(** val b : params -> nat -> nat **)

let b p x =
  mul (S (S O)) (r p x)

(** val even_band : params -> nat -> nat list **)

let even_band p x =
  map two (z p x)

(** val odd_band : params -> nat -> nat -> nat list **)

let odd_band p x y =
  map (fun j -> add (b p x) (two_j_minus1 j)) (z p y)

(** val half_even_indices : nat list -> nat list **)

let half_even_indices zn =
  map div2 (filter is_even zn)

(** val odd_ge_B1 : nat -> nat -> bool **)

let odd_ge_B1 bx k =
  match is_odd k with
  | True -> Nat.leb (S bx) k
  | False -> False

(** val decode_odd_index : nat -> nat -> nat **)

let decode_odd_index bx k =
  div2 (S (sub k bx))

(** val y_indices : nat -> nat list -> nat list **)

let y_indices bx zn =
  map (decode_odd_index bx) (filter (odd_ge_B1 bx) zn)

(** val find_r_aux : nat -> nat -> nat -> nat **)

let rec find_r_aux x k = function
| O -> k
| S fuel' ->
  (match Nat.ltb x (fib k) with
   | True -> k
   | False -> find_r_aux x (S k) fuel')

(** val r0 : nat -> nat **)

let r0 x =
  find_r_aux x O (S (S x))

(** val zeck_greedy_down : nat -> nat -> bool -> (nat list, nat) prod **)

let rec zeck_greedy_down k rem prev_taken =
  match k with
  | O -> Pair (Nil, rem)
  | S k' ->
    (match k' with
     | O -> Pair (Nil, rem)
     | S _ ->
       (match prev_taken with
        | True -> zeck_greedy_down k' rem False
        | False ->
          (match Nat.leb (fib k) rem with
           | True ->
             let pr = zeck_greedy_down k' (sub rem (fib k)) True in
             Pair ((Cons (k, (fst pr))), (snd pr))
           | False -> zeck_greedy_down k' rem False)))

(** val z0 : nat -> nat list **)

let z0 x =
  fst (zeck_greedy_down (r0 x) x False)

(** val base_params : params **)

let base_params =
  Build_Params (z0, r0)

(** val boundary : nat -> nat **)

let boundary x =
  b base_params x

(** val even_band_of : nat -> nat list **)

let even_band_of x =
  even_band base_params x

(** val odd_band_of : nat -> nat -> nat list **)

let odd_band_of x y =
  odd_band base_params x y

(** val encode : nat -> nat -> nat **)

let encode a b0 =
  sum_fib (app (odd_band_of a b0) (even_band_of a))

(** val half_even_support : nat list -> nat list **)

let half_even_support =
  half_even_indices

(** val odd_support_indices : nat -> nat list -> nat list **)

let odd_support_indices x zn =
  y_indices (boundary x) zn

(** val decode : nat -> (nat, nat) prod **)

let decode c =
  let zn = z0 c in
  let x = sum_fib (half_even_support zn) in
  let y = sum_fib (odd_support_indices x zn) in Pair (x, y)

type iO_Query =
| Pair_Query of nat * nat
| Inspect_Query of nat

type code_Status =
| Part_Of_Injective_Function
| Dead_End

type iO_Result =
| Pair_Result of nat
| Inspect_Result of (nat, nat) prod * nat * code_Status

(** val paired_AB : nat -> nat -> nat **)

let paired_AB =
  encode

(** val unpaired_C : nat -> (nat, nat) prod **)

let unpaired_C =
  decode

(** val check_Pairing : nat -> nat **)

let check_Pairing c =
  let ab = unpaired_C c in paired_AB (fst ab) (snd ab)

(** val in_Imageb : nat -> bool **)

let in_Imageb c =
  Nat.eqb (check_Pairing c) c

(** val status_Of_Code : nat -> code_Status **)

let status_Of_Code c =
  match in_Imageb c with
  | True -> Part_Of_Injective_Function
  | False -> Dead_End

(** val pair_IO : nat -> nat -> iO_Result **)

let pair_IO a b0 =
  Pair_Result (paired_AB a b0)

(** val unpair_IO : nat -> iO_Result **)

let unpair_IO c =
  Inspect_Result ((unpaired_C c), (check_Pairing c), (status_Of_Code c))

(** val e001_IO : iO_Query -> iO_Result **)

let e001_IO = function
| Pair_Query (a, b0) -> pair_IO a b0
| Inspect_Query c -> unpair_IO c
