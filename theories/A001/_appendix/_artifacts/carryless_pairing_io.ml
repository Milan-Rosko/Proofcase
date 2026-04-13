
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val fib_pair : int -> int * int **)

let rec fib_pair n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (0, (Stdlib.Int.succ 0)))
    (fun n' -> let (a, b) = fib_pair n' in (b, (add a b)))
    n

(** val fib : int -> int **)

let fib n =
  fst (fib_pair n)

(** val sum_fib : int list -> int **)

let rec sum_fib = function
| [] -> 0
| k :: xs' -> add (fib k) (sum_fib xs')

(** val two : int -> int **)

let two n =
  add n n

(** val two_j_minus1 : int -> int **)

let two_j_minus1 j =
  Nat.pred (two j)

(** val is_even : int -> bool **)

let rec is_even n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun k -> is_even k)
      n0)
    n

(** val is_odd : int -> bool **)

let is_odd n =
  negb (is_even n)

(** val div2 : int -> int **)

let rec div2 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun k -> Stdlib.Int.succ (div2 k))
      n0)
    n

type params =
| Build_Params of (int -> int list) * (int -> int)

(** val even_band : params -> int -> int list **)

let even_band p x =
  map two (let Build_Params (z1, _) = p in z1 x)

(** val odd_band : params -> int -> int -> int list **)

let odd_band p x y =
  map (fun j ->
    add
      (mul (Stdlib.Int.succ (Stdlib.Int.succ 0))
        (let Build_Params (_, r1) = p in r1 x))
      (two_j_minus1 j))
    (let Build_Params (z1, _) = p in z1 y)

(** val half_even_indices : int list -> int list **)

let half_even_indices zn =
  map div2 (filter is_even zn)

(** val odd_ge_B1 : int -> int -> bool **)

let odd_ge_B1 bx k =
  if is_odd k then (<=) (Stdlib.Int.succ bx) k else false

(** val decode_odd_index : int -> int -> int **)

let decode_odd_index bx k =
  div2 (Stdlib.Int.succ (sub k bx))

(** val y_indices : int -> int list -> int list **)

let y_indices bx zn =
  map (decode_odd_index bx) (filter (odd_ge_B1 bx) zn)

(** val find_r_aux : int -> int -> int -> int **)

let rec find_r_aux x k fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> k)
    (fun fuel' ->
    if Nat.ltb x (fib k) then k else find_r_aux x (Stdlib.Int.succ k) fuel')
    fuel

(** val r0 : int -> int **)

let r0 x =
  find_r_aux x 0 (Stdlib.Int.succ (Stdlib.Int.succ x))

(** val zeck_greedy_down : int -> int -> bool -> int list * int **)

let rec zeck_greedy_down k rem prev_taken =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], rem))
    (fun k' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> ([], rem))
      (fun _ ->
      if prev_taken
      then zeck_greedy_down k' rem false
      else if (<=) (fib k) rem
           then let pr = zeck_greedy_down k' (sub rem (fib k)) true in
                ((k :: (fst pr)), (snd pr))
           else zeck_greedy_down k' rem false)
      k')
    k

(** val z0 : int -> int list **)

let z0 x =
  fst (zeck_greedy_down (r0 x) x false)

(** val boundary : int -> int **)

let boundary x =
  mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) (r0 x)

(** val even_band_of : int -> int list **)

let even_band_of x =
  even_band (Build_Params (z0, r0)) x

(** val odd_band_of : int -> int -> int list **)

let odd_band_of x y =
  odd_band (Build_Params (z0, r0)) x y

(** val encode : int -> int -> int **)

let encode a b =
  sum_fib (app (odd_band_of a b) (even_band_of a))

(** val half_even_support : int list -> int list **)

let half_even_support =
  half_even_indices

(** val odd_support_indices : int -> int list -> int list **)

let odd_support_indices x zn =
  y_indices (boundary x) zn

(** val decode : int -> int * int **)

let decode c =
  let zn = z0 c in
  let x = sum_fib (half_even_support zn) in
  let y = sum_fib (odd_support_indices x zn) in (x, y)

type iO_Query =
| Pair_Query of int * int
| Inspect_Query of int

type code_Status =
| Part_Of_Injective_Function
| Dead_End

type iO_Result =
| Pair_Result of int
| Inspect_Result of (int * int) * int * code_Status

(** val check_Pairing : int -> int **)

let check_Pairing c =
  let ab = decode c in encode (fst ab) (snd ab)

(** val in_Imageb : int -> bool **)

let in_Imageb c =
  (=) (check_Pairing c) c

(** val status_Of_Code : int -> code_Status **)

let status_Of_Code c =
  if in_Imageb c then Part_Of_Injective_Function else Dead_End

(** val pair_IO : int -> int -> iO_Result **)

let pair_IO a b =
  Pair_Result (encode a b)

(** val unpair_IO : int -> iO_Result **)

let unpair_IO c =
  Inspect_Result ((decode c), (check_Pairing c), (status_Of_Code c))

(** val a001_IO : iO_Query -> iO_Result **)

let a001_IO = function
| Pair_Query (a, b) -> pair_IO a b
| Inspect_Query c -> unpair_IO c
