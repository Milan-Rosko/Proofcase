
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

(** val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec add = Big_int_Z.add_big_int

(** val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec mul = Big_int_Z.mult_big_int

(** val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec sub = (fun n m -> Big_int_Z.max_big_int Big_int_Z.zero_big_int
  (Big_int_Z.sub_big_int n m))

module Nat =
 struct
  (** val pred : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred n =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> n)
      (fun u -> u)
      n

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eqb = Big_int_Z.eq_big_int

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec leb = Big_int_Z.le_big_int

  (** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ltb n m =
    leb (Big_int_Z.succ_big_int n) m
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val fib_pair :
    Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int **)

let rec fib_pair n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> (Big_int_Z.zero_big_int, (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))
    (fun n' -> let (a, b) = fib_pair n' in (b, (add a b)))
    n

(** val fib : Big_int_Z.big_int -> Big_int_Z.big_int **)

let fib n =
  fst (fib_pair n)

(** val sum_fib : Big_int_Z.big_int list -> Big_int_Z.big_int **)

let rec sum_fib = function
| [] -> Big_int_Z.zero_big_int
| k :: xs' -> add (fib k) (sum_fib xs')

(** val two : Big_int_Z.big_int -> Big_int_Z.big_int **)

let two n =
  add n n

(** val two_j_minus1 : Big_int_Z.big_int -> Big_int_Z.big_int **)

let two_j_minus1 j =
  Nat.pred (two j)

(** val is_even : Big_int_Z.big_int -> bool **)

let rec is_even n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> true)
    (fun n0 ->
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> false)
      (fun k -> is_even k)
      n0)
    n

(** val is_odd : Big_int_Z.big_int -> bool **)

let is_odd n =
  negb (is_even n)

(** val div2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec div2 n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> Big_int_Z.zero_big_int)
    (fun n0 ->
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun k -> Big_int_Z.succ_big_int (div2 k))
      n0)
    n

type params =
| Build_Params of (Big_int_Z.big_int -> Big_int_Z.big_int list)
   * (Big_int_Z.big_int -> Big_int_Z.big_int)

(** val even_band : params -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let even_band p x =
  map two (let Build_Params (z1, _) = p in z1 x)

(** val odd_band :
    params -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let odd_band p x y =
  map (fun j ->
    add
      (mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)) (let Build_Params (_, r1) = p in r1 x))
      (two_j_minus1 j))
    (let Build_Params (z1, _) = p in z1 y)

(** val half_even_indices :
    Big_int_Z.big_int list -> Big_int_Z.big_int list **)

let half_even_indices zn =
  map div2 (filter is_even zn)

(** val odd_ge_B1 : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let odd_ge_B1 bx k =
  if is_odd k then Nat.leb (Big_int_Z.succ_big_int bx) k else false

(** val decode_odd_index :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let decode_odd_index bx k =
  div2 (Big_int_Z.succ_big_int (sub k bx))

(** val y_indices :
    Big_int_Z.big_int -> Big_int_Z.big_int list -> Big_int_Z.big_int list **)

let y_indices bx zn =
  map (decode_odd_index bx) (filter (odd_ge_B1 bx) zn)

(** val find_r_aux :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int **)

let rec find_r_aux x k fuel =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> k)
    (fun fuel' ->
    if Nat.ltb x (fib k)
    then k
    else find_r_aux x (Big_int_Z.succ_big_int k) fuel')
    fuel

(** val r0 : Big_int_Z.big_int -> Big_int_Z.big_int **)

let r0 x =
  find_r_aux x Big_int_Z.zero_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int x))

(** val zeck_greedy_down :
    Big_int_Z.big_int -> Big_int_Z.big_int -> bool -> Big_int_Z.big_int
    list * Big_int_Z.big_int **)

let rec zeck_greedy_down k rem prev_taken =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> ([], rem))
    (fun k' ->
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> ([], rem))
      (fun _ ->
      if prev_taken
      then zeck_greedy_down k' rem false
      else if Nat.leb (fib k) rem
           then let pr = zeck_greedy_down k' (sub rem (fib k)) true in
                ((k :: (fst pr)), (snd pr))
           else zeck_greedy_down k' rem false)
      k')
    k

(** val z0 : Big_int_Z.big_int -> Big_int_Z.big_int list **)

let z0 x =
  fst (zeck_greedy_down (r0 x) x false)

(** val boundary : Big_int_Z.big_int -> Big_int_Z.big_int **)

let boundary x =
  mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)) (r0 x)

(** val even_band_of : Big_int_Z.big_int -> Big_int_Z.big_int list **)

let even_band_of x =
  even_band (Build_Params (z0, r0)) x

(** val odd_band_of :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let odd_band_of x y =
  odd_band (Build_Params (z0, r0)) x y

(** val encode :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let encode a b =
  sum_fib (app (odd_band_of a b) (even_band_of a))

(** val half_even_support :
    Big_int_Z.big_int list -> Big_int_Z.big_int list **)

let half_even_support =
  half_even_indices

(** val odd_support_indices :
    Big_int_Z.big_int -> Big_int_Z.big_int list -> Big_int_Z.big_int list **)

let odd_support_indices x zn =
  y_indices (boundary x) zn

(** val decode :
    Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int **)

let decode c =
  let zn = z0 c in
  let x = sum_fib (half_even_support zn) in
  let y = sum_fib (odd_support_indices x zn) in (x, y)

type iO_Query =
| Pair_Query of Big_int_Z.big_int * Big_int_Z.big_int
| Inspect_Query of Big_int_Z.big_int

type code_Status =
| Part_Of_Injective_Function
| Dead_End

type iO_Result =
| Pair_Result of Big_int_Z.big_int
| Inspect_Result of (Big_int_Z.big_int * Big_int_Z.big_int)
   * Big_int_Z.big_int * code_Status

(** val check_Pairing : Big_int_Z.big_int -> Big_int_Z.big_int **)

let check_Pairing c =
  let ab = decode c in encode (fst ab) (snd ab)

(** val in_Imageb : Big_int_Z.big_int -> bool **)

let in_Imageb c =
  Nat.eqb (check_Pairing c) c

(** val status_Of_Code : Big_int_Z.big_int -> code_Status **)

let status_Of_Code c =
  if in_Imageb c then Part_Of_Injective_Function else Dead_End

(** val pair_IO : Big_int_Z.big_int -> Big_int_Z.big_int -> iO_Result **)

let pair_IO a b =
  Pair_Result (encode a b)

(** val unpair_IO : Big_int_Z.big_int -> iO_Result **)

let unpair_IO c =
  Inspect_Result ((decode c), (check_Pairing c), (status_Of_Code c))

(** val a001_IO : iO_Query -> iO_Result **)

let a001_IO = function
| Pair_Query (a, b) -> pair_IO a b
| Inspect_Query c -> unpair_IO c
