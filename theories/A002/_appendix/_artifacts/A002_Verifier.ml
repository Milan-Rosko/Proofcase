
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

(** val length : 'a1 list -> Big_int_Z.big_int **)

let rec length = function
| [] -> Big_int_Z.zero_big_int
| _ :: l' -> Big_int_Z.succ_big_int (length l')

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

  (** val max :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec max n m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> n)
        (fun m' -> Big_int_Z.succ_big_int (max n' m'))
        m)
      n

  (** val even : Big_int_Z.big_int -> bool **)

  let rec even n =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> true)
      (fun n0 ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> false)
        (fun n' -> even n')
        n0)
      n

  (** val odd : Big_int_Z.big_int -> bool **)

  let odd n =
    negb (even n)

  (** val div2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec div2 = (fun n -> Big_int_Z.div_big_int n (Big_int_Z.big_int_of_int 2))
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val nth_error : 'a1 list -> Big_int_Z.big_int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l' -> nth_error l' n0)
    n

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
    (fun n' -> let (a, b0) = fib_pair n' in (b0, (add a b0)))
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

type params =
| Build_Params of (Big_int_Z.big_int -> Big_int_Z.big_int list)
   * (Big_int_Z.big_int -> Big_int_Z.big_int)

(** val z : params -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let z = function
| Build_Params (z1, _) -> z1

(** val r : params -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let r = function
| Build_Params (_, r1) -> r1

(** val b : params -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let b p x =
  mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)) (r p x)

(** val even_band : params -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let even_band p x =
  map two (z p x)

(** val odd_band :
    params -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let odd_band p x y =
  map (fun j -> add (b p x) (two_j_minus1 j)) (z p y)

(** val half_even_indices :
    Big_int_Z.big_int list -> Big_int_Z.big_int list **)

let half_even_indices zn =
  map Nat.div2 (filter Nat.even zn)

(** val odd_ge_B1 : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let odd_ge_B1 bx k =
  (&&) (Nat.odd k) (Nat.leb (Big_int_Z.succ_big_int bx) k)

(** val decode_odd_index :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let decode_odd_index bx k =
  Nat.div2 (Big_int_Z.succ_big_int (sub k bx))

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

(** val base_params : params **)

let base_params =
  Build_Params (z0, r0)

(** val boundary : Big_int_Z.big_int -> Big_int_Z.big_int **)

let boundary x =
  b base_params x

(** val even_band_of : Big_int_Z.big_int -> Big_int_Z.big_int list **)

let even_band_of x =
  even_band base_params x

(** val odd_band_of :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let odd_band_of x y =
  odd_band base_params x y

(** val encode :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let encode a b0 =
  sum_fib (app (odd_band_of a b0) (even_band_of a))

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

(** val sTATUS_REJECT : Big_int_Z.big_int **)

let sTATUS_REJECT =
  Big_int_Z.zero_big_int

(** val sTATUS_ACCEPT : Big_int_Z.big_int **)

let sTATUS_ACCEPT =
  Big_int_Z.succ_big_int Big_int_Z.zero_big_int

(** val accept : Big_int_Z.big_int -> Big_int_Z.big_int **)

let accept payload =
  encode sTATUS_ACCEPT payload

(** val code_error :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int **)

let code_error stage index detail =
  encode stage (encode index detail)

(** val reject :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int **)

let reject stage index detail =
  encode sTATUS_REJECT (code_error stage index detail)

(** val sTAGE_DERIVATION_HEADER : Big_int_Z.big_int **)

let sTAGE_DERIVATION_HEADER =
  Big_int_Z.zero_big_int

(** val sTAGE_LIST_STRUCTURE : Big_int_Z.big_int **)

let sTAGE_LIST_STRUCTURE =
  Big_int_Z.succ_big_int Big_int_Z.zero_big_int

(** val sTAGE_LINE : Big_int_Z.big_int **)

let sTAGE_LINE =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

(** val sTAGE_TAG : Big_int_Z.big_int **)

let sTAGE_TAG =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))

(** val sTAGE_FORMULA : Big_int_Z.big_int **)

let sTAGE_FORMULA =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))

(** val sTAGE_RULE : Big_int_Z.big_int **)

let sTAGE_RULE =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))

(** val sTAGE_CONCLUSION : Big_int_Z.big_int **)

let sTAGE_CONCLUSION =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))

(** val eRR_NONCANONICAL_DERIVATION : Big_int_Z.big_int **)

let eRR_NONCANONICAL_DERIVATION =
  Big_int_Z.zero_big_int

(** val eRR_BAD_DERIVATION_LENGTH : Big_int_Z.big_int **)

let eRR_BAD_DERIVATION_LENGTH =
  Big_int_Z.succ_big_int Big_int_Z.zero_big_int

(** val eRR_EMPTY_DERIVATION : Big_int_Z.big_int **)

let eRR_EMPTY_DERIVATION =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

(** val eRR_BAD_CONCLUSION : Big_int_Z.big_int **)

let eRR_BAD_CONCLUSION =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))

(** val eRR_FUEL_EXHAUSTED : Big_int_Z.big_int **)

let eRR_FUEL_EXHAUSTED =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))

(** val eRR_NONCANONICAL_NODE : Big_int_Z.big_int **)

let eRR_NONCANONICAL_NODE =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))

(** val eRR_BAD_TAG : Big_int_Z.big_int **)

let eRR_BAD_TAG =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))

(** val eRR_BAD_LIST_TAG : Big_int_Z.big_int **)

let eRR_BAD_LIST_TAG =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))))

(** val eRR_INDEX_OUT_OF_RANGE : Big_int_Z.big_int **)

let eRR_INDEX_OUT_OF_RANGE =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)))))))))

(** val eRR_NONCANONICAL_LINE : Big_int_Z.big_int **)

let eRR_NONCANONICAL_LINE =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))

(** val eRR_UNKNOWN_RULE : Big_int_Z.big_int **)

let eRR_UNKNOWN_RULE =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))))))))))

(** val eRR_NORMALIZED_STEP_REJECTED : Big_int_Z.big_int **)

let eRR_NORMALIZED_STEP_REJECTED =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))

(** val eRR_NONCANONICAL_FORMULA : Big_int_Z.big_int **)

let eRR_NONCANONICAL_FORMULA =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))

(** val eRR_BAD_IMP_PAYLOAD : Big_int_Z.big_int **)

let eRR_BAD_IMP_PAYLOAD =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))

(** val eRR_NOT_IMP : Big_int_Z.big_int **)

let eRR_NOT_IMP =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))

(** val eRR_AXK_NOT_IMP_1 : Big_int_Z.big_int **)

let eRR_AXK_NOT_IMP_1 =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))

(** val eRR_AXK_NOT_IMP_2 : Big_int_Z.big_int **)

let eRR_AXK_NOT_IMP_2 =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXK_A_MISMATCH : Big_int_Z.big_int **)

let eRR_AXK_A_MISMATCH =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXK_BAD_A : Big_int_Z.big_int **)

let eRR_AXK_BAD_A =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXK_BAD_B : Big_int_Z.big_int **)

let eRR_AXK_BAD_B =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_NOT_IMP_1 : Big_int_Z.big_int **)

let eRR_AXS_NOT_IMP_1 =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_NOT_IMP_2 : Big_int_Z.big_int **)

let eRR_AXS_NOT_IMP_2 =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_NOT_IMP_3 : Big_int_Z.big_int **)

let eRR_AXS_NOT_IMP_3 =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_NOT_IMP_4 : Big_int_Z.big_int **)

let eRR_AXS_NOT_IMP_4 =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_NOT_IMP_5 : Big_int_Z.big_int **)

let eRR_AXS_NOT_IMP_5 =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_NOT_IMP_6 : Big_int_Z.big_int **)

let eRR_AXS_NOT_IMP_6 =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_A_MISMATCH_LEFT : Big_int_Z.big_int **)

let eRR_AXS_A_MISMATCH_LEFT =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_A_MISMATCH_RIGHT : Big_int_Z.big_int **)

let eRR_AXS_A_MISMATCH_RIGHT =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_B_MISMATCH : Big_int_Z.big_int **)

let eRR_AXS_B_MISMATCH =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_C_MISMATCH : Big_int_Z.big_int **)

let eRR_AXS_C_MISMATCH =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_BAD_A : Big_int_Z.big_int **)

let eRR_AXS_BAD_A =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_BAD_B : Big_int_Z.big_int **)

let eRR_AXS_BAD_B =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_AXS_BAD_C : Big_int_Z.big_int **)

let eRR_AXS_BAD_C =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_MP_P_NOT_LT_J : Big_int_Z.big_int **)

let eRR_MP_P_NOT_LT_J =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_MP_Q_NOT_LT_J : Big_int_Z.big_int **)

let eRR_MP_Q_NOT_LT_J =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_MP_BAD_LINE_J : Big_int_Z.big_int **)

let eRR_MP_BAD_LINE_J =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_MP_BAD_LINE_P : Big_int_Z.big_int **)

let eRR_MP_BAD_LINE_P =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_MP_BAD_LINE_Q : Big_int_Z.big_int **)

let eRR_MP_BAD_LINE_Q =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_MP_Q_NOT_IMP : Big_int_Z.big_int **)

let eRR_MP_Q_NOT_IMP =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_MP_ANTECEDENT_MISMATCH : Big_int_Z.big_int **)

let eRR_MP_ANTECEDENT_MISMATCH =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_MP_CONSEQUENT_MISMATCH : Big_int_Z.big_int **)

let eRR_MP_CONSEQUENT_MISMATCH =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val fst001 : Big_int_Z.big_int -> Big_int_Z.big_int **)

let fst001 c =
  fst (decode c)

(** val snd001 : Big_int_Z.big_int -> Big_int_Z.big_int **)

let snd001 c =
  snd (decode c)

(** val recode001 : Big_int_Z.big_int -> Big_int_Z.big_int **)

let recode001 c =
  encode (fst001 c) (snd001 c)

(** val canonical001b : Big_int_Z.big_int -> bool **)

let canonical001b c =
  Nat.eqb (recode001 c) c

(** val is_pair001b :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let is_pair001b c a b0 =
  (&&) ((&&) (canonical001b c) (Nat.eqb (fst001 c) a)) (Nat.eqb (snd001 c) b0)

(** val tAG_NIL : Big_int_Z.big_int **)

let tAG_NIL =
  Big_int_Z.zero_big_int

(** val tAG_CONS : Big_int_Z.big_int **)

let tAG_CONS =
  Big_int_Z.succ_big_int Big_int_Z.zero_big_int

(** val code_nil : Big_int_Z.big_int **)

let code_nil =
  encode tAG_NIL Big_int_Z.zero_big_int

(** val code_cons :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_cons h t =
  encode tAG_CONS (encode h t)

(** val code_derivation :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_derivation =
  encode

(** val list_tag : Big_int_Z.big_int -> Big_int_Z.big_int **)

let list_tag =
  fst001

(** val list_payload : Big_int_Z.big_int -> Big_int_Z.big_int **)

let list_payload =
  snd001

(** val is_nil_nodeb : Big_int_Z.big_int -> bool **)

let is_nil_nodeb body =
  is_pair001b body tAG_NIL Big_int_Z.zero_big_int

(** val cons_payloadb : Big_int_Z.big_int -> bool **)

let cons_payloadb =
  canonical001b

(** val list_exact_lengthb :
    Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let rec list_exact_lengthb n body =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> is_nil_nodeb body)
    (fun n' ->
    if canonical001b body
    then if Nat.eqb (list_tag body) tAG_CONS
         then let payload = list_payload body in
              if cons_payloadb payload
              then list_exact_lengthb n' (snd001 payload)
              else false
         else false
    else false)
    n

(** val nth_list_fuel :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int **)

let rec nth_list_fuel fuel body i =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> reject sTAGE_LIST_STRUCTURE i eRR_FUEL_EXHAUSTED)
    (fun fuel' ->
    if canonical001b body
    then let tag = list_tag body in
         let payload = list_payload body in
         if Nat.eqb tag tAG_CONS
         then if cons_payloadb payload
              then let h = fst001 payload in
                   let t = snd001 payload in
                   if Nat.eqb i Big_int_Z.zero_big_int
                   then accept h
                   else nth_list_fuel fuel' t (Nat.pred i)
              else reject sTAGE_LIST_STRUCTURE i eRR_NONCANONICAL_NODE
         else if Nat.eqb tag tAG_NIL
              then reject sTAGE_LIST_STRUCTURE i eRR_INDEX_OUT_OF_RANGE
              else reject sTAGE_LIST_STRUCTURE i eRR_BAD_LIST_TAG
    else reject sTAGE_LIST_STRUCTURE i eRR_NONCANONICAL_NODE)
    fuel

(** val tAG_VAR : Big_int_Z.big_int **)

let tAG_VAR =
  Big_int_Z.zero_big_int

(** val tAG_IMP : Big_int_Z.big_int **)

let tAG_IMP =
  Big_int_Z.succ_big_int Big_int_Z.zero_big_int

(** val code_var : Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_var i =
  encode tAG_VAR i

(** val code_imp :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_imp a b0 =
  encode tAG_IMP (encode a b0)

(** val formula_tag : Big_int_Z.big_int -> Big_int_Z.big_int **)

let formula_tag =
  fst001

(** val formula_payload : Big_int_Z.big_int -> Big_int_Z.big_int **)

let formula_payload =
  snd001

(** val is_formula_fuel : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let rec is_formula_fuel fuel c =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> false)
    (fun fuel' ->
    if canonical001b c
    then let tag = formula_tag c in
         let payload = formula_payload c in
         if Nat.eqb tag tAG_VAR
         then true
         else if Nat.eqb tag tAG_IMP
              then if canonical001b payload
                   then (&&) (is_formula_fuel fuel' (fst001 payload))
                          (is_formula_fuel fuel' (snd001 payload))
                   else false
              else false
    else false)
    fuel

(** val formula_bound : Big_int_Z.big_int -> Big_int_Z.big_int **)

let formula_bound c =
  Big_int_Z.succ_big_int c

(** val is_formula : Big_int_Z.big_int -> bool **)

let is_formula c =
  is_formula_fuel (formula_bound c) c

(** val parse_imp : Big_int_Z.big_int -> Big_int_Z.big_int **)

let parse_imp phi =
  if canonical001b phi
  then let tag = formula_tag phi in
       let payload = formula_payload phi in
       if Nat.eqb tag tAG_IMP
       then if canonical001b payload
            then accept payload
            else reject sTAGE_FORMULA Big_int_Z.zero_big_int
                   eRR_BAD_IMP_PAYLOAD
       else reject sTAGE_FORMULA Big_int_Z.zero_big_int eRR_NOT_IMP
  else reject sTAGE_FORMULA Big_int_Z.zero_big_int eRR_NONCANONICAL_FORMULA

(** val code_line :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_line =
  encode

(** val line_tag : Big_int_Z.big_int -> Big_int_Z.big_int **)

let line_tag =
  fst001

(** val line_formula : Big_int_Z.big_int -> Big_int_Z.big_int **)

let line_formula =
  snd001

(** val rULE_AXK : Big_int_Z.big_int **)

let rULE_AXK =
  Big_int_Z.zero_big_int

(** val rULE_AXS : Big_int_Z.big_int **)

let rULE_AXS =
  Big_int_Z.succ_big_int Big_int_Z.zero_big_int

(** val rULE_MP : Big_int_Z.big_int **)

let rULE_MP =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

(** val tag_axk : Big_int_Z.big_int **)

let tag_axk =
  encode rULE_AXK Big_int_Z.zero_big_int

(** val tag_axs : Big_int_Z.big_int **)

let tag_axs =
  encode rULE_AXS Big_int_Z.zero_big_int

(** val tag_mp :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let tag_mp p q =
  encode rULE_MP (encode p q)

(** val rule_code : Big_int_Z.big_int -> Big_int_Z.big_int **)

let rule_code =
  fst001

(** val rule_payload : Big_int_Z.big_int -> Big_int_Z.big_int **)

let rule_payload =
  snd001

(** val parse_rule_tag : Big_int_Z.big_int -> Big_int_Z.big_int **)

let parse_rule_tag tag =
  if canonical001b tag
  then let rule = rule_code tag in
       let payload = rule_payload tag in
       if Nat.eqb rule rULE_AXK
       then if Nat.eqb payload Big_int_Z.zero_big_int
            then accept (encode rULE_AXK Big_int_Z.zero_big_int)
            else reject sTAGE_TAG Big_int_Z.zero_big_int eRR_BAD_TAG
       else if Nat.eqb rule rULE_AXS
            then if Nat.eqb payload Big_int_Z.zero_big_int
                 then accept (encode rULE_AXS Big_int_Z.zero_big_int)
                 else reject sTAGE_TAG Big_int_Z.zero_big_int eRR_BAD_TAG
            else if Nat.eqb rule rULE_MP
                 then if canonical001b payload
                      then accept (encode rULE_MP payload)
                      else reject sTAGE_TAG Big_int_Z.zero_big_int
                             eRR_NONCANONICAL_NODE
                 else reject sTAGE_TAG Big_int_Z.zero_big_int eRR_UNKNOWN_RULE
  else reject sTAGE_TAG Big_int_Z.zero_big_int eRR_BAD_TAG

(** val parse_line : Big_int_Z.big_int -> Big_int_Z.big_int **)

let parse_line ell =
  if canonical001b ell
  then let tag = line_tag ell in
       let phi = line_formula ell in
       let parsed_tag = parse_rule_tag tag in
       if Nat.eqb (fst001 parsed_tag) sTATUS_ACCEPT
       then accept (encode tag phi)
       else reject sTAGE_TAG Big_int_Z.zero_big_int (snd001 parsed_tag)
  else reject sTAGE_LINE Big_int_Z.zero_big_int eRR_NONCANONICAL_LINE

(** val result_status : Big_int_Z.big_int -> Big_int_Z.big_int **)

let result_status =
  fst001

(** val result_payload : Big_int_Z.big_int -> Big_int_Z.big_int **)

let result_payload =
  snd001

(** val acceptedb : Big_int_Z.big_int -> bool **)

let acceptedb r1 =
  Nat.eqb (result_status r1) sTATUS_ACCEPT

(** val parsed_line_formula : Big_int_Z.big_int -> Big_int_Z.big_int **)

let parsed_line_formula =
  snd001

(** val nth_line :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int **)

let nth_line n body i =
  nth_list_fuel (Big_int_Z.succ_big_int n) body i

(** val check_axk : Big_int_Z.big_int -> Big_int_Z.big_int **)

let check_axk phi =
  let outer = parse_imp phi in
  if acceptedb outer
  then let outer_payload = result_payload outer in
       let a = fst001 outer_payload in
       let rhs = snd001 outer_payload in
       let inner = parse_imp rhs in
       if acceptedb inner
       then let inner_payload = result_payload inner in
            let b0 = fst001 inner_payload in
            let a2 = snd001 inner_payload in
            if Nat.eqb a a2
            then if is_formula a
                 then if is_formula b0
                      then accept (encode rULE_AXK (encode a b0))
                      else reject sTAGE_RULE Big_int_Z.zero_big_int
                             eRR_AXK_BAD_B
                 else reject sTAGE_RULE Big_int_Z.zero_big_int eRR_AXK_BAD_A
            else reject sTAGE_RULE Big_int_Z.zero_big_int eRR_AXK_A_MISMATCH
       else reject sTAGE_RULE Big_int_Z.zero_big_int eRR_AXK_NOT_IMP_2
  else reject sTAGE_RULE Big_int_Z.zero_big_int eRR_AXK_NOT_IMP_1

(** val check_axs : Big_int_Z.big_int -> Big_int_Z.big_int **)

let check_axs phi =
  let imp1 = parse_imp phi in
  if acceptedb imp1
  then let p1 = result_payload imp1 in
       let x = fst001 p1 in
       let y = snd001 p1 in
       let imp2 = parse_imp x in
       if acceptedb imp2
       then let p2 = result_payload imp2 in
            let a = fst001 p2 in
            let bC = snd001 p2 in
            let imp3 = parse_imp bC in
            if acceptedb imp3
            then let p3 = result_payload imp3 in
                 let b0 = fst001 p3 in
                 let c = snd001 p3 in
                 let imp4 = parse_imp y in
                 if acceptedb imp4
                 then let p4 = result_payload imp4 in
                      let aB = fst001 p4 in
                      let aC = snd001 p4 in
                      let imp5 = parse_imp aB in
                      if acceptedb imp5
                      then let p5 = result_payload imp5 in
                           let a1 = fst001 p5 in
                           let b1 = snd001 p5 in
                           let imp6 = parse_imp aC in
                           if acceptedb imp6
                           then let p6 = result_payload imp6 in
                                let a2 = fst001 p6 in
                                let c1 = snd001 p6 in
                                if Nat.eqb a a1
                                then if Nat.eqb a a2
                                     then if Nat.eqb b0 b1
                                          then if Nat.eqb c c1
                                               then if is_formula a
                                                    then if is_formula b0
                                                         then if is_formula c
                                                              then accept
                                                                    (encode
                                                                    rULE_AXS
                                                                    (encode a
                                                                    (encode
                                                                    b0 c)))
                                                              else reject
                                                                    sTAGE_RULE
                                                                    Big_int_Z.zero_big_int
                                                                    eRR_AXS_BAD_C
                                                         else reject
                                                                sTAGE_RULE
                                                                Big_int_Z.zero_big_int
                                                                eRR_AXS_BAD_B
                                                    else reject sTAGE_RULE
                                                           Big_int_Z.zero_big_int
                                                           eRR_AXS_BAD_A
                                               else reject sTAGE_RULE
                                                      Big_int_Z.zero_big_int
                                                      eRR_AXS_C_MISMATCH
                                          else reject sTAGE_RULE
                                                 Big_int_Z.zero_big_int
                                                 eRR_AXS_B_MISMATCH
                                     else reject sTAGE_RULE
                                            Big_int_Z.zero_big_int
                                            eRR_AXS_A_MISMATCH_RIGHT
                                else reject sTAGE_RULE Big_int_Z.zero_big_int
                                       eRR_AXS_A_MISMATCH_LEFT
                           else reject sTAGE_RULE Big_int_Z.zero_big_int
                                  eRR_AXS_NOT_IMP_6
                      else reject sTAGE_RULE Big_int_Z.zero_big_int
                             eRR_AXS_NOT_IMP_5
                 else reject sTAGE_RULE Big_int_Z.zero_big_int
                        eRR_AXS_NOT_IMP_4
            else reject sTAGE_RULE Big_int_Z.zero_big_int eRR_AXS_NOT_IMP_3
       else reject sTAGE_RULE Big_int_Z.zero_big_int eRR_AXS_NOT_IMP_2
  else reject sTAGE_RULE Big_int_Z.zero_big_int eRR_AXS_NOT_IMP_1

(** val line_formula_result :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int -> Big_int_Z.big_int **)

let line_formula_result n body i detail =
  let fetched = nth_line n body i in
  if acceptedb fetched
  then let parsed = parse_line (result_payload fetched) in
       if acceptedb parsed
       then accept (parsed_line_formula (result_payload parsed))
       else reject sTAGE_RULE i detail
  else reject sTAGE_RULE i detail

(** val check_mp :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let check_mp n body j p q =
  if Nat.ltb p j
  then if Nat.ltb q j
       then if Nat.ltb j n
            then let rj = line_formula_result n body j eRR_MP_BAD_LINE_J in
                 if acceptedb rj
                 then let phi_j = result_payload rj in
                      let rp = line_formula_result n body p eRR_MP_BAD_LINE_P
                      in
                      if acceptedb rp
                      then let phi_p = result_payload rp in
                           let rq =
                             line_formula_result n body q eRR_MP_BAD_LINE_Q
                           in
                           if acceptedb rq
                           then let phi_q = result_payload rq in
                                let parsed_q = parse_imp phi_q in
                                if acceptedb parsed_q
                                then let q_payload = result_payload parsed_q
                                     in
                                     let a = fst001 q_payload in
                                     let b0 = snd001 q_payload in
                                     if Nat.eqb a phi_p
                                     then if Nat.eqb b0 phi_j
                                          then accept
                                                 (encode rULE_MP
                                                   (encode p
                                                     (encode q (encode a b0))))
                                          else reject sTAGE_RULE j
                                                 eRR_MP_CONSEQUENT_MISMATCH
                                     else reject sTAGE_RULE j
                                            eRR_MP_ANTECEDENT_MISMATCH
                                else reject sTAGE_RULE j eRR_MP_Q_NOT_IMP
                           else reject sTAGE_RULE q eRR_MP_BAD_LINE_Q
                      else reject sTAGE_RULE p eRR_MP_BAD_LINE_P
                 else reject sTAGE_RULE j eRR_MP_BAD_LINE_J
            else reject sTAGE_RULE j eRR_MP_BAD_LINE_J
       else reject sTAGE_RULE j eRR_MP_Q_NOT_LT_J
  else reject sTAGE_RULE j eRR_MP_P_NOT_LT_J

(** val code_local_cert_payload :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_local_cert_payload =
  encode

(** val code_final_cert_payload :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_final_cert_payload n theta certs final_formula =
  encode n (encode theta (encode certs final_formula))

(** val verify_line :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int **)

let verify_line n body j =
  let fetched = nth_line n body j in
  if acceptedb fetched
  then let ell = result_payload fetched in
       if canonical001b ell
       then let tag = line_tag ell in
            let phi = line_formula ell in
            let parsed_tag = parse_rule_tag tag in
            if acceptedb parsed_tag
            then let tag_payload = result_payload parsed_tag in
                 let rule = fst001 tag_payload in
                 let payload = snd001 tag_payload in
                 if Nat.eqb rule rULE_AXK
                 then let checked = check_axk phi in
                      if acceptedb checked
                      then accept
                             (code_local_cert_payload j
                               (result_payload checked))
                      else reject sTAGE_RULE j (result_payload checked)
                 else if Nat.eqb rule rULE_AXS
                      then let checked = check_axs phi in
                           if acceptedb checked
                           then accept
                                  (code_local_cert_payload j
                                    (result_payload checked))
                           else reject sTAGE_RULE j (result_payload checked)
                      else if Nat.eqb rule rULE_MP
                           then if canonical001b payload
                                then let p = fst001 payload in
                                     let q = snd001 payload in
                                     let checked = check_mp n body j p q in
                                     if acceptedb checked
                                     then accept
                                            (code_local_cert_payload j
                                              (result_payload checked))
                                     else reject sTAGE_RULE j
                                            (result_payload checked)
                                else reject sTAGE_TAG j eRR_NONCANONICAL_NODE
                           else reject sTAGE_TAG j eRR_UNKNOWN_RULE
            else reject sTAGE_TAG j (result_payload parsed_tag)
       else reject sTAGE_LINE j eRR_NONCANONICAL_LINE
  else reject sTAGE_LINE j (result_payload fetched)

(** val verify_lines :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec verify_lines fuel n body j certs =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ ->
    if Nat.eqb j n
    then accept certs
    else reject sTAGE_RULE j eRR_FUEL_EXHAUSTED)
    (fun fuel' ->
    if Nat.eqb j n
    then accept certs
    else let checked = verify_line n body j in
         if acceptedb checked
         then let local_cert = result_payload checked in
              verify_lines fuel' n body (Big_int_Z.succ_big_int j)
                (code_cons local_cert certs)
         else checked)
    fuel

(** val final_formula_result :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let final_formula_result n body =
  let last = Nat.pred n in
  let fetched = nth_line n body last in
  if acceptedb fetched
  then let parsed = parse_line (result_payload fetched) in
       if acceptedb parsed
       then accept (parsed_line_formula (result_payload parsed))
       else reject sTAGE_CONCLUSION last (result_payload parsed)
  else reject sTAGE_CONCLUSION last (result_payload fetched)

(** val a002_Verify :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let a002_Verify d theta =
  if canonical001b d
  then let n = fst001 d in
       let body = snd001 d in
       if list_exact_lengthb n body
       then if Nat.eqb n Big_int_Z.zero_big_int
            then reject sTAGE_CONCLUSION Big_int_Z.zero_big_int
                   eRR_EMPTY_DERIVATION
            else let checked_lines =
                   verify_lines n n body Big_int_Z.zero_big_int code_nil
                 in
                 if acceptedb checked_lines
                 then let certs = result_payload checked_lines in
                      let final_formula = final_formula_result n body in
                      if acceptedb final_formula
                      then let phi_last = result_payload final_formula in
                           if Nat.eqb phi_last theta
                           then accept
                                  (code_final_cert_payload n theta certs
                                    phi_last)
                           else reject sTAGE_CONCLUSION (Nat.pred n)
                                  eRR_BAD_CONCLUSION
                      else final_formula
                 else checked_lines
       else reject sTAGE_LIST_STRUCTURE Big_int_Z.zero_big_int
              eRR_BAD_DERIVATION_LENGTH
  else reject sTAGE_DERIVATION_HEADER Big_int_Z.zero_big_int
         eRR_NONCANONICAL_DERIVATION

(** val a002_Certb :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let a002_Certb d theta p =
  Nat.eqb (a002_Verify d theta) (accept p)

type normalizedFormula =
| NFVar of Big_int_Z.big_int
| NFImp of normalizedFormula * normalizedFormula

type normalizedRule =
| NRAxK
| NRAxS
| NRMP of Big_int_Z.big_int * Big_int_Z.big_int

type normalizedLine = { normalized_line_rule : normalizedRule;
                        normalized_line_formula : normalizedFormula }

type normalizedDerivation = normalizedLine list

(** val normalized_formula_eqb :
    normalizedFormula -> normalizedFormula -> bool **)

let rec normalized_formula_eqb a b0 =
  match a with
  | NFVar i -> (match b0 with
                | NFVar j -> Nat.eqb i j
                | NFImp (_, _) -> false)
  | NFImp (a1, a2) ->
    (match b0 with
     | NFVar _ -> false
     | NFImp (b1, b2) ->
       (&&) (normalized_formula_eqb a1 b1) (normalized_formula_eqb a2 b2))

(** val normalized_stepb :
    normalizedFormula list -> normalizedRule -> normalizedFormula -> bool **)

let normalized_stepb prefix rule formula =
  match rule with
  | NRAxK ->
    (match formula with
     | NFVar _ -> false
     | NFImp (a, n) ->
       (match n with
        | NFVar _ -> false
        | NFImp (_, a') -> normalized_formula_eqb a a'))
  | NRAxS ->
    (match formula with
     | NFVar _ -> false
     | NFImp (n, n0) ->
       (match n with
        | NFVar _ -> false
        | NFImp (a, n1) ->
          (match n1 with
           | NFVar _ -> false
           | NFImp (b0, c) ->
             (match n0 with
              | NFVar _ -> false
              | NFImp (n2, n3) ->
                (match n2 with
                 | NFVar _ -> false
                 | NFImp (a1, b1) ->
                   (match n3 with
                    | NFVar _ -> false
                    | NFImp (a2, c1) ->
                      (&&)
                        ((&&)
                          ((&&) (normalized_formula_eqb a a1)
                            (normalized_formula_eqb a a2))
                          (normalized_formula_eqb b0 b1))
                        (normalized_formula_eqb c c1)))))))
  | NRMP (p, q) ->
    (match nth_error prefix p with
     | Some a ->
       (match nth_error prefix q with
        | Some n ->
          (match n with
           | NFVar _ -> false
           | NFImp (a', b0) ->
             (&&) (normalized_formula_eqb a a')
               (normalized_formula_eqb formula b0))
        | None -> false)
     | None -> false)

(** val normalized_linesb :
    normalizedFormula list -> normalizedDerivation -> bool **)

let rec normalized_linesb prefix = function
| [] -> true
| line :: rest ->
  (&&)
    (normalized_stepb prefix line.normalized_line_rule
      line.normalized_line_formula)
    (normalized_linesb (app prefix (line.normalized_line_formula :: [])) rest)

(** val normalized_conclusion :
    normalizedDerivation -> normalizedFormula option **)

let rec normalized_conclusion = function
| [] -> None
| line :: rest ->
  (match rest with
   | [] -> Some line.normalized_line_formula
   | _ :: _ -> normalized_conclusion rest)

(** val normalized_verifyb :
    normalizedDerivation -> normalizedFormula -> bool **)

let normalized_verifyb lines target =
  (&&) (normalized_linesb [] lines)
    (match normalized_conclusion lines with
     | Some conclusion -> normalized_formula_eqb conclusion target
     | None -> false)

(** val normalized_formula_height : normalizedFormula -> Big_int_Z.big_int **)

let rec normalized_formula_height = function
| NFVar _ -> Big_int_Z.zero_big_int
| NFImp (a, b0) ->
  Big_int_Z.succ_big_int
    (Nat.max (normalized_formula_height a) (normalized_formula_height b0))

(** val encode_normalized_formula_raw :
    normalizedFormula -> Big_int_Z.big_int **)

let rec encode_normalized_formula_raw = function
| NFVar i -> code_var i
| NFImp (a, b0) ->
  code_imp (encode_normalized_formula_raw a)
    (encode_normalized_formula_raw b0)

(** val encode_normalized_formula : normalizedFormula -> Big_int_Z.big_int **)

let encode_normalized_formula formula =
  encode (Big_int_Z.succ_big_int (normalized_formula_height formula))
    (encode_normalized_formula_raw formula)

(** val normalize_formula_fuel :
    Big_int_Z.big_int -> Big_int_Z.big_int -> normalizedFormula option **)

let rec normalize_formula_fuel fuel c =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> None)
    (fun fuel' ->
    if canonical001b c
    then let tag = formula_tag c in
         let payload = formula_payload c in
         if Nat.eqb tag tAG_VAR
         then Some (NFVar payload)
         else if Nat.eqb tag tAG_IMP
              then if canonical001b payload
                   then (match normalize_formula_fuel fuel' (fst001 payload) with
                         | Some a ->
                           (match normalize_formula_fuel fuel'
                                    (snd001 payload) with
                            | Some b0 -> Some (NFImp (a, b0))
                            | None -> None)
                         | None -> None)
                   else None
              else None
    else None)
    fuel

(** val normalize_formula : Big_int_Z.big_int -> normalizedFormula option **)

let normalize_formula c =
  if canonical001b c
  then normalize_formula_fuel (fst001 c) (snd001 c)
  else None

(** val normalize_rule : Big_int_Z.big_int -> normalizedRule option **)

let normalize_rule tag =
  if canonical001b tag
  then let rule = rule_code tag in
       let payload = rule_payload tag in
       if Nat.eqb rule rULE_AXK
       then if Nat.eqb payload Big_int_Z.zero_big_int
            then Some NRAxK
            else None
       else if Nat.eqb rule rULE_AXS
            then if Nat.eqb payload Big_int_Z.zero_big_int
                 then Some NRAxS
                 else None
            else if Nat.eqb rule rULE_MP
                 then if canonical001b payload
                      then Some (NRMP ((fst001 payload), (snd001 payload)))
                      else None
                 else None
  else None

(** val encode_normalized_rule : normalizedRule -> Big_int_Z.big_int **)

let encode_normalized_rule = function
| NRAxK -> tag_axk
| NRAxS -> tag_axs
| NRMP (p, q) -> tag_mp p q

(** val normalize_line : Big_int_Z.big_int -> normalizedLine option **)

let normalize_line ell =
  if canonical001b ell
  then (match normalize_rule (line_tag ell) with
        | Some rule ->
          (match normalize_formula (line_formula ell) with
           | Some formula ->
             Some { normalized_line_rule = rule; normalized_line_formula =
               formula }
           | None -> None)
        | None -> None)
  else None

(** val encode_normalized_line : normalizedLine -> Big_int_Z.big_int **)

let encode_normalized_line line =
  code_line (encode_normalized_rule line.normalized_line_rule)
    (encode_normalized_formula line.normalized_line_formula)

(** val normalize_lines :
    Big_int_Z.big_int -> Big_int_Z.big_int -> normalizedDerivation option **)

let rec normalize_lines n body =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> if is_nil_nodeb body then Some [] else None)
    (fun n' ->
    if canonical001b body
    then if Nat.eqb (list_tag body) tAG_CONS
         then let payload = list_payload body in
              if canonical001b payload
              then (match normalize_line (fst001 payload) with
                    | Some line ->
                      (match normalize_lines n' (snd001 payload) with
                       | Some rest -> Some (line :: rest)
                       | None -> None)
                    | None -> None)
              else None
         else None
    else None)
    n

(** val encode_normalized_lines :
    normalizedDerivation -> Big_int_Z.big_int **)

let rec encode_normalized_lines = function
| [] -> code_nil
| line :: rest ->
  code_cons (encode_normalized_line line) (encode_normalized_lines rest)

(** val normalize_derivation :
    Big_int_Z.big_int -> normalizedDerivation option **)

let normalize_derivation d =
  if canonical001b d then normalize_lines (fst001 d) (snd001 d) else None

(** val encode_normalized_derivation :
    normalizedDerivation -> Big_int_Z.big_int **)

let encode_normalized_derivation lines =
  code_derivation (length lines) (encode_normalized_lines lines)

(** val normalized_failure_index :
    normalizedFormula list -> normalizedDerivation -> Big_int_Z.big_int ->
    Big_int_Z.big_int option **)

let rec normalized_failure_index prefix lines index =
  match lines with
  | [] -> None
  | line :: rest ->
    if normalized_stepb prefix line.normalized_line_rule
         line.normalized_line_formula
    then normalized_failure_index
           (app prefix (line.normalized_line_formula :: [])) rest
           (Big_int_Z.succ_big_int index)
    else Some index

(** val normalized_rejection : normalizedDerivation -> Big_int_Z.big_int **)

let normalized_rejection lines =
  match normalized_failure_index [] lines Big_int_Z.zero_big_int with
  | Some index -> reject sTAGE_RULE index eRR_NORMALIZED_STEP_REJECTED
  | None ->
    (match normalized_conclusion lines with
     | Some _ ->
       reject sTAGE_CONCLUSION (Nat.pred (length lines)) eRR_BAD_CONCLUSION
     | None ->
       reject sTAGE_CONCLUSION Big_int_Z.zero_big_int eRR_EMPTY_DERIVATION)

(** val certified_payload :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let certified_payload =
  encode

(** val a002_Verify_certified :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let a002_Verify_certified d theta =
  match normalize_derivation d with
  | Some lines ->
    (match normalize_formula theta with
     | Some target ->
       if normalized_verifyb lines target
       then accept (certified_payload d theta)
       else normalized_rejection lines
     | None ->
       reject sTAGE_FORMULA Big_int_Z.zero_big_int eRR_NONCANONICAL_FORMULA)
  | None ->
    reject sTAGE_DERIVATION_HEADER Big_int_Z.zero_big_int
      eRR_NONCANONICAL_DERIVATION

(** val a002_Certified_Certb :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let a002_Certified_Certb d theta payload =
  (&&)
    ((&&) ((&&) (canonical001b payload) (Nat.eqb (fst001 payload) d))
      (Nat.eqb (snd001 payload) theta))
    (match normalize_derivation d with
     | Some lines ->
       (match normalize_formula theta with
        | Some target -> normalized_verifyb lines target
        | None -> false)
     | None -> false)
