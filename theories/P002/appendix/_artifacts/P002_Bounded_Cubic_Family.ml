
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

type monomial =
| M_const
| M_linear of Big_int_Z.big_int
| M_quadratic of Big_int_Z.big_int * Big_int_Z.big_int
| M_cubic of Big_int_Z.big_int * Big_int_Z.big_int * Big_int_Z.big_int

type term = { coeff : Big_int_Z.big_int; mono : monomial }

type h10_nd3n_equation = { var_count : Big_int_Z.big_int;
                           lhs_terms : term list; rhs_terms : term list }

type cubic_family_instance = h10_nd3n_equation list

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

(** val k_IP : Big_int_Z.big_int **)

let k_IP =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))))))))))

(** val k_R1 : Big_int_Z.big_int **)

let k_R1 =
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
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val k_R2 : Big_int_Z.big_int **)

let k_R2 =
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

(** val iP_offset : Big_int_Z.big_int **)

let iP_offset =
  Big_int_Z.zero_big_int

(** val r1_offset : Big_int_Z.big_int **)

let r1_offset =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))))))))

(** val r2_offset : Big_int_Z.big_int **)

let r2_offset =
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

(** val band_support :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let band_support offset x =
  map (fun i -> add offset i) (z0 x)

(** val band_pred :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let band_pred offset k k0 =
  (&&)
    (Nat.leb
      (add offset (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))
      k0)
    (Nat.ltb k0 (add offset k))

(** val band_indices :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list ->
    Big_int_Z.big_int list **)

let band_indices offset k zn =
  map (fun k0 -> sub k0 offset) (filter (band_pred offset k) zn)

(** val ip_support : Big_int_Z.big_int -> Big_int_Z.big_int list **)

let ip_support =
  band_support iP_offset

(** val r1_support : Big_int_Z.big_int -> Big_int_Z.big_int list **)

let r1_support =
  band_support r1_offset

(** val r2_support : Big_int_Z.big_int -> Big_int_Z.big_int list **)

let r2_support =
  band_support r2_offset

type iterantState = { state_ip : Big_int_Z.big_int;
                      state_r1 : Big_int_Z.big_int;
                      state_r2 : Big_int_Z.big_int }

(** val state_support : iterantState -> Big_int_Z.big_int list **)

let state_support st =
  app (r2_support st.state_r2)
    (app (r1_support st.state_r1) (ip_support st.state_ip))

(** val encode_state : iterantState -> Big_int_Z.big_int **)

let encode_state st =
  sum_fib (state_support st)

(** val decode_ip_from_support :
    Big_int_Z.big_int list -> Big_int_Z.big_int **)

let decode_ip_from_support zn =
  sum_fib (band_indices iP_offset k_IP zn)

(** val decode_r1_from_support :
    Big_int_Z.big_int list -> Big_int_Z.big_int **)

let decode_r1_from_support zn =
  sum_fib (band_indices r1_offset k_R1 zn)

(** val decode_r2_from_support :
    Big_int_Z.big_int list -> Big_int_Z.big_int **)

let decode_r2_from_support zn =
  sum_fib (band_indices r2_offset k_R2 zn)

(** val decode_state_from_support : Big_int_Z.big_int list -> iterantState **)

let decode_state_from_support zn =
  { state_ip = (decode_ip_from_support zn); state_r1 =
    (decode_r1_from_support zn); state_r2 = (decode_r2_from_support zn) }

(** val decode_state : Big_int_Z.big_int -> iterantState **)

let decode_state s =
  decode_state_from_support (z0 s)

type counter =
| Counter1
| Counter2

type instruction =
| INC of counter * Big_int_Z.big_int
| JZDEC of counter * Big_int_Z.big_int * Big_int_Z.big_int
| HALT

type program = instruction list

(** val read_counter : counter -> iterantState -> Big_int_Z.big_int **)

let read_counter c st =
  match c with
  | Counter1 -> st.state_r1
  | Counter2 -> st.state_r2

(** val write_counter :
    counter -> Big_int_Z.big_int -> iterantState -> iterantState **)

let write_counter c v st =
  match c with
  | Counter1 ->
    { state_ip = st.state_ip; state_r1 = v; state_r2 = st.state_r2 }
  | Counter2 ->
    { state_ip = st.state_ip; state_r1 = st.state_r1; state_r2 = v }

(** val set_ip : Big_int_Z.big_int -> iterantState -> iterantState **)

let set_ip ip st =
  { state_ip = ip; state_r1 = st.state_r1; state_r2 = st.state_r2 }

(** val initial_state : Big_int_Z.big_int -> iterantState **)

let initial_state input =
  { state_ip = (Big_int_Z.succ_big_int Big_int_Z.zero_big_int); state_r1 =
    input; state_r2 = Big_int_Z.zero_big_int }

(** val fetch_instruction : program -> iterantState -> instruction option **)

let fetch_instruction prog st =
  nth_error prog st.state_ip

(** val step_state : program -> iterantState -> iterantState **)

let step_state prog st =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> st)
    (fun _ ->
    match fetch_instruction prog st with
    | Some i ->
      (match i with
       | INC (c, next_ip) ->
         set_ip next_ip
           (write_counter c (Big_int_Z.succ_big_int (read_counter c st)) st)
       | JZDEC (c, zero_ip, dec_ip) ->
         if Nat.eqb (read_counter c st) Big_int_Z.zero_big_int
         then set_ip zero_ip st
         else set_ip dec_ip
                (write_counter c (Nat.pred (read_counter c st)) st)
       | HALT -> set_ip Big_int_Z.zero_big_int st)
    | None -> set_ip Big_int_Z.zero_big_int st)
    st.state_ip

(** val nextState : program -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let nextState prog s =
  encode_state (step_state prog (decode_state s))

(** val stepb : program -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let stepb prog s t =
  Nat.eqb (nextState prog s) t

(** val encode_nat_list : Big_int_Z.big_int list -> Big_int_Z.big_int **)

let rec encode_nat_list = function
| [] -> Big_int_Z.zero_big_int
| x :: xs' -> Big_int_Z.succ_big_int (encode x (encode_nat_list xs'))

(** val coded_list_head : Big_int_Z.big_int -> Big_int_Z.big_int **)

let coded_list_head n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> Big_int_Z.zero_big_int)
    (fun k -> fst (decode k))
    n

(** val coded_list_tail : Big_int_Z.big_int -> Big_int_Z.big_int **)

let coded_list_tail n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> Big_int_Z.zero_big_int)
    (fun k -> snd (decode k))
    n

(** val coded_nth :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec coded_nth i n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> coded_list_head n)
    (fun i' -> coded_nth i' (coded_list_tail n))
    i

type machineState = iterantState

type machineProgram = program

type encodedState = Big_int_Z.big_int

(** val current_state : encodedState -> machineState **)

let current_state =
  decode_state

(** val halted_state_b : machineState -> bool **)

let halted_state_b st =
  Nat.eqb st.state_ip Big_int_Z.zero_big_int

(** val halted_code_b : encodedState -> bool **)

let halted_code_b s =
  halted_state_b (current_state s)

(** val stepCode : machineProgram -> encodedState -> encodedState **)

let stepCode =
  nextState

(** val step_matches_b :
    machineProgram -> encodedState -> encodedState -> bool **)

let step_matches_b =
  stepb

type codeTrace = encodedState list

(** val encode_code_trace : codeTrace -> Big_int_Z.big_int **)

let encode_code_trace =
  encode_nat_list

(** val code_trace_head : Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_trace_head =
  coded_list_head

(** val code_trace_tail : Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_trace_tail =
  coded_list_tail

(** val code_trace_nth :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let code_trace_nth =
  coded_nth

(** val decode_code_trace_bounded :
    Big_int_Z.big_int -> Big_int_Z.big_int -> codeTrace **)

let rec decode_code_trace_bounded budget witness =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> [])
    (fun budget' ->
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> [])
      (fun _ ->
      (code_trace_head witness) :: (decode_code_trace_bounded budget'
                                     (code_trace_tail witness)))
      witness)
    budget

(** val decode_code_trace : Big_int_Z.big_int -> codeTrace **)

let decode_code_trace witness =
  decode_code_trace_bounded witness witness

(** val start_code : Big_int_Z.big_int -> encodedState **)

let start_code input =
  encode_state (initial_state input)

(** val codeTraceStartsFrom_b : encodedState -> codeTrace -> bool **)

let codeTraceStartsFrom_b start = function
| [] -> false
| s0 :: _ -> Nat.eqb s0 start

(** val validCodeTrace_b : machineProgram -> codeTrace -> bool **)

let rec validCodeTrace_b prog = function
| [] -> false
| s1 :: rest ->
  (match rest with
   | [] -> halted_code_b s1
   | s2 :: _ -> (&&) (step_matches_b prog s1 s2) (validCodeTrace_b prog rest))

(** val codeTraceStartsWith_b : Big_int_Z.big_int -> codeTrace -> bool **)

let codeTraceStartsWith_b input tr =
  codeTraceStartsFrom_b (start_code input) tr

(** val codeTraceWitness_b :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let codeTraceWitness_b prog input witness =
  let tr = decode_code_trace witness in
  (&&) (codeTraceStartsWith_b input tr)
    ((&&) (validCodeTrace_b prog tr) (Nat.eqb witness (encode_code_trace tr)))

(** val fMValidTrace_b :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let fMValidTrace_b =
  codeTraceWitness_b

type equation_family = cubic_family_instance

(** val cubic_monomial_count : monomial -> Big_int_Z.big_int **)

let cubic_monomial_count = function
| M_cubic (_, _, _) -> Big_int_Z.succ_big_int Big_int_Z.zero_big_int
| _ -> Big_int_Z.zero_big_int

(** val cubic_term_count : term -> Big_int_Z.big_int **)

let cubic_term_count t =
  cubic_monomial_count t.mono

(** val cubic_poly_count : term list -> Big_int_Z.big_int **)

let rec cubic_poly_count = function
| [] -> Big_int_Z.zero_big_int
| t :: ts' -> add (cubic_term_count t) (cubic_poly_count ts')

(** val cubic_equation_count : h10_nd3n_equation -> Big_int_Z.big_int **)

let cubic_equation_count eqn =
  add (cubic_poly_count eqn.lhs_terms) (cubic_poly_count eqn.rhs_terms)

(** val cubic_family_count : cubic_family_instance -> Big_int_Z.big_int **)

let rec cubic_family_count = function
| [] -> Big_int_Z.zero_big_int
| eqn :: gamma' -> add (cubic_equation_count eqn) (cubic_family_count gamma')

(** val family_var_bound : cubic_family_instance -> Big_int_Z.big_int **)

let rec family_var_bound = function
| [] -> Big_int_Z.zero_big_int
| eqn :: gamma' -> Nat.max eqn.var_count (family_var_bound gamma')

type traceConstraintFamily = equation_family

(** val trace_witness_length : Big_int_Z.big_int -> Big_int_Z.big_int **)

let trace_witness_length witness =
  length (decode_code_trace witness)

(** val trace_witness_step_count : Big_int_Z.big_int -> Big_int_Z.big_int **)

let trace_witness_step_count witness =
  Nat.pred (trace_witness_length witness)

(** val trace_witness_last_code : Big_int_Z.big_int -> Big_int_Z.big_int **)

let trace_witness_last_code witness =
  code_trace_nth (trace_witness_step_count witness) witness

(** val emit_linear_const_equation :
    Big_int_Z.big_int -> Big_int_Z.big_int -> h10_nd3n_equation **)

let emit_linear_const_equation var value =
  { var_count = (Big_int_Z.succ_big_int var); lhs_terms = ({ coeff =
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int); mono = (M_linear
    var) } :: []); rhs_terms = ({ coeff = value; mono = M_const } :: []) }

(** val emit_false_equation : h10_nd3n_equation **)

let emit_false_equation =
  { var_count = Big_int_Z.zero_big_int; lhs_terms = ({ coeff =
    (Big_int_Z.succ_big_int Big_int_Z.zero_big_int); mono = M_const } :: []);
    rhs_terms = [] }

(** val emit_trace_shape_family_upto :
    Big_int_Z.big_int -> Big_int_Z.big_int -> equation_family **)

let rec emit_trace_shape_family_upto witness bound =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ ->
    (emit_linear_const_equation (Big_int_Z.succ_big_int
      Big_int_Z.zero_big_int) (code_trace_nth Big_int_Z.zero_big_int witness)) :: [])
    (fun bound' ->
    app (emit_trace_shape_family_upto witness bound')
      ((emit_linear_const_equation (Big_int_Z.succ_big_int
         (Big_int_Z.succ_big_int bound'))
         (code_trace_nth (Big_int_Z.succ_big_int bound') witness)) :: []))
    bound

(** val emit_trace_shape_family :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    equation_family **)

let emit_trace_shape_family _ _ witness =
  app
    (emit_trace_shape_family_upto witness (trace_witness_step_count witness))
    (if Nat.eqb (encode_code_trace (decode_code_trace witness)) witness
     then []
     else emit_false_equation :: [])

(** val emit_trace_start_family :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    equation_family **)

let emit_trace_start_family _ input _ =
  (emit_linear_const_equation (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)
    (start_code input)) :: []

(** val emit_trace_step_family_upto :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    equation_family **)

let rec emit_trace_step_family_upto prog witness count =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> [])
    (fun count' ->
    app (emit_trace_step_family_upto prog witness count')
      ((emit_linear_const_equation (Big_int_Z.succ_big_int
         (Big_int_Z.succ_big_int count'))
         (stepCode prog (code_trace_nth count' witness))) :: []))
    count

(** val emit_trace_step_family :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    equation_family **)

let emit_trace_step_family prog _ witness =
  emit_trace_step_family_upto prog witness (trace_witness_step_count witness)

(** val emit_trace_halt_family :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    equation_family **)

let emit_trace_halt_family _ _ witness =
  let last = trace_witness_last_code witness in
  app ((emit_linear_const_equation Big_int_Z.zero_big_int last) :: [])
    (if halted_code_b last then [] else emit_false_equation :: [])

(** val emit_trace_family :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    traceConstraintFamily **)

let emit_trace_family prog input witness =
  app (emit_trace_shape_family prog input witness)
    (app (emit_trace_start_family prog input witness)
      (app (emit_trace_step_family prog input witness)
        (emit_trace_halt_family prog input witness)))

(** val search_FMValidTrace_upto :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int option **)

let rec search_FMValidTrace_upto prog input bound =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ ->
    if fMValidTrace_b prog input Big_int_Z.zero_big_int
    then Some Big_int_Z.zero_big_int
    else None)
    (fun bound' ->
    match search_FMValidTrace_upto prog input bound' with
    | Some witness -> Some witness
    | None ->
      if fMValidTrace_b prog input (Big_int_Z.succ_big_int bound')
      then Some (Big_int_Z.succ_big_int bound')
      else None)
    bound

(** val emit_bounded_witness_search_family :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    traceConstraintFamily **)

let emit_bounded_witness_search_family prog input bound =
  match search_FMValidTrace_upto prog input bound with
  | Some witness -> emit_trace_family prog input witness
  | None -> emit_false_equation :: []

(** val compile_fm_family_upto :
    machineProgram -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    cubic_family_instance **)

let compile_fm_family_upto =
  emit_bounded_witness_search_family
