
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

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val of_succ_nat : Big_int_Z.big_int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
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

module Z =
 struct
  (** val of_nat : Big_int_Z.big_int -> z **)

  let of_nat n =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Pos.of_succ_nat n0))
      n
 end

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

(** val z0 : params -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let z0 = function
| Build_Params (z2, _) -> z2

(** val r : params -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let r = function
| Build_Params (_, r1) -> r1

(** val b : params -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let b p x =
  mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)) (r p x)

(** val even_band : params -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let even_band p x =
  map two (z0 p x)

(** val odd_band :
    params -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list **)

let odd_band p x y =
  map (fun j -> add (b p x) (two_j_minus1 j)) (z0 p y)

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

(** val z1 : Big_int_Z.big_int -> Big_int_Z.big_int list **)

let z1 x =
  fst (zeck_greedy_down (r0 x) x false)

(** val base_params : params **)

let base_params =
  Build_Params (z1, r0)

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
  let zn = z1 c in
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

(** val eRR_EMPTY_DERIVATION : Big_int_Z.big_int **)

let eRR_EMPTY_DERIVATION =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

(** val eRR_BAD_CONCLUSION : Big_int_Z.big_int **)

let eRR_BAD_CONCLUSION =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))

(** val eRR_NONCANONICAL_NODE : Big_int_Z.big_int **)

let eRR_NONCANONICAL_NODE =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int Big_int_Z.zero_big_int))))

(** val eRR_BAD_TAG : Big_int_Z.big_int **)

let eRR_BAD_TAG =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int)))))

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

(** val eRR_BAD_FORMULA_TAG : Big_int_Z.big_int **)

let eRR_BAD_FORMULA_TAG =
  Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
    Big_int_Z.zero_big_int))))))))))))))))))))

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

(** val list_tag : Big_int_Z.big_int -> Big_int_Z.big_int **)

let list_tag =
  fst001

(** val list_payload : Big_int_Z.big_int -> Big_int_Z.big_int **)

let list_payload =
  snd001

(** val is_nil_nodeb : Big_int_Z.big_int -> bool **)

let is_nil_nodeb body =
  is_pair001b body tAG_NIL Big_int_Z.zero_big_int

(** val tAG_VAR : Big_int_Z.big_int **)

let tAG_VAR =
  Big_int_Z.zero_big_int

(** val tAG_IMP : Big_int_Z.big_int **)

let tAG_IMP =
  Big_int_Z.succ_big_int Big_int_Z.zero_big_int

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

(** val parse_formula_diagnostic : Big_int_Z.big_int -> Big_int_Z.big_int **)

let parse_formula_diagnostic phi =
  if is_formula phi
  then accept phi
  else reject sTAGE_FORMULA Big_int_Z.zero_big_int eRR_BAD_FORMULA_TAG

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

(** val normalize_derivation :
    Big_int_Z.big_int -> normalizedDerivation option **)

let normalize_derivation d =
  if canonical001b d then normalize_lines (fst001 d) (snd001 d) else None

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

type a002_IO_Query =
| Verify_Query of Big_int_Z.big_int * Big_int_Z.big_int
| Cert_Check_Query of Big_int_Z.big_int * Big_int_Z.big_int
   * Big_int_Z.big_int
| Parse_Formula_Query of Big_int_Z.big_int
| Parse_Line_Query of Big_int_Z.big_int

type a002_IO_Result =
| Verify_Result of Big_int_Z.big_int
| Cert_Check_Result of bool
| Parse_Result of Big_int_Z.big_int

(** val a002_Verified :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let a002_Verified =
  a002_Verify_certified

(** val a002_Certificate_Check :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let a002_Certificate_Check =
  a002_Certified_Certb

(** val a002_Parse_Formula : Big_int_Z.big_int -> Big_int_Z.big_int **)

let a002_Parse_Formula =
  parse_formula_diagnostic

(** val a002_Parse_Line : Big_int_Z.big_int -> Big_int_Z.big_int **)

let a002_Parse_Line =
  parse_line

(** val a002_IO : a002_IO_Query -> a002_IO_Result **)

let a002_IO = function
| Verify_Query (d, theta) -> Verify_Result (a002_Verify_certified d theta)
| Cert_Check_Query (d, theta, p) ->
  Cert_Check_Result (a002_Certified_Certb d theta p)
| Parse_Formula_Query phi -> Parse_Result (parse_formula_diagnostic phi)
| Parse_Line_Query ell -> Parse_Result (parse_line ell)

(** val decode_Result :
    Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int **)

let decode_Result r1 =
  ((result_status r1), (result_payload r1))

(** val decode_Error :
    Big_int_Z.big_int ->
    (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int **)

let decode_Error payload =
  let stage = fst001 payload in
  let index_detail = snd001 payload in
  ((stage, (fst001 index_detail)), (snd001 index_detail))

(** val verify_Diagnostic :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int **)

let verify_Diagnostic d theta =
  let r1 = a002_Verify_certified d theta in
  ((r1, (result_status r1)), (result_payload r1))

(** val a002_Verified_Z : Big_int_Z.big_int -> Big_int_Z.big_int -> z **)

let a002_Verified_Z d theta =
  Z.of_nat (a002_Verify_certified d theta)

(** val a002_Parse_Formula_Z : Big_int_Z.big_int -> z **)

let a002_Parse_Formula_Z phi =
  Z.of_nat (parse_formula_diagnostic phi)

(** val a002_Parse_Line_Z : Big_int_Z.big_int -> z **)

let a002_Parse_Line_Z ell =
  Z.of_nat (parse_line ell)

type a002_IO_Result_Z =
| Verify_Result_Z of z
| Cert_Check_Result_Z of bool
| Parse_Result_Z of z

(** val a002_IO_Z : a002_IO_Query -> a002_IO_Result_Z **)

let a002_IO_Z = function
| Verify_Query (d, theta) -> Verify_Result_Z (a002_Verified_Z d theta)
| Cert_Check_Query (d, theta, p) ->
  Cert_Check_Result_Z (a002_Certified_Certb d theta p)
| Parse_Formula_Query phi -> Parse_Result_Z (a002_Parse_Formula_Z phi)
| Parse_Line_Query ell -> Parse_Result_Z (a002_Parse_Line_Z ell)

(** val verify_Diagnostic_Z :
    Big_int_Z.big_int -> Big_int_Z.big_int -> (z * z) * z **)

let verify_Diagnostic_Z d theta =
  let diag = verify_Diagnostic d theta in
  let (p, payload) = diag in
  let (raw, status) = p in
  (((Z.of_nat raw), (Z.of_nat status)), (Z.of_nat payload))
