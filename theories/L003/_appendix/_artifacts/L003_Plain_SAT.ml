
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

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

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

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val even : nat -> bool **)

  let rec even = function
  | O -> True
  | S n0 -> (match n0 with
             | O -> False
             | S n' -> even n')

  (** val div2 : nat -> nat **)

  let rec div2 = function
  | O -> O
  | S n0 -> (match n0 with
             | O -> O
             | S n' -> S (div2 n'))
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f a), (map f l0))

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> Nil
| S len0 -> Cons (start, (seq (S start) len0))

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | Nil -> default
          | Cons (x, _) -> x)
  | S m -> (match l with
            | Nil -> default
            | Cons (_, l') -> nth m l' default)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| Nil -> Nil
| Cons (x, l0) -> app (f x) (flat_map f l0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Nil -> False
| Cons (a, l0) -> (match f a with
                   | True -> True
                   | False -> existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) -> (match f a with
                   | True -> forallb f l0
                   | False -> False)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| Nil -> Nil
| Cons (x, l0) ->
  (match f x with
   | True -> Cons (x, (filter f l0))
   | False -> filter f l0)

type concreteTerm =
| TConst of bool
| TBit of nat
| TNot of concreteTerm
| TAnd of concreteTerm * concreteTerm
| TOr of concreteTerm * concreteTerm
| TDup of concreteTerm
| TProj of concreteTerm
| TOracle of nat list

type bitStream = nat -> bool

(** val stream_pair : bitStream -> bitStream -> bitStream **)

let stream_pair x y i =
  match Nat.even i with
  | True -> x (Nat.div2 i)
  | False -> y (Nat.div2 i)

(** val unary_bits : nat -> bool list **)

let rec unary_bits = function
| O -> Cons (False, Nil)
| S m -> Cons (True, (unary_bits m))

(** val list_bits : nat list -> bool list **)

let rec list_bits = function
| Nil -> Cons (False, Nil)
| Cons (i, l') -> Cons (True, (app (unary_bits i) (list_bits l')))

(** val term_serialize : concreteTerm -> bool list **)

let rec term_serialize = function
| TConst b -> Cons (False, (Cons (False, (Cons (False, (Cons (b, Nil)))))))
| TBit i ->
  app (Cons (False, (Cons (False, (Cons (True, Nil)))))) (unary_bits i)
| TNot s ->
  app (Cons (False, (Cons (True, (Cons (False, Nil)))))) (term_serialize s)
| TAnd (s, u) ->
  app (Cons (False, (Cons (True, (Cons (True, Nil))))))
    (app (term_serialize s) (term_serialize u))
| TOr (s, u) ->
  app (Cons (True, (Cons (False, (Cons (False, Nil))))))
    (app (term_serialize s) (term_serialize u))
| TDup s ->
  app (Cons (True, (Cons (False, (Cons (True, Nil)))))) (term_serialize s)
| TProj s ->
  app (Cons (True, (Cons (True, (Cons (False, Nil)))))) (term_serialize s)
| TOracle l ->
  app (Cons (True, (Cons (True, (Cons (True, Nil)))))) (list_bits l)

(** val term_code : concreteTerm -> bitStream **)

let term_code t i =
  nth i (term_serialize t) False

(** val term_level : concreteTerm -> nat **)

let term_level t =
  length (term_serialize t)

(** val term_size : concreteTerm -> nat **)

let rec term_size = function
| TNot s -> add (S O) (term_size s)
| TAnd (s, u) -> add (add (S O) (term_size s)) (term_size u)
| TOr (s, u) -> add (add (S O) (term_size s)) (term_size u)
| TDup s -> add (S O) (term_size s)
| TProj s -> add (S O) (term_size s)
| _ -> S O

(** val diagonal_term : concreteTerm -> concreteTerm **)

let diagonal_term v =
  TNot (TDup (TProj v))

(** val proj_shift : (nat -> nat) -> nat -> nat **)

let proj_shift f j =
  match Nat.even j with
  | True -> mul (S (S O)) (f (Nat.div2 j))
  | False -> j

(** val reindex : concreteTerm -> (nat -> nat) -> concreteTerm **)

let rec reindex t f =
  match t with
  | TConst b -> TConst b
  | TBit i -> TBit (f i)
  | TNot s -> TNot (reindex s f)
  | TAnd (s, u) -> TAnd ((reindex s f), (reindex u f))
  | TOr (s, u) -> TOr ((reindex s f), (reindex u f))
  | TDup s -> reindex s (fun j -> f (Nat.div2 j))
  | TProj s -> TProj (reindex s (proj_shift f))
  | TOracle l -> TOracle (map f l)

(** val bit_literal : bool -> nat -> concreteTerm **)

let bit_literal b i =
  match b with
  | True -> TBit i
  | False -> TNot (TBit i)

(** val match_bits : bool list -> nat -> concreteTerm **)

let rec match_bits c k =
  match c with
  | Nil -> TConst True
  | Cons (b, c') ->
    TAnd ((bit_literal b (mul (S (S O)) k)), (match_bits c' (S k)))

(** val even_position : nat -> nat **)

let even_position j =
  mul (S (S O)) j

(** val odd_position : nat -> nat **)

let odd_position j =
  S (mul (S (S O)) j)

(** val brute_force_entry : concreteTerm -> concreteTerm **)

let brute_force_entry e =
  TAnd ((match_bits (term_serialize e) O), (reindex e odd_position))

(** val brute_force_list : concreteTerm list -> concreteTerm **)

let rec brute_force_list = function
| Nil -> TConst False
| Cons (e, l') -> TOr ((brute_force_entry e), (brute_force_list l'))

(** val bounded_lists : nat -> nat -> nat list list **)

let rec bounded_lists b = function
| O -> Cons (Nil, Nil)
| S k' ->
  Cons (Nil,
    (flat_map (fun i -> map (fun x -> Cons (i, x)) (bounded_lists b k'))
      (seq O b)))

(** val terms_upto : nat -> concreteTerm list **)

let rec terms_upto = function
| O -> Nil
| S m ->
  Cons ((TConst False), (Cons ((TConst True),
    (app (map (fun x -> TBit x) (seq O (S m)))
      (app (map (fun x -> TOracle x) (bounded_lists (S m) (S m)))
        (app (map (fun x -> TNot x) (terms_upto m))
          (app (map (fun x -> TDup x) (terms_upto m))
            (app (map (fun x -> TProj x) (terms_upto m))
              (app
                (flat_map (fun a ->
                  map (fun x -> TAnd (a, x)) (terms_upto m)) (terms_upto m))
                (flat_map (fun a -> map (fun x -> TOr (a, x)) (terms_upto m))
                  (terms_upto m)))))))))))

(** val brute_force : nat -> concreteTerm **)

let brute_force n =
  brute_force_list (terms_upto n)

(** val concrete_certifier : nat -> concreteTerm **)

let concrete_certifier n =
  reindex (brute_force n) even_position

type propFormula =
| PConst of bool
| PVar of nat
| PNeg of propFormula
| PAnd of propFormula * propFormula
| POr of propFormula * propFormula

(** val formula_eval : propFormula -> bitStream -> bool **)

let rec formula_eval f a =
  match f with
  | PConst b -> b
  | PVar j -> a j
  | PNeg f1 -> negb (formula_eval f1 a)
  | PAnd (f1, f2) ->
    (match formula_eval f1 a with
     | True -> formula_eval f2 a
     | False -> False)
  | POr (f1, f2) ->
    (match formula_eval f1 a with
     | True -> True
     | False -> formula_eval f2 a)

(** val formula_var_bound : propFormula -> nat **)

let rec formula_var_bound = function
| PConst _ -> O
| PVar j -> S j
| PNeg f1 -> formula_var_bound f1
| PAnd (f1, f2) -> add (formula_var_bound f1) (formula_var_bound f2)
| POr (f1, f2) -> add (formula_var_bound f1) (formula_var_bound f2)

(** val formula_size : propFormula -> nat **)

let rec formula_size = function
| PNeg f1 -> add (S O) (formula_size f1)
| PAnd (f1, f2) -> add (add (S O) (formula_size f1)) (formula_size f2)
| POr (f1, f2) -> add (add (S O) (formula_size f1)) (formula_size f2)
| _ -> S O

(** val stream_update : bitStream -> nat -> bool -> bitStream **)

let stream_update a n b i =
  match Nat.eqb i n with
  | True -> b
  | False -> a i

(** val truth_table : propFormula -> nat -> bitStream -> bool **)

let rec truth_table f n a =
  match n with
  | O -> formula_eval f a
  | S m ->
    (match truth_table f m (stream_update a m False) with
     | True -> True
     | False -> truth_table f m (stream_update a m True))

(** val classify : propFormula -> bool **)

let classify f =
  truth_table f (formula_var_bound f) (fun _ -> False)

(** val circuit_verifierb : concreteTerm -> bool **)

let rec circuit_verifierb = function
| TConst _ -> True
| TBit _ -> True
| TNot s -> circuit_verifierb s
| TAnd (s, u) ->
  (match circuit_verifierb s with
   | True -> circuit_verifierb u
   | False -> False)
| TOr (s, u) ->
  (match circuit_verifierb s with
   | True -> circuit_verifierb u
   | False -> False)
| TDup s -> circuit_verifierb s
| _ -> False

(** val specialize_term :
    concreteTerm -> (nat -> propFormula) -> propFormula **)

let rec specialize_term t acc =
  match t with
  | TConst b -> PConst b
  | TBit i -> acc i
  | TNot s -> PNeg (specialize_term s acc)
  | TAnd (s, u) -> PAnd ((specialize_term s acc), (specialize_term u acc))
  | TOr (s, u) -> POr ((specialize_term s acc), (specialize_term u acc))
  | TDup s -> specialize_term s (fun i -> acc (Nat.div2 i))
  | _ -> PConst False

(** val claim_assignment : concreteTerm -> nat -> propFormula **)

let claim_assignment v i =
  match Nat.even i with
  | True ->
    PConst
      (stream_pair (term_code (diagonal_term v))
        (term_code (diagonal_term v)) (Nat.div2 i))
  | False -> PVar (Nat.div2 i)

(** val specialized_formula : concreteTerm -> propFormula **)

let specialized_formula v =
  specialize_term v (claim_assignment v)

type literal = (bool, nat) prod

type clause = literal list

type cNF = clause list

(** val lit_eval : bitStream -> literal -> bool **)

let lit_eval a = function
| Pair (b, j) -> (match b with
                  | True -> a j
                  | False -> negb (a j))

(** val clause_eval : bitStream -> clause -> bool **)

let clause_eval a c =
  existsb (lit_eval a) c

(** val cnf_eval : bitStream -> cNF -> bool **)

let cnf_eval a f =
  forallb (clause_eval a) f

(** val tseitin_aux : propFormula -> nat -> ((nat, nat) prod, cNF) prod **)

let rec tseitin_aux f next =
  match f with
  | PConst b ->
    Pair ((Pair (next, (S next))), (Cons ((Cons ((Pair (b, next)), Nil)),
      Nil)))
  | PVar j -> Pair ((Pair (j, next)), Nil)
  | PNeg g ->
    let Pair (p, c) = tseitin_aux g next in
    let Pair (o, n1) = p in
    Pair ((Pair (n1, (S n1))), (Cons ((Cons ((Pair (False, n1)), (Cons ((Pair
    (False, o)), Nil)))), (Cons ((Cons ((Pair (True, n1)), (Cons ((Pair
    (True, o)), Nil)))), c)))))
  | PAnd (g, h) ->
    let Pair (p, c1) = tseitin_aux g next in
    let Pair (o1, n1) = p in
    let Pair (p0, c2) = tseitin_aux h n1 in
    let Pair (o2, n2) = p0 in
    Pair ((Pair (n2, (S n2))), (Cons ((Cons ((Pair (False, n2)), (Cons ((Pair
    (True, o1)), Nil)))), (Cons ((Cons ((Pair (False, n2)), (Cons ((Pair
    (True, o2)), Nil)))), (Cons ((Cons ((Pair (False, o1)), (Cons ((Pair
    (False, o2)), (Cons ((Pair (True, n2)), Nil)))))), (app c1 c2))))))))
  | POr (g, h) ->
    let Pair (p, c1) = tseitin_aux g next in
    let Pair (o1, n1) = p in
    let Pair (p0, c2) = tseitin_aux h n1 in
    let Pair (o2, n2) = p0 in
    Pair ((Pair (n2, (S n2))), (Cons ((Cons ((Pair (False, n2)), (Cons ((Pair
    (True, o1)), (Cons ((Pair (True, o2)), Nil)))))), (Cons ((Cons ((Pair
    (False, o1)), (Cons ((Pair (True, n2)), Nil)))), (Cons ((Cons ((Pair
    (False, o2)), (Cons ((Pair (True, n2)), Nil)))), (app c1 c2))))))))

(** val tseitin : propFormula -> cNF **)

let tseitin f =
  let Pair (p, c) = tseitin_aux f (formula_var_bound f) in
  let Pair (o, _) = p in Cons ((Cons ((Pair (True, o)), Nil)), c)

(** val neg_code : concreteTerm -> bitStream **)

let neg_code t i =
  negb (term_code t i)

(** val reads : concreteTerm -> nat list **)

let rec reads = function
| TConst _ -> Nil
| TBit i -> Cons (i, Nil)
| TNot s -> reads s
| TAnd (s, u) -> app (reads s) (reads u)
| TOr (s, u) -> app (reads s) (reads u)
| TDup s -> map Nat.div2 (reads s)
| TProj s -> map Nat.div2 (filter Nat.even (reads s))
| TOracle l -> l

type boolOracle = bool list -> bool

type oracleArg =
| AConst of bool
| AVar of nat

(** val arg_eval : bitStream -> oracleArg -> bool **)

let arg_eval a = function
| AConst b -> b
| AVar j -> a j

type oFormula =
| OConst of bool
| OVar of nat
| ONeg of oFormula
| OAnd of oFormula * oFormula
| OOr of oFormula * oFormula
| OAtom of oracleArg list

(** val oformula_eval : boolOracle -> oFormula -> bitStream -> bool **)

let rec oformula_eval ob f a =
  match f with
  | OConst b -> b
  | OVar j -> a j
  | ONeg g -> negb (oformula_eval ob g a)
  | OAnd (g, h) ->
    (match oformula_eval ob g a with
     | True -> oformula_eval ob h a
     | False -> False)
  | OOr (g, h) ->
    (match oformula_eval ob g a with
     | True -> True
     | False -> oformula_eval ob h a)
  | OAtom args -> ob (map (arg_eval a) args)

(** val arg_bound : oracleArg -> nat **)

let arg_bound = function
| AConst _ -> O
| AVar j -> S j

(** val args_bound : oracleArg list -> nat **)

let rec args_bound = function
| Nil -> O
| Cons (c, l') -> add (arg_bound c) (args_bound l')

(** val oformula_var_bound : oFormula -> nat **)

let rec oformula_var_bound = function
| OConst _ -> O
| OVar j -> S j
| ONeg g -> oformula_var_bound g
| OAnd (g, h) -> add (oformula_var_bound g) (oformula_var_bound h)
| OOr (g, h) -> add (oformula_var_bound g) (oformula_var_bound h)
| OAtom args -> args_bound args

(** val otruth_table : boolOracle -> oFormula -> nat -> bitStream -> bool **)

let rec otruth_table ob f n a =
  match n with
  | O -> oformula_eval ob f a
  | S m ->
    (match otruth_table ob f m (stream_update a m False) with
     | True -> True
     | False -> otruth_table ob f m (stream_update a m True))

(** val oclassify : boolOracle -> oFormula -> bool **)

let oclassify ob f =
  otruth_table ob f (oformula_var_bound f) (fun _ -> False)

(** val embed_formula : propFormula -> oFormula **)

let rec embed_formula = function
| PConst b -> OConst b
| PVar j -> OVar j
| PNeg g -> ONeg (embed_formula g)
| PAnd (g, h) -> OAnd ((embed_formula g), (embed_formula h))
| POr (g, h) -> OOr ((embed_formula g), (embed_formula h))

(** val arg_formula : oracleArg -> oFormula **)

let arg_formula = function
| AConst b -> OConst b
| AVar j -> OVar j

(** val ospecialize : concreteTerm -> (nat -> oracleArg) -> oFormula **)

let rec ospecialize t acc =
  match t with
  | TConst b -> OConst b
  | TBit i -> arg_formula (acc i)
  | TNot s -> ONeg (ospecialize s acc)
  | TAnd (s, u) -> OAnd ((ospecialize s acc), (ospecialize u acc))
  | TOr (s, u) -> OOr ((ospecialize s acc), (ospecialize u acc))
  | TDup s -> ospecialize s (fun i -> acc (Nat.div2 i))
  | TProj _ -> OConst False
  | TOracle l -> OAtom (map acc l)

(** val claim_args : concreteTerm -> nat -> oracleArg **)

let claim_args v i =
  match Nat.even i with
  | True ->
    AConst
      (stream_pair (term_code (diagonal_term v))
        (term_code (diagonal_term v)) (Nat.div2 i))
  | False -> AVar (Nat.div2 i)

(** val oracle_specialized_formula : concreteTerm -> oFormula **)

let oracle_specialized_formula v =
  ospecialize v (claim_args v)
