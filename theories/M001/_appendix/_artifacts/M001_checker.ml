
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

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

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

module Nat =
 struct
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

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | Nil -> None
        | Cons (x, _) -> Some x)
| S n0 -> (match l with
           | Nil -> None
           | Cons (_, l') -> nth_error l' n0)

type formula =
| Bot
| Imp of formula * formula

type context = formula list

type axiomSet =
  formula -> bool
  (* singleton inductive, whose constructor was Build_AxiomSet *)

type finiteAxiomSet =
  formula list
  (* singleton inductive, whose constructor was Build_FiniteAxiomSet *)

type regulatorLogicProfile =
| Regulator_profile_minimal
| Regulator_profile_with_efq

type regulatorTheory = { regulator_theory_profile : regulatorLogicProfile;
                         regulator_theory_axiom_set : axiomSet }

(** val regulator_theory_with_axiom_set :
    regulatorLogicProfile -> axiomSet -> regulatorTheory **)

let regulator_theory_with_axiom_set profile t =
  { regulator_theory_profile = profile; regulator_theory_axiom_set = t }

type justification =
| J_Assumption
| J_Axiom
| J_MP of nat * nat

type proofLine = { line_formula : formula; line_justification : justification }

type proof = proofLine list

(** val formula_eq_bool : formula -> formula -> bool **)

let rec formula_eq_bool a b =
  match a with
  | Bot -> (match b with
            | Bot -> True
            | Imp (_, _) -> False)
  | Imp (a1, a2) ->
    (match b with
     | Bot -> False
     | Imp (b1, b2) ->
       (match formula_eq_bool a1 b1 with
        | True -> formula_eq_bool a2 b2
        | False -> False))

(** val ctx_mem_bool : formula -> context -> bool **)

let rec ctx_mem_bool a = function
| Nil -> False
| Cons (b, gamma') ->
  (match formula_eq_bool a b with
   | True -> True
   | False -> ctx_mem_bool a gamma')

(** val finite_axiom_set_contains_bool : finiteAxiomSet -> formula -> bool **)

let finite_axiom_set_contains_bool fT a =
  ctx_mem_bool a fT

(** val finite_axiom_set_to_axiom_set : finiteAxiomSet -> axiomSet **)

let finite_axiom_set_to_axiom_set =
  finite_axiom_set_contains_bool

(** val k_axiom_bool : formula -> bool **)

let k_axiom_bool = function
| Bot -> False
| Imp (a, f) ->
  (match f with
   | Bot -> False
   | Imp (_, a') -> formula_eq_bool a a')

(** val s_axiom_bool : formula -> bool **)

let s_axiom_bool = function
| Bot -> False
| Imp (f, f0) ->
  (match f with
   | Bot -> False
   | Imp (a1, f1) ->
     (match f1 with
      | Bot -> False
      | Imp (b1, c1) ->
        (match f0 with
         | Bot -> False
         | Imp (f2, f3) ->
           (match f2 with
            | Bot -> False
            | Imp (a2, b2) ->
              (match f3 with
               | Bot -> False
               | Imp (a3, c2) ->
                 (match match match formula_eq_bool a1 a2 with
                              | True -> formula_eq_bool a1 a3
                              | False -> False with
                        | True -> formula_eq_bool b1 b2
                        | False -> False with
                  | True -> formula_eq_bool c1 c2
                  | False -> False))))))

(** val efq_axiom_bool : formula -> bool **)

let efq_axiom_bool = function
| Bot -> False
| Imp (f, _) -> (match f with
                 | Bot -> True
                 | Imp (_, _) -> False)

(** val logical_axiom_bool : regulatorLogicProfile -> formula -> bool **)

let logical_axiom_bool profile phi =
  match profile with
  | Regulator_profile_minimal ->
    (match k_axiom_bool phi with
     | True -> True
     | False -> s_axiom_bool phi)
  | Regulator_profile_with_efq ->
    (match match k_axiom_bool phi with
           | True -> True
           | False -> s_axiom_bool phi with
     | True -> True
     | False -> efq_axiom_bool phi)

(** val available_axiom_bool : regulatorTheory -> formula -> bool **)

let available_axiom_bool r phi =
  match logical_axiom_bool r.regulator_theory_profile phi with
  | True -> True
  | False -> r.regulator_theory_axiom_set phi

(** val nth_formula : proofLine list -> nat -> formula option **)

let nth_formula prefix i =
  match nth_error prefix i with
  | Some line -> Some line.line_formula
  | None -> None

(** val pl_assumption : formula -> proofLine **)

let pl_assumption a =
  { line_formula = a; line_justification = J_Assumption }

(** val pl_axiom : formula -> proofLine **)

let pl_axiom a =
  { line_formula = a; line_justification = J_Axiom }

(** val pl_mp : formula -> nat -> nat -> proofLine **)

let pl_mp a i j =
  { line_formula = a; line_justification = (J_MP (i, j)) }

(** val last_formula : proof -> formula option **)

let rec last_formula = function
| Nil -> None
| Cons (line, p') ->
  (match p' with
   | Nil -> Some line.line_formula
   | Cons (_, _) -> last_formula p')

(** val mp_orientation_left_bool : formula -> formula -> formula -> bool **)

let mp_orientation_left_bool fi fj target =
  match fj with
  | Bot -> False
  | Imp (c, b) ->
    (match formula_eq_bool fi c with
     | True -> formula_eq_bool b target
     | False -> False)

(** val mp_orientation_right_bool : formula -> formula -> formula -> bool **)

let mp_orientation_right_bool fi fj target =
  match fi with
  | Bot -> False
  | Imp (c, b) ->
    (match formula_eq_bool c fj with
     | True -> formula_eq_bool b target
     | False -> False)

(** val mp_valid_bool : proofLine list -> nat -> nat -> formula -> bool **)

let mp_valid_bool prefix i j target =
  match nth_formula prefix i with
  | Some fi ->
    (match nth_formula prefix j with
     | Some fj ->
       (match mp_orientation_left_bool fi fj target with
        | True -> True
        | False -> mp_orientation_right_bool fi fj target)
     | None -> False)
  | None -> False

(** val proof_line_valid_bool :
    regulatorTheory -> context -> proofLine list -> proofLine -> bool **)

let proof_line_valid_bool r gamma prefix line =
  let phi = line.line_formula in
  (match line.line_justification with
   | J_Assumption -> ctx_mem_bool phi gamma
   | J_Axiom -> available_axiom_bool r phi
   | J_MP (i, j) ->
     (match match Nat.ltb i (length prefix) with
            | True -> Nat.ltb j (length prefix)
            | False -> False with
      | True -> mp_valid_bool prefix i j phi
      | False -> False))

(** val proof_script_check_from_bool :
    regulatorTheory -> context -> proofLine list -> proofLine list -> bool **)

let rec proof_script_check_from_bool r gamma prefix = function
| Nil -> True
| Cons (line, rest) ->
  (match proof_line_valid_bool r gamma prefix line with
   | True ->
     proof_script_check_from_bool r gamma (app prefix (Cons (line, Nil))) rest
   | False -> False)

(** val regulator_theory_check_bool :
    regulatorTheory -> context -> proof -> formula -> bool **)

let regulator_theory_check_bool r gamma p a =
  match proof_script_check_from_bool r gamma Nil p with
  | True ->
    (match last_formula p with
     | Some b -> formula_eq_bool b a
     | None -> False)
  | False -> False

(** val finite_axiom_set_to_regulator_theory :
    regulatorLogicProfile -> finiteAxiomSet -> regulatorTheory **)

let finite_axiom_set_to_regulator_theory profile t =
  regulator_theory_with_axiom_set profile (finite_axiom_set_to_axiom_set t)

(** val finite_axiom_set_check_bool :
    regulatorLogicProfile -> finiteAxiomSet -> context -> proof -> formula ->
    bool **)

let finite_axiom_set_check_bool profile t gamma p a =
  regulator_theory_check_bool
    (finite_axiom_set_to_regulator_theory profile t) gamma p a

(** val k_axiom_formula : formula -> formula -> formula **)

let k_axiom_formula a b =
  Imp (a, (Imp (b, a)))

(** val s_axiom_formula : formula -> formula -> formula -> formula **)

let s_axiom_formula a b c =
  Imp ((Imp (a, (Imp (b, c)))), (Imp ((Imp (a, b)), (Imp (a, c)))))

(** val deduction_identity_block_from : nat -> formula -> proof **)

let deduction_identity_block_from base a =
  Cons ((pl_axiom (k_axiom_formula a a)), (Cons
    ((pl_axiom (k_axiom_formula a (Imp (a, a)))), (Cons
    ((pl_axiom (s_axiom_formula a (Imp (a, a)) a)), (Cons
    ((pl_mp (Imp ((Imp (a, (Imp (a, a)))), (Imp (a, a))))
       (add base (S (S O))) (add base (S O))),
    (Cons ((pl_mp (Imp (a, a)) (add base (S (S (S O)))) (add base O)),
    Nil)))))))))

(** val deduction_assumption_lift_block_from :
    nat -> formula -> formula -> proof **)

let deduction_assumption_lift_block_from base a c =
  Cons ((pl_assumption c), (Cons ((pl_axiom (k_axiom_formula c a)), (Cons
    ((pl_mp (Imp (a, c)) (add base O) (add base (S O))), Nil)))))

(** val deduction_axiom_lift_block_from :
    nat -> formula -> formula -> proof **)

let deduction_axiom_lift_block_from base a c =
  Cons ((pl_axiom c), (Cons ((pl_axiom (k_axiom_formula c a)), (Cons
    ((pl_mp (Imp (a, c)) (add base O) (add base (S O))), Nil)))))

(** val deduction_mp_lift_block_from :
    nat -> formula -> formula -> formula -> nat -> nat -> proof **)

let deduction_mp_lift_block_from base a c b idx_imp idx_arg =
  Cons ((pl_axiom (s_axiom_formula a c b)), (Cons
    ((pl_mp (Imp ((Imp (a, c)), (Imp (a, b)))) (add base O) idx_imp), (Cons
    ((pl_mp (Imp (a, b)) (add base (S O)) idx_arg), Nil)))))

type deductionState = { deduction_state_output : proof;
                        deduction_state_index_map : nat list }

(** val deduction_state_empty : deductionState **)

let deduction_state_empty =
  { deduction_state_output = Nil; deduction_state_index_map = Nil }

(** val deduction_state_next_index : deductionState -> nat **)

let deduction_state_next_index st =
  length st.deduction_state_output

(** val deduction_state_append_block :
    deductionState -> proof -> nat -> deductionState **)

let deduction_state_append_block st block final_offset =
  let base = deduction_state_next_index st in
  { deduction_state_output = (app st.deduction_state_output block);
  deduction_state_index_map =
  (app st.deduction_state_index_map (Cons ((add base final_offset), Nil))) }

(** val deduction_state_append_identity :
    formula -> deductionState -> deductionState **)

let deduction_state_append_identity a st =
  deduction_state_append_block st
    (deduction_identity_block_from (deduction_state_next_index st) a) (S (S
    (S (S O))))

(** val deduction_state_append_assumption_lift :
    formula -> formula -> deductionState -> deductionState **)

let deduction_state_append_assumption_lift a c st =
  deduction_state_append_block st
    (deduction_assumption_lift_block_from (deduction_state_next_index st) a c)
    (S (S O))

(** val deduction_state_append_axiom_lift :
    formula -> formula -> deductionState -> deductionState **)

let deduction_state_append_axiom_lift a c st =
  deduction_state_append_block st
    (deduction_axiom_lift_block_from (deduction_state_next_index st) a c) (S
    (S O))

(** val deduction_state_append_mp_lift :
    formula -> formula -> formula -> nat -> nat -> deductionState ->
    deductionState **)

let deduction_state_append_mp_lift a c b idx_imp idx_arg st =
  deduction_state_append_block st
    (deduction_mp_lift_block_from (deduction_state_next_index st) a c b
      idx_imp idx_arg)
    (S (S O))

(** val deduction_transform_mp_line :
    formula -> formula -> proofLine list -> nat -> nat -> deductionState ->
    deductionState **)

let deduction_transform_mp_line a target source_prefix i j st =
  match nth_formula source_prefix i with
  | Some fi ->
    (match nth_formula source_prefix j with
     | Some fj ->
       (match nth_error st.deduction_state_index_map i with
        | Some idx_i ->
          (match nth_error st.deduction_state_index_map j with
           | Some idx_j ->
             (match mp_orientation_left_bool fi fj target with
              | True ->
                deduction_state_append_mp_lift a fi target idx_j idx_i st
              | False ->
                (match mp_orientation_right_bool fi fj target with
                 | True ->
                   deduction_state_append_mp_lift a fj target idx_i idx_j st
                 | False -> deduction_state_append_identity a st))
           | None -> deduction_state_append_identity a st)
        | None -> deduction_state_append_identity a st)
     | None -> deduction_state_append_identity a st)
  | None -> deduction_state_append_identity a st

(** val deduction_transform_line :
    formula -> proofLine list -> proofLine -> deductionState -> deductionState **)

let deduction_transform_line a source_prefix line st =
  let phi = line.line_formula in
  (match line.line_justification with
   | J_Assumption ->
     (match formula_eq_bool phi a with
      | True -> deduction_state_append_identity a st
      | False -> deduction_state_append_assumption_lift a phi st)
   | J_Axiom -> deduction_state_append_axiom_lift a phi st
   | J_MP (i, j) -> deduction_transform_mp_line a phi source_prefix i j st)

(** val deduction_transform_lines :
    formula -> proofLine list -> proofLine list -> deductionState ->
    deductionState **)

let rec deduction_transform_lines a source_prefix todo st =
  match todo with
  | Nil -> st
  | Cons (line, rest) ->
    let st' = deduction_transform_line a source_prefix line st in
    deduction_transform_lines a (app source_prefix (Cons (line, Nil))) rest
      st'

(** val regulator_theory_deduction_transform : formula -> proof -> proof **)

let regulator_theory_deduction_transform a p =
  (deduction_transform_lines a Nil p deduction_state_empty).deduction_state_output

(** val regulator_theory_reductio_transform : formula -> proof -> proof **)

let regulator_theory_reductio_transform =
  regulator_theory_deduction_transform

(** val proof_script_shift_index : nat -> nat -> nat **)

let proof_script_shift_index =
  add

(** val proof_script_shift_justification :
    nat -> justification -> justification **)

let proof_script_shift_justification offset = function
| J_MP (i, k) ->
  J_MP ((proof_script_shift_index offset i),
    (proof_script_shift_index offset k))
| x -> x

(** val proof_script_shift_line : nat -> proofLine -> proofLine **)

let proof_script_shift_line offset line =
  { line_formula = line.line_formula; line_justification =
    (proof_script_shift_justification offset line.line_justification) }

(** val proof_script_shift : nat -> proof -> proof **)

let proof_script_shift offset p =
  map (proof_script_shift_line offset) p

(** val proof_script_last_index : proof -> nat **)

let proof_script_last_index p =
  pred (length p)

(** val regulator_theory_mp_compose : formula -> proof -> proof -> proof **)

let regulator_theory_mp_compose b p_imp p_arg =
  let offset = length p_imp in
  let shifted_arg = proof_script_shift offset p_arg in
  app (app p_imp shifted_arg) (Cons
    ((pl_mp b (proof_script_last_index p_imp)
       (add offset (proof_script_last_index p_arg))),
    Nil))
