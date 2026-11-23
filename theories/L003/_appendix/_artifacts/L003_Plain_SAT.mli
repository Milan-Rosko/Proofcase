
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val even : nat -> bool

  val div2 : nat -> nat
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : nat -> nat -> nat list

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

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

val stream_pair : bitStream -> bitStream -> bitStream

val unary_bits : nat -> bool list

val list_bits : nat list -> bool list

val term_serialize : concreteTerm -> bool list

val term_code : concreteTerm -> bitStream

val term_level : concreteTerm -> nat

val term_size : concreteTerm -> nat

val diagonal_term : concreteTerm -> concreteTerm

val proj_shift : (nat -> nat) -> nat -> nat

val reindex : concreteTerm -> (nat -> nat) -> concreteTerm

val bit_literal : bool -> nat -> concreteTerm

val match_bits : bool list -> nat -> concreteTerm

val even_position : nat -> nat

val odd_position : nat -> nat

val brute_force_entry : concreteTerm -> concreteTerm

val brute_force_list : concreteTerm list -> concreteTerm

val bounded_lists : nat -> nat -> nat list list

val terms_upto : nat -> concreteTerm list

val brute_force : nat -> concreteTerm

val concrete_certifier : nat -> concreteTerm

type propFormula =
| PConst of bool
| PVar of nat
| PNeg of propFormula
| PAnd of propFormula * propFormula
| POr of propFormula * propFormula

val formula_eval : propFormula -> bitStream -> bool

val formula_var_bound : propFormula -> nat

val formula_size : propFormula -> nat

val stream_update : bitStream -> nat -> bool -> bitStream

val truth_table : propFormula -> nat -> bitStream -> bool

val classify : propFormula -> bool

val circuit_verifierb : concreteTerm -> bool

val specialize_term : concreteTerm -> (nat -> propFormula) -> propFormula

val claim_assignment : concreteTerm -> nat -> propFormula

val specialized_formula : concreteTerm -> propFormula

type literal = (bool, nat) prod

type clause = literal list

type cNF = clause list

val lit_eval : bitStream -> literal -> bool

val clause_eval : bitStream -> clause -> bool

val cnf_eval : bitStream -> cNF -> bool

val tseitin_aux : propFormula -> nat -> ((nat, nat) prod, cNF) prod

val tseitin : propFormula -> cNF

val neg_code : concreteTerm -> bitStream

val reads : concreteTerm -> nat list

type boolOracle = bool list -> bool

type oracleArg =
| AConst of bool
| AVar of nat

val arg_eval : bitStream -> oracleArg -> bool

type oFormula =
| OConst of bool
| OVar of nat
| ONeg of oFormula
| OAnd of oFormula * oFormula
| OOr of oFormula * oFormula
| OAtom of oracleArg list

val oformula_eval : boolOracle -> oFormula -> bitStream -> bool

val arg_bound : oracleArg -> nat

val args_bound : oracleArg list -> nat

val oformula_var_bound : oFormula -> nat

val otruth_table : boolOracle -> oFormula -> nat -> bitStream -> bool

val oclassify : boolOracle -> oFormula -> bool

val embed_formula : propFormula -> oFormula

val arg_formula : oracleArg -> oFormula

val ospecialize : concreteTerm -> (nat -> oracleArg) -> oFormula

val claim_args : concreteTerm -> nat -> oracleArg

val oracle_specialized_formula : concreteTerm -> oFormula
