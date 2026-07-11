
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

module Nat :
 sig
  val pred : Big_int_Z.big_int -> Big_int_Z.big_int

  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val even : Big_int_Z.big_int -> bool

  val odd : Big_int_Z.big_int -> bool

  val div2 : Big_int_Z.big_int -> Big_int_Z.big_int
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val of_succ_nat : Big_int_Z.big_int -> positive
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val nth_error : 'a1 list -> Big_int_Z.big_int -> 'a1 option

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

module Z :
 sig
  val of_nat : Big_int_Z.big_int -> z
 end

val fib_pair : Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

val fib : Big_int_Z.big_int -> Big_int_Z.big_int

val sum_fib : Big_int_Z.big_int list -> Big_int_Z.big_int

val two : Big_int_Z.big_int -> Big_int_Z.big_int

val two_j_minus1 : Big_int_Z.big_int -> Big_int_Z.big_int

type params =
| Build_Params of (Big_int_Z.big_int -> Big_int_Z.big_int list)
   * (Big_int_Z.big_int -> Big_int_Z.big_int)

val z0 : params -> Big_int_Z.big_int -> Big_int_Z.big_int list

val r : params -> Big_int_Z.big_int -> Big_int_Z.big_int

val b : params -> Big_int_Z.big_int -> Big_int_Z.big_int

val even_band : params -> Big_int_Z.big_int -> Big_int_Z.big_int list

val odd_band :
  params -> Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list

val half_even_indices : Big_int_Z.big_int list -> Big_int_Z.big_int list

val odd_ge_B1 : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val decode_odd_index :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val y_indices :
  Big_int_Z.big_int -> Big_int_Z.big_int list -> Big_int_Z.big_int list

val find_r_aux :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int

val r0 : Big_int_Z.big_int -> Big_int_Z.big_int

val zeck_greedy_down :
  Big_int_Z.big_int -> Big_int_Z.big_int -> bool -> Big_int_Z.big_int
  list * Big_int_Z.big_int

val z1 : Big_int_Z.big_int -> Big_int_Z.big_int list

val base_params : params

val boundary : Big_int_Z.big_int -> Big_int_Z.big_int

val even_band_of : Big_int_Z.big_int -> Big_int_Z.big_int list

val odd_band_of :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list

val encode : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val half_even_support : Big_int_Z.big_int list -> Big_int_Z.big_int list

val odd_support_indices :
  Big_int_Z.big_int -> Big_int_Z.big_int list -> Big_int_Z.big_int list

val decode : Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

val sTATUS_REJECT : Big_int_Z.big_int

val sTATUS_ACCEPT : Big_int_Z.big_int

val accept : Big_int_Z.big_int -> Big_int_Z.big_int

val code_error :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int

val reject :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int

val sTAGE_DERIVATION_HEADER : Big_int_Z.big_int

val sTAGE_LIST_STRUCTURE : Big_int_Z.big_int

val sTAGE_LINE : Big_int_Z.big_int

val sTAGE_TAG : Big_int_Z.big_int

val sTAGE_FORMULA : Big_int_Z.big_int

val sTAGE_RULE : Big_int_Z.big_int

val sTAGE_CONCLUSION : Big_int_Z.big_int

val eRR_NONCANONICAL_DERIVATION : Big_int_Z.big_int

val eRR_BAD_DERIVATION_LENGTH : Big_int_Z.big_int

val eRR_EMPTY_DERIVATION : Big_int_Z.big_int

val eRR_BAD_CONCLUSION : Big_int_Z.big_int

val eRR_FUEL_EXHAUSTED : Big_int_Z.big_int

val eRR_NONCANONICAL_NODE : Big_int_Z.big_int

val eRR_BAD_TAG : Big_int_Z.big_int

val eRR_BAD_LIST_TAG : Big_int_Z.big_int

val eRR_INDEX_OUT_OF_RANGE : Big_int_Z.big_int

val eRR_NONCANONICAL_LINE : Big_int_Z.big_int

val eRR_UNKNOWN_RULE : Big_int_Z.big_int

val eRR_NONCANONICAL_FORMULA : Big_int_Z.big_int

val eRR_BAD_FORMULA_TAG : Big_int_Z.big_int

val eRR_BAD_IMP_PAYLOAD : Big_int_Z.big_int

val eRR_NOT_IMP : Big_int_Z.big_int

val eRR_AXK_NOT_IMP_1 : Big_int_Z.big_int

val eRR_AXK_NOT_IMP_2 : Big_int_Z.big_int

val eRR_AXK_A_MISMATCH : Big_int_Z.big_int

val eRR_AXK_BAD_A : Big_int_Z.big_int

val eRR_AXK_BAD_B : Big_int_Z.big_int

val eRR_AXS_NOT_IMP_1 : Big_int_Z.big_int

val eRR_AXS_NOT_IMP_2 : Big_int_Z.big_int

val eRR_AXS_NOT_IMP_3 : Big_int_Z.big_int

val eRR_AXS_NOT_IMP_4 : Big_int_Z.big_int

val eRR_AXS_NOT_IMP_5 : Big_int_Z.big_int

val eRR_AXS_NOT_IMP_6 : Big_int_Z.big_int

val eRR_AXS_A_MISMATCH_LEFT : Big_int_Z.big_int

val eRR_AXS_A_MISMATCH_RIGHT : Big_int_Z.big_int

val eRR_AXS_B_MISMATCH : Big_int_Z.big_int

val eRR_AXS_C_MISMATCH : Big_int_Z.big_int

val eRR_AXS_BAD_A : Big_int_Z.big_int

val eRR_AXS_BAD_B : Big_int_Z.big_int

val eRR_AXS_BAD_C : Big_int_Z.big_int

val eRR_MP_P_NOT_LT_J : Big_int_Z.big_int

val eRR_MP_Q_NOT_LT_J : Big_int_Z.big_int

val eRR_MP_BAD_LINE_J : Big_int_Z.big_int

val eRR_MP_BAD_LINE_P : Big_int_Z.big_int

val eRR_MP_BAD_LINE_Q : Big_int_Z.big_int

val eRR_MP_Q_NOT_IMP : Big_int_Z.big_int

val eRR_MP_ANTECEDENT_MISMATCH : Big_int_Z.big_int

val eRR_MP_CONSEQUENT_MISMATCH : Big_int_Z.big_int

val fst001 : Big_int_Z.big_int -> Big_int_Z.big_int

val snd001 : Big_int_Z.big_int -> Big_int_Z.big_int

val recode001 : Big_int_Z.big_int -> Big_int_Z.big_int

val canonical001b : Big_int_Z.big_int -> bool

val is_pair001b :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val tAG_NIL : Big_int_Z.big_int

val tAG_CONS : Big_int_Z.big_int

val code_nil : Big_int_Z.big_int

val code_cons : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val list_tag : Big_int_Z.big_int -> Big_int_Z.big_int

val list_payload : Big_int_Z.big_int -> Big_int_Z.big_int

val is_nil_nodeb : Big_int_Z.big_int -> bool

val cons_payloadb : Big_int_Z.big_int -> bool

val list_exact_lengthb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val nth_list_fuel :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int

val tAG_VAR : Big_int_Z.big_int

val tAG_IMP : Big_int_Z.big_int

val formula_tag : Big_int_Z.big_int -> Big_int_Z.big_int

val formula_payload : Big_int_Z.big_int -> Big_int_Z.big_int

val is_formula_fuel : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val formula_bound : Big_int_Z.big_int -> Big_int_Z.big_int

val is_formula : Big_int_Z.big_int -> bool

val parse_imp : Big_int_Z.big_int -> Big_int_Z.big_int

val parse_formula_diagnostic : Big_int_Z.big_int -> Big_int_Z.big_int

val line_tag : Big_int_Z.big_int -> Big_int_Z.big_int

val line_formula : Big_int_Z.big_int -> Big_int_Z.big_int

val rULE_AXK : Big_int_Z.big_int

val rULE_AXS : Big_int_Z.big_int

val rULE_MP : Big_int_Z.big_int

val rule_code : Big_int_Z.big_int -> Big_int_Z.big_int

val rule_payload : Big_int_Z.big_int -> Big_int_Z.big_int

val parse_rule_tag : Big_int_Z.big_int -> Big_int_Z.big_int

val parse_line : Big_int_Z.big_int -> Big_int_Z.big_int

val result_status : Big_int_Z.big_int -> Big_int_Z.big_int

val result_payload : Big_int_Z.big_int -> Big_int_Z.big_int

val acceptedb : Big_int_Z.big_int -> bool

val parsed_line_formula : Big_int_Z.big_int -> Big_int_Z.big_int

val nth_line :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int

val check_axk : Big_int_Z.big_int -> Big_int_Z.big_int

val check_axs : Big_int_Z.big_int -> Big_int_Z.big_int

val line_formula_result :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int -> Big_int_Z.big_int

val check_mp :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val code_local_cert_payload :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val code_final_cert_payload :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int -> Big_int_Z.big_int

val verify_line :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int

val verify_lines :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val final_formula_result :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val a002_Verify : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

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

val normalized_formula_eqb : normalizedFormula -> normalizedFormula -> bool

val normalized_stepb :
  normalizedFormula list -> normalizedRule -> normalizedFormula -> bool

val normalized_linesb : normalizedFormula list -> normalizedDerivation -> bool

val normalized_conclusion : normalizedDerivation -> normalizedFormula option

val normalized_verifyb : normalizedDerivation -> normalizedFormula -> bool

val normalize_formula_fuel :
  Big_int_Z.big_int -> Big_int_Z.big_int -> normalizedFormula option

val normalize_formula : Big_int_Z.big_int -> normalizedFormula option

val normalize_rule : Big_int_Z.big_int -> normalizedRule option

val normalize_line : Big_int_Z.big_int -> normalizedLine option

val normalize_lines :
  Big_int_Z.big_int -> Big_int_Z.big_int -> normalizedDerivation option

val normalize_derivation : Big_int_Z.big_int -> normalizedDerivation option

val a002_Verify_certified :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val a002_Certified_Certb :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool

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

val a002_Verified :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val a002_Certificate_Check :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bool

val a002_Parse_Formula : Big_int_Z.big_int -> Big_int_Z.big_int

val a002_Parse_Line : Big_int_Z.big_int -> Big_int_Z.big_int

val a002_IO : a002_IO_Query -> a002_IO_Result

val decode_Result : Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

val decode_Error :
  Big_int_Z.big_int ->
  (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int

val verify_Diagnostic :
  Big_int_Z.big_int -> Big_int_Z.big_int ->
  (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int

val a002_Verified_Z : Big_int_Z.big_int -> Big_int_Z.big_int -> z

val a002_Parse_Formula_Z : Big_int_Z.big_int -> z

val a002_Parse_Line_Z : Big_int_Z.big_int -> z

type a002_IO_Result_Z =
| Verify_Result_Z of z
| Cert_Check_Result_Z of bool
| Parse_Result_Z of z

val a002_IO_Z : a002_IO_Query -> a002_IO_Result_Z

val verify_Diagnostic_Z :
  Big_int_Z.big_int -> Big_int_Z.big_int -> (z * z) * z
