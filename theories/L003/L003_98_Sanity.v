(*L003_98_Sanity.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                          Proofcase / L003_98_Sanity                          │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Sanity layer for L003/SOLVER'S PARADOX. Closed computations exercise
  grading, reindexing, enumeration, truth-table classification,
  circuit-verifier recognition, specialization at the diagonal claim, and
  Tseitin conversion; the minimal branches, the brute-force family, and the
  main theorem are re-read against the public artifact import.

*)

From L003 Require Import L003_97_Artifacts.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                 TRUTH TABLES                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `p /\ ~ p` is unsatisfiable and `p \/ ~ p` is satisfiable;
│          truth tables decide both.
│
*)

Example sanity_contradiction_unsat :
  classify (PAnd (PVar 0) (PNeg (PVar 0))) = false.
Proof. vm_compute. reflexivity. Qed.

Example sanity_tautology_sat :
  classify (POr (PVar 0) (PNeg (PVar 0))) = true.
Proof. vm_compute. reflexivity. Qed.

(*
│
│          A satisfiable formula over three variables whose only model
│          sets `x0 = x2 = true` and `x1 = false`.
│
*)

Example sanity_three_variable_sat :
  classify
    (PAnd (PVar 0) (PAnd (PNeg (PVar 1)) (PVar 2))) = true.
Proof. vm_compute. reflexivity. Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           GRADING AND ENUMERATION                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Constants have level four; each formation operation adds
│          three, so the diagonal term of a constant has level
│          thirteen.
│
*)

Example sanity_constant_level :
  term_level (TConst true) = 4 /\
  term_level (diagonal_term (TConst true)) = 13.
Proof. vm_compute. split; reflexivity. Qed.

(*
│
│          Reindexing absorbs duplication into the index map and
│          shifts reads under projection.
│
*)

Example sanity_reindex_dup :
  reindex (TDup (TBit 3)) odd_position = TBit 3.
Proof. vm_compute. reflexivity. Qed.

Example sanity_reindex_proj :
  reindex (TProj (TAnd (TBit 0) (TBit 1))) odd_position =
  TProj (TAnd (TBit 2) (TBit 1)).
Proof. vm_compute. reflexivity. Qed.

(*
│
│          The enumeration over-approximates each level: `terms_upto
│          1` lists both constants, the bit reader `TBit 0`, and the
│          oracle queries at `[]` and `[0]`; `terms_upto 2` already
│          has 76 entries.
│
*)

Example sanity_enumeration_small :
  terms_upto 1 = [TConst false; TConst true; TBit 0; TOracle []; TOracle [0]] /\
  length (terms_upto 2) = 76.
Proof. vm_compute. split; reflexivity. Qed.

Example sanity_brute_force_family :
  BoundedCertificationFamily (concrete_structure empty_oracle) concrete_certifier.
Proof. exact (concrete_certification_family empty_oracle). Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CIRCUIT VERIFIERS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Example sanity_circuit_verifier_accepts_circuit :
  circuit_verifierb (TAnd (TBit 0) (TDup (TNot (TBit 3)))) = true.
Proof. vm_compute. reflexivity. Qed.

Example sanity_circuit_verifier_rejects_projection :
  circuit_verifierb (TOr (TBit 0) (TProj (TBit 1))) = false.
Proof. vm_compute. reflexivity. Qed.

Example sanity_circuit_verifier_rejects_oracle :
  circuit_verifierb (TAnd (TBit 0) (TOracle [1; 2])) = false.
Proof. vm_compute. reflexivity. Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                SPECIALIZATION                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The constant verifiers specialize to constant formulas, and
│          their classification matches the two minimal branches.
│
*)

Example sanity_accept_all_specializes :
  specialized_formula (TConst true) = PConst true /\
  classify (specialized_formula (TConst true)) = true.
Proof. vm_compute. split; reflexivity. Qed.

Example sanity_accept_none_specializes :
  specialized_formula (TConst false) = PConst false /\
  classify (specialized_formula (TConst false)) = false.
Proof. vm_compute. split; reflexivity. Qed.

(*
│
│          A verifier reading witness bit 0 (stream position 1)
│          specializes to the variable `PVar 0`; it is satisfiable, so
│          the dichotomy places it in the first branch.
│
*)

Definition sanity_witness_reader : ConcreteTerm :=
  TBit 1.

Example sanity_witness_reader_specializes :
  specialized_formula sanity_witness_reader = PVar 0.
Proof. vm_compute. reflexivity. Qed.

Example sanity_witness_reader_first_branch :
  ConcreteAccepted empty_oracle sanity_witness_reader /\
  ~ ConcreteDiagonalClaim empty_oracle sanity_witness_reader.
Proof.
  destruct (universality_obstruction empty_oracle sanity_witness_reader I)
    as [Hfirst | [Hnacc _]].
  - exact Hfirst.
  - exfalso.
    apply Hnacc.
    apply (proj1 (specialization empty_oracle sanity_witness_reader I)).
    exists (fun _ => true).
    reflexivity.
Qed.

(*
│
│          A verifier reading claim bit 0 specializes to the first bit
│          of the quotation of its own diagonal term.
│
*)

Definition sanity_claim_reader : ConcreteTerm :=
  TBit 0.

Example sanity_claim_reader_specializes :
  specialized_formula sanity_claim_reader =
  PConst (term_code (diagonal_term sanity_claim_reader) 0).
Proof. vm_compute. reflexivity. Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                   TSEITIN                                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The Tseitin CNF of `p /\ ~ p` has five clauses: the root
│          unit clause, three for the conjunction, and two for the
│          negation. The model sets `p` true, the negation variable
│          `x1` false, and the conjunction variable `x2` true, and
│          violates the root clause.
│
*)

Example sanity_tseitin_contradiction :
  length (tseitin (PAnd (PVar 0) (PNeg (PVar 0)))) = 6 /\
  cnf_eval (fun i => Nat.eqb i 0 || Nat.eqb i 2)
    (tseitin (PAnd (PVar 0) (PNeg (PVar 0)))) = false.
Proof. vm_compute. split; reflexivity. Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CODING SENSITIVITY                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The first bit of the quotation of `g_v` is the first bit of
│          the negation tag: `false` under the standard quotation,
│          `true` under the negated one.
│
*)

Example sanity_first_quotation_bit :
  term_code (diagonal_term (TBit 0)) 0 = false /\
  neg_code (diagonal_term (TBit 0)) 0 = true.
Proof. vm_compute. split; reflexivity. Qed.

Example sanity_branch_flip :
  (~ QuotedAccepted empty_oracle term_code (TBit 0) /\
   QuotedClaim empty_oracle term_code (TBit 0)) /\
  (QuotedAccepted empty_oracle neg_code (TBit 0) /\
   ~ QuotedClaim empty_oracle neg_code (TBit 0)).
Proof. exact (branch_depends_on_quotation empty_oracle). Qed.

(*
│
│          The diagonal of `TBit 0` lies exactly nine bits above it.
│
*)

Example sanity_diagonal_nine_above :
  term_level (TBit 0) = 4 /\ term_level (diagonal_term (TBit 0)) = 13.
Proof. vm_compute. split; reflexivity. Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        READ POSITIONS AND LOWER BOUND                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Duplication halves read positions, projection keeps only
│          even ones; the quotations of `TBit 2` and `TBit 3` differ
│          only at position five.
│
*)

Example sanity_reads :
  reads (TDup (TBit 5)) = [2] /\
  reads (TProj (TAnd (TBit 4) (TBit 3))) = [2].
Proof. vm_compute. split; reflexivity. Qed.

Example sanity_one_bit_pair :
  term_code (TBit 2) 5 = false /\ term_code (TBit 3) 5 = true /\
  term_code (TBit 2) 6 = term_code (TBit 3) 6.
Proof. vm_compute. repeat split. Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               RELATIVIZED SAT                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          With the parity oracle, the atom querying bits zero and one
│          is satisfiable and its negation together with both bits set
│          is not.
│
*)

Definition sanity_parity : BoolOracle :=
  fun l => fold_right xorb false l.

Example sanity_oclassify :
  oclassify sanity_parity (OAtom [AVar 0; AVar 1]) = true /\
  oclassify sanity_parity
    (OAnd (OAtom [AVar 0; AVar 1]) (OAnd (OVar 0) (OVar 1))) = false.
Proof. vm_compute. split; reflexivity. Qed.

Example sanity_oracle_circuit_specializes :
  oracle_specialized_formula (TOracle [1]) = OAtom [AVar 0].
Proof. vm_compute. reflexivity. Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                INTERNAL MODEL                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Example sanity_internal_model : INTERNAL_MODEL_CONTRACT.
Proof. exact (conj internal_premises_satisfiable language_premises_satisfiable). Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                THEOREM SHAPES                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The certified endpoints inhabit their public contracts, and
│          the concrete diagonal claim is literally the size-free
│          diagonal claim of `concrete_language O`.
│
*)

Example sanity_core_endpoint : L003_CORE_CONTRACT := l003_core_qed.

Example sanity_contract_endpoint : L003_CONTRACT := l003_contract_qed.

Example sanity_concrete_is_size_free :
  forall O v,
    ConcreteDiagonalClaim O v <-> ~ SizeFreeDiagonalAccepted (concrete_language O) v.
Proof.
  intros O v.
  exact (size_free_fixed_point (concrete_language O) v).
Qed.
