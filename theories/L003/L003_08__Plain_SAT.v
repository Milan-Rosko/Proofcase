(*L003_08__Plain_SAT.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Proofcase / L003_08__Plain_SAT                        │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Plain propositional formulas and a constructive truth-table classifier.
  Every circuit verifier specializes, at its own diagonal claim, to a
  propositional formula no larger than itself whose satisfiability is exactly
  the verifier's acceptance, relative to any oracle. Truth tables classify
  that formula correctly, the internal brute-force evaluator of any level
  containing the verifier lies above that level up to diagonal cost, and the
  verifier fails to certify its associated verdict: this is the Solver's
  Paradox for plain SAT.

  Classification and certification are distinct. Nothing in this file
  concerns the complexity of satisfiability.

*)

From L003 Require Export L003_07__Exhaustive_Evaluation.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            PROPOSITIONAL FORMULAS                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Plain propositional formulas: constants, variables,
│          negation, conjunction, disjunction. An assignment is a bit
│          stream.
│
*)

Inductive PropFormula : Type :=
| PConst : bool -> PropFormula
| PVar : nat -> PropFormula
| PNeg : PropFormula -> PropFormula
| PAnd : PropFormula -> PropFormula -> PropFormula
| POr : PropFormula -> PropFormula -> PropFormula.

Fixpoint formula_eval (f : PropFormula) (a : BitStream) : bool :=
  match f with
  | PConst b => b
  | PVar j => a j
  | PNeg f1 => negb (formula_eval f1 a)
  | PAnd f1 f2 => formula_eval f1 a && formula_eval f2 a
  | POr f1 f2 => formula_eval f1 a || formula_eval f2 a
  end.

Definition Satisfiable (f : PropFormula) : Prop :=
  exists a : BitStream, formula_eval f a = true.

(*
│
│          `formula_var_bound f` bounds every variable index of `f`.
│          It is a sum rather than a maximum; only the bound matters.
│
*)

Fixpoint formula_var_bound (f : PropFormula) : nat :=
  match f with
  | PConst _ => 0
  | PVar j => S j
  | PNeg f1 => formula_var_bound f1
  | PAnd f1 f2 | POr f1 f2 => formula_var_bound f1 + formula_var_bound f2
  end.

Fixpoint formula_size (f : PropFormula) : nat :=
  match f with
  | PConst _ | PVar _ => 1
  | PNeg f1 => 1 + formula_size f1
  | PAnd f1 f2 | POr f1 f2 => 1 + formula_size f1 + formula_size f2
  end.

Lemma formula_eval_agree :
  forall f a b,
    (forall i, i < formula_var_bound f -> a i = b i) ->
    formula_eval f a = formula_eval f b.
Proof.
  induction f as [c | j | f1 IH1 | f1 IH1 f2 IH2 | f1 IH1 f2 IH2];
    simpl; intros a b H.
  - reflexivity.
  - apply H. lia.
  - rewrite (IH1 a b H). reflexivity.
  - rewrite (IH1 a b), (IH2 a b); try reflexivity;
      intros i Hi; apply H; lia.
  - rewrite (IH1 a b), (IH2 a b); try reflexivity;
      intros i Hi; apply H; lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                 TRUTH TABLES                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition stream_update (a : BitStream) (n : nat) (b : bool) : BitStream :=
  fun i => if Nat.eqb i n then b else a i.

(*
│
│          Truth-table search over the variables below `n`, starting
│          from the background assignment `a`.
│
*)

Fixpoint truth_table (f : PropFormula) (n : nat) (a : BitStream) : bool :=
  match n with
  | O => formula_eval f a
  | S m =>
      truth_table f m (stream_update a m false) ||
      truth_table f m (stream_update a m true)
  end.

Lemma truth_table_sound :
  forall f n a,
    truth_table f n a = true ->
    Satisfiable f.
Proof.
  intros f n.
  induction n as [| m IH]; simpl; intros a H.
  - exists a. exact H.
  - apply orb_true_iff in H as [H | H]; eapply IH; exact H.
Qed.

Lemma truth_table_complete :
  forall f n (a env : BitStream),
    (forall i, n <= i -> env i = a i) ->
    formula_eval f env = true ->
    truth_table f n a = true.
Proof.
  intros f n.
  induction n as [| m IH]; simpl; intros a env Hagree Heval.
  - rewrite <- (formula_eval_agree f env a); [exact Heval |].
    intros i _.
    apply Hagree.
    lia.
  - apply orb_true_iff.
    assert (Hnext : forall i, m <= i -> env i = stream_update a m (env m) i).
    { intros i Hi.
      unfold stream_update.
      destruct (Nat.eqb_spec i m) as [Heq | Hneq].
      - subst. reflexivity.
      - apply Hagree. lia. }
    pose proof (IH _ env Hnext Heval) as Hkey.
    revert Hkey.
    destruct (env m); intro Hkey; [right | left]; exact Hkey.
Qed.

Definition classify (f : PropFormula) : bool :=
  truth_table f (formula_var_bound f) (fun _ => false).

(*
│
│          Truth tables classify every formula correctly.
│
*)

Theorem classify_correct :
  forall f, classify f = true <-> Satisfiable f.
Proof.
  intro f.
  split; [apply truth_table_sound |].
  intros [env Henv].
  set (env' := fun i => if i <? formula_var_bound f then env i else false).
  apply (truth_table_complete f (formula_var_bound f) (fun _ => false) env').
  - intros i Hi.
    unfold env'.
    destruct (Nat.ltb_spec i (formula_var_bound f)); [lia | reflexivity].
  - rewrite (formula_eval_agree f env' env); [exact Henv |].
    intros i Hi.
    unfold env'.
    destruct (Nat.ltb_spec i (formula_var_bound f)); [reflexivity | lia].
Qed.

Corollary satisfiability_decidable :
  forall f, Satisfiable f \/ ~ Satisfiable f.
Proof.
  intro f.
  destruct (classify f) eqn:Hclass.
  - left. apply classify_correct. exact Hclass.
  - right. intro Hsat. apply classify_correct in Hsat. congruence.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CIRCUIT VERIFIERS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A circuit verifier contains no projection node and no
│          oracle node. The Boolean test is reflected into the
│          propositional predicate.
│
*)

Fixpoint CircuitVerifier (t : ConcreteTerm) : Prop :=
  match t with
  | TConst _ | TBit _ => True
  | TNot s | TDup s => CircuitVerifier s
  | TAnd s u | TOr s u => CircuitVerifier s /\ CircuitVerifier u
  | TProj _ | TOracle _ => False
  end.

Fixpoint circuit_verifierb (t : ConcreteTerm) : bool :=
  match t with
  | TConst _ | TBit _ => true
  | TNot s | TDup s => circuit_verifierb s
  | TAnd s u | TOr s u => circuit_verifierb s && circuit_verifierb u
  | TProj _ | TOracle _ => false
  end.

Lemma circuit_verifierb_iff :
  forall t, circuit_verifierb t = true <-> CircuitVerifier t.
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl.
  - split; intros _; [exact I | reflexivity].
  - split; intros _; [exact I | reflexivity].
  - exact IH.
  - rewrite andb_true_iff, IHs, IHu. tauto.
  - rewrite andb_true_iff, IHs, IHu. tauto.
  - exact IH.
  - split; [discriminate | contradiction].
  - split; [discriminate | contradiction].
Qed.

(*
│
│          Circuit verifiers are oracle-free.
│
*)

Lemma circuit_verifier_oracle_free :
  forall t, CircuitVerifier t -> OracleFree t.
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intro H; try tauto.
Qed.


(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                SPECIALIZATION                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `specialize_term t acc` replaces each input bit `i` by the
│          formula `acc i`. Duplication only redirects bit indices and
│          introduces no formula node. Projection and oracle nodes,
│          absent from circuit verifiers, become `false`.
│
*)

Fixpoint specialize_term
    (t : ConcreteTerm)
    (acc : nat -> PropFormula) : PropFormula :=
  match t with
  | TConst b => PConst b
  | TBit i => acc i
  | TNot s => PNeg (specialize_term s acc)
  | TAnd s u => PAnd (specialize_term s acc) (specialize_term u acc)
  | TOr s u => POr (specialize_term s acc) (specialize_term u acc)
  | TDup s => specialize_term s (fun i => acc (Nat.div2 i))
  | TProj _ | TOracle _ => PConst false
  end.

Lemma negation_bridge :
  forall (Q : Prop) (b : bool),
    (Q <-> b = true) ->
    (~ Q <-> negb b = true).
Proof.
  intros Q b H.
  destruct b; simpl; split.
  - intro Hn. exfalso. apply Hn. apply H. reflexivity.
  - intro Hf. discriminate Hf.
  - intros _. reflexivity.
  - intros _ HQ. apply H in HQ. discriminate HQ.
Qed.

Lemma specialize_term_correct :
  forall O t,
    CircuitVerifier t ->
    forall (acc : nat -> PropFormula) (env x : BitStream),
      (forall i, formula_eval (acc i) env = x i) ->
      (term_sem O t x <-> formula_eval (specialize_term t acc) env = true).
Proof.
  intro O.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intros Hcircuit acc env x Hacc.
  - tauto.
  - rewrite Hacc. tauto.
  - apply negation_bridge.
    apply IH; assumption.
  - rewrite andb_true_iff.
    rewrite (IHs (proj1 Hcircuit) acc env x Hacc),
      (IHu (proj2 Hcircuit) acc env x Hacc).
    tauto.
  - rewrite orb_true_iff.
    rewrite (IHs (proj1 Hcircuit) acc env x Hacc),
      (IHu (proj2 Hcircuit) acc env x Hacc).
    tauto.
  - apply IH; [exact Hcircuit |].
    intro i.
    unfold stream_pair.
    destruct (Nat.even i); apply Hacc.
  - contradiction.
  - contradiction.
Qed.

Lemma specialize_term_size :
  forall t (acc : nat -> PropFormula),
    (forall i, formula_size (acc i) = 1) ->
    formula_size (specialize_term t acc) <= term_size t.
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intros acc Hacc.
  - lia.
  - rewrite Hacc. lia.
  - specialize (IH acc Hacc). lia.
  - specialize (IHs acc Hacc). specialize (IHu acc Hacc). lia.
  - specialize (IHs acc Hacc). specialize (IHu acc Hacc). lia.
  - specialize (IH (fun i => acc (Nat.div2 i)) (fun i => Hacc _)). lia.
  - lia.
  - lia.
Qed.

(*
│
│          At the diagonal claim of `v`, claim bits (even positions)
│          become constants and witness bits (odd positions) become
│          propositional variables.
│
*)

Definition claim_assignment (v : ConcreteTerm) : nat -> PropFormula :=
  fun i =>
    if Nat.even i
    then PConst
           (stream_pair (term_code (diagonal_term v))
                        (term_code (diagonal_term v)) (Nat.div2 i))
    else PVar (Nat.div2 i).

Definition specialized_formula (v : ConcreteTerm) : PropFormula :=
  specialize_term v (claim_assignment v).

Lemma claim_assignment_eval :
  forall v w i,
    formula_eval (claim_assignment v i) w =
    stream_pair
      (stream_pair (term_code (diagonal_term v)) (term_code (diagonal_term v)))
      w i.
Proof.
  intros v w i.
  unfold claim_assignment, stream_pair.
  destruct (Nat.even i); reflexivity.
Qed.

(*
│
│          Specialization: relative to every oracle, acceptance at the
│          diagonal claim is satisfiability of `psi_v`, and `psi_v` is
│          no larger than `v`: at most its node count, hence at most a
│          third of its level.
│
*)

Theorem specialization :
  forall O v,
    CircuitVerifier v ->
    (ConcreteAccepted O v <-> Satisfiable (specialized_formula v)) /\
    formula_size (specialized_formula v) <= term_size v /\
    3 * formula_size (specialized_formula v) <= term_level v.
Proof.
  intros O v Hcircuit.
  assert (Hsize : formula_size (specialized_formula v) <= term_size v).
  { apply specialize_term_size.
    intro i.
    unfold claim_assignment.
    destruct (Nat.even i); reflexivity. }
  split; [| split; [exact Hsize | pose proof (term_size_level v); lia]].
  - unfold ConcreteAccepted, Satisfiable, specialized_formula.
    split; intros [w Hw]; exists w.
    + exact
        (proj1
          (specialize_term_correct O v Hcircuit (claim_assignment v) w _
             (claim_assignment_eval v w)) Hw).
    + exact
        (proj2
          (specialize_term_correct O v Hcircuit (claim_assignment v) w _
             (claim_assignment_eval v w)) Hw).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                        SOLVER'S PARADOX FOR PLAIN SAT                        │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `BF_n` settles the diagonal claim of `v` at every level
│          containing `g_v`.
│
*)

Lemma brute_force_settles_diagonal :
  forall O v n,
    term_level (diagonal_term v) <= n ->
    (term_sem O (brute_force n)
       (stream_pair (term_code (diagonal_term v)) (term_code (diagonal_term v)))
     <-> ConcreteDiagonalClaim O v).
Proof.
  intros O v n Hn.
  exact (evaluator_settles_diagonal (concrete_structure O) v
           (brute_force n) n Hn (brute_force_evaluates O n)).
Qed.

(*
│
│          For every oracle and every circuit verifier `v`: (i)
│          `psi_v` is no larger than `v`, in node count and in a third
│          of the level; (ii) truth tables classify it correctly;
│          (iii) `g_v` lies exactly nine bits above `v`, the internal
│          brute-force evaluator at the level of `g_v` settles the
│          diagonal claim, and every internal evaluator whose domain
│          contains `g_v` lies more than three bits above `v`; (iv)
│          the diagonal claim holds exactly when `psi_v` is
│          unsatisfiable; (v) exactly one of two branches holds.
│          Decidability of satisfiability of `psi_v` splits the
│          branches.
│
*)

Theorem solvers_paradox_plain_sat :
  forall O v,
    CircuitVerifier v ->
    formula_size (specialized_formula v) <= term_size v /\
    3 * formula_size (specialized_formula v) <= term_level v /\
    (classify (specialized_formula v) = true <->
     Satisfiable (specialized_formula v)) /\
    (term_level (diagonal_term v) = term_level v + 9 /\
     (term_sem O (brute_force (term_level (diagonal_term v)))
        (stream_pair (term_code (diagonal_term v)) (term_code (diagonal_term v)))
      <-> ConcreteDiagonalClaim O v) /\
     (forall B n,
        term_level (diagonal_term v) <= n ->
        Evaluates (concrete_structure O) B n ->
        term_level v + 3 < term_level B)) /\
    (ConcreteDiagonalClaim O v <-> ~ Satisfiable (specialized_formula v)) /\
    ((Satisfiable (specialized_formula v) /\ ConcreteAccepted O v /\
      ~ ConcreteDiagonalClaim O v) \/
     (~ Satisfiable (specialized_formula v) /\ ~ ConcreteAccepted O v /\
      ConcreteDiagonalClaim O v)) /\
    ~ ((Satisfiable (specialized_formula v) /\ ConcreteAccepted O v /\
        ~ ConcreteDiagonalClaim O v) /\
       (~ Satisfiable (specialized_formula v) /\ ~ ConcreteAccepted O v /\
        ConcreteDiagonalClaim O v)).
Proof.
  intros O v Hcircuit.
  destruct (specialization O v Hcircuit) as [Hacc [Hsize Hlevel]].
  pose proof (concrete_fixed_point O v) as Hfixed.
  assert (Hclaim :
    ConcreteDiagonalClaim O v <-> ~ Satisfiable (specialized_formula v)).
  { rewrite Hfixed, Hacc. reflexivity. }
  split; [exact Hsize |].
  split; [exact Hlevel |].
  split; [apply classify_correct |].
  split.
  { split; [exact (diagonal_term_level v) |].
    split.
    - exact (brute_force_settles_diagonal O v _ (le_n _)).
    - intros B n Hdomain HB.
      exact (settler_above_verifier (concrete_structure O) v B n
               (concrete_exact_costs O) Hdomain HB). }
  split; [exact Hclaim |].
  split.
  - destruct (satisfiability_decidable (specialized_formula v))
      as [Hsat | Hunsat].
    + left.
      split; [exact Hsat |].
      split; [apply Hacc; exact Hsat |].
      intro Hc.
      exact (proj1 Hclaim Hc Hsat).
    + right.
      split; [exact Hunsat |].
      split; [intro Ha; exact (Hunsat (proj1 Hacc Ha)) |].
      apply Hclaim.
      exact Hunsat.
  - intros [[Hsat _] [Hunsat _]].
    exact (Hunsat Hsat).
Qed.

(*
│
│          The obstruction part: relative to every oracle, every
│          circuit verifier accepts a false diagonal claim or leaves a
│          true one uncertified. This is the abstract dichotomy, with
│          decidability of acceptance supplied by truth tables.
│
*)

Corollary universality_obstruction :
  forall O v,
    CircuitVerifier v ->
    CertificationFailsAtDiagonal (concrete_structure O) v.
Proof.
  intros O v Hcircuit.
  apply certification_dichotomy.
  destruct (specialization O v Hcircuit) as [Hacc _].
  destruct (satisfiability_decidable (specialized_formula v))
    as [Hsat | Hunsat].
  - left. exact (proj2 Hacc Hsat).
  - right. intro Ha. exact (Hunsat (proj1 Hacc Ha)).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               MINIMAL BRANCHES                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The verifier accepting every certificate, `TConst true`,
│          realizes the first branch relative to every oracle: its
│          diagonal claim is false although accepted.
│
*)

Theorem accept_all_realizes_first_branch :
  forall O,
    Satisfiable (specialized_formula (TConst true)) /\
    ConcreteAccepted O (TConst true) /\
    ~ ConcreteDiagonalClaim O (TConst true).
Proof.
  intro O.
  destruct (solvers_paradox_plain_sat O (TConst true) I)
    as [_ [_ [_ [_ [_ [Hbranch _]]]]]].
  destruct Hbranch as [Hfirst | [Hunsat _]].
  - exact Hfirst.
  - exfalso.
    apply Hunsat.
    exists (fun _ => false).
    reflexivity.
Qed.

(*
│
│          The verifier accepting no certificate, `TConst false`,
│          realizes the second branch relative to every oracle: its
│          diagonal claim is true although uncertified.
│
*)

Theorem accept_none_realizes_second_branch :
  forall O,
    ~ Satisfiable (specialized_formula (TConst false)) /\
    ~ ConcreteAccepted O (TConst false) /\
    ConcreteDiagonalClaim O (TConst false).
Proof.
  intro O.
  destruct (solvers_paradox_plain_sat O (TConst false) I)
    as [_ [_ [_ [_ [_ [Hbranch _]]]]]].
  destruct Hbranch as [[[a Ha] _] | Hsecond].
  - cbn in Ha. discriminate Ha.
  - exact Hsecond.
Qed.
