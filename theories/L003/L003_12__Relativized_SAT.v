(*L003_12__Relativized_SAT.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                     Proofcase / L003_12__Relativized_SAT                     │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  The plain-SAT specialization relativized to a Boolean oracle. Propositional
  formulas gain an oracle atom whose arguments are constants or variables.
  Every oracle circuit, a verifier without projection but with oracle nodes,
  specializes at its own diagonal claim to such a formula, no larger than
  itself, whose satisfiability relative to the oracle is exactly the
  verifier's acceptance. Truth tables classify these formulas correctly for
  every Boolean oracle, so the Solver's Paradox for SAT holds relative to
  every Boolean-decidable oracle.

*)

From L003 Require Export L003_11__Evaluator_Lower_Bound.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               BOOLEAN ORACLES                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A Boolean oracle decides every query; it induces a
│          propositional oracle for the concrete language.
│
*)

Definition BoolOracle : Type := list bool -> bool.

Definition bool_oracle (ob : BoolOracle) : Oracle :=
  fun l => ob l = true.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               ORACLE FORMULAS                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          An oracle argument is a constant or a variable; an oracle
│          atom queries the oracle on the values of its arguments.
│
*)

Inductive OracleArg : Type :=
| AConst : bool -> OracleArg
| AVar : nat -> OracleArg.

Definition arg_eval (a : BitStream) (c : OracleArg) : bool :=
  match c with
  | AConst b => b
  | AVar j => a j
  end.

Inductive OFormula : Type :=
| OConst : bool -> OFormula
| OVar : nat -> OFormula
| ONeg : OFormula -> OFormula
| OAnd : OFormula -> OFormula -> OFormula
| OOr : OFormula -> OFormula -> OFormula
| OAtom : list OracleArg -> OFormula.

Fixpoint oformula_eval (ob : BoolOracle) (f : OFormula) (a : BitStream) : bool :=
  match f with
  | OConst b => b
  | OVar j => a j
  | ONeg g => negb (oformula_eval ob g a)
  | OAnd g h => oformula_eval ob g a && oformula_eval ob h a
  | OOr g h => oformula_eval ob g a || oformula_eval ob h a
  | OAtom args => ob (map (arg_eval a) args)
  end.

Definition OSatisfiable (ob : BoolOracle) (f : OFormula) : Prop :=
  exists a : BitStream, oformula_eval ob f a = true.

Definition arg_bound (c : OracleArg) : nat :=
  match c with
  | AConst _ => 0
  | AVar j => S j
  end.

Fixpoint args_bound (l : list OracleArg) : nat :=
  match l with
  | [] => 0
  | c :: l' => arg_bound c + args_bound l'
  end.

Fixpoint oformula_var_bound (f : OFormula) : nat :=
  match f with
  | OConst _ => 0
  | OVar j => S j
  | ONeg g => oformula_var_bound g
  | OAnd g h | OOr g h => oformula_var_bound g + oformula_var_bound h
  | OAtom args => args_bound args
  end.

(*
│
│          An oracle atom is one node, as an oracle node is one node
│          of a term.
│
*)

Fixpoint oformula_size (f : OFormula) : nat :=
  match f with
  | OConst _ | OVar _ | OAtom _ => 1
  | ONeg g => 1 + oformula_size g
  | OAnd g h | OOr g h => 1 + oformula_size g + oformula_size h
  end.

Lemma args_eval_agree :
  forall l (a b : BitStream),
    (forall i, i < args_bound l -> a i = b i) ->
    map (arg_eval a) l = map (arg_eval b) l.
Proof.
  induction l as [| c l IH]; intros a b H; simpl; [reflexivity |].
  f_equal.
  - destruct c as [bc | j]; simpl; [reflexivity |].
    apply H. simpl. lia.
  - apply IH. intros i Hi. apply H. simpl. lia.
Qed.

Lemma oformula_eval_agree :
  forall ob f a b,
    (forall i, i < oformula_var_bound f -> a i = b i) ->
    oformula_eval ob f a = oformula_eval ob f b.
Proof.
  intro ob.
  induction f as [c | j | g IH | g IHg h IHh | g IHg h IHh | args];
    simpl; intros a b H.
  - reflexivity.
  - apply H. lia.
  - rewrite (IH a b H). reflexivity.
  - rewrite (IHg a b), (IHh a b); try reflexivity;
      intros i Hi; apply H; lia.
  - rewrite (IHg a b), (IHh a b); try reflexivity;
      intros i Hi; apply H; lia.
  - rewrite (args_eval_agree args a b H). reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           RELATIVIZED TRUTH TABLES                           │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Fixpoint otruth_table (ob : BoolOracle) (f : OFormula) (n : nat) (a : BitStream) : bool :=
  match n with
  | O => oformula_eval ob f a
  | S m =>
      otruth_table ob f m (stream_update a m false) ||
      otruth_table ob f m (stream_update a m true)
  end.

Lemma otruth_table_sound :
  forall ob f n a,
    otruth_table ob f n a = true ->
    OSatisfiable ob f.
Proof.
  intros ob f n.
  induction n as [| m IH]; simpl; intros a H.
  - exists a. exact H.
  - apply orb_true_iff in H as [H | H]; eapply IH; exact H.
Qed.

Lemma otruth_table_complete :
  forall ob f n (a env : BitStream),
    (forall i, n <= i -> env i = a i) ->
    oformula_eval ob f env = true ->
    otruth_table ob f n a = true.
Proof.
  intros ob f n.
  induction n as [| m IH]; simpl; intros a env Hagree Heval.
  - rewrite <- (oformula_eval_agree ob f env a); [exact Heval |].
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

Definition oclassify (ob : BoolOracle) (f : OFormula) : bool :=
  otruth_table ob f (oformula_var_bound f) (fun _ => false).

(*
│
│          Truth tables classify every oracle formula correctly, for
│          every Boolean oracle.
│
*)

Theorem oclassify_correct :
  forall ob f, oclassify ob f = true <-> OSatisfiable ob f.
Proof.
  intros ob f.
  split; [apply otruth_table_sound |].
  intros [env Henv].
  set (env' := fun i => if i <? oformula_var_bound f then env i else false).
  apply (otruth_table_complete ob f (oformula_var_bound f) (fun _ => false) env').
  - intros i Hi.
    unfold env'.
    destruct (Nat.ltb_spec i (oformula_var_bound f)); [lia | reflexivity].
  - rewrite (oformula_eval_agree ob f env' env); [exact Henv |].
    intros i Hi.
    unfold env'.
    destruct (Nat.ltb_spec i (oformula_var_bound f)); [reflexivity | lia].
Qed.

Corollary osatisfiability_decidable :
  forall ob f, OSatisfiable ob f \/ ~ OSatisfiable ob f.
Proof.
  intros ob f.
  destruct (oclassify ob f) eqn:Hclass.
  - left. apply oclassify_correct. exact Hclass.
  - right. intro Hsat. apply oclassify_correct in Hsat. congruence.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            ORACLE-FREE AGREEMENT                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Plain formulas embed as oracle-free oracle formulas. On
│          them, evaluation, the variable bound, size, and
│          classification agree with the plain versions for every
│          oracle.
│
*)

Fixpoint embed_formula (f : PropFormula) : OFormula :=
  match f with
  | PConst b => OConst b
  | PVar j => OVar j
  | PNeg g => ONeg (embed_formula g)
  | PAnd g h => OAnd (embed_formula g) (embed_formula h)
  | POr g h => OOr (embed_formula g) (embed_formula h)
  end.

Lemma embed_formula_agrees :
  forall ob f a,
    oformula_eval ob (embed_formula f) a = formula_eval f a /\
    oformula_var_bound (embed_formula f) = formula_var_bound f /\
    oformula_size (embed_formula f) = formula_size f.
Proof.
  intros ob f a.
  induction f as [b | j | g IH | g IHg h IHh | g IHg h IHh]; simpl.
  - repeat split.
  - repeat split.
  - destruct IH as [He [Hb Hs]]. rewrite He, Hb, Hs. repeat split.
  - destruct IHg as [He1 [Hb1 Hs1]], IHh as [He2 [Hb2 Hs2]].
    rewrite He1, Hb1, Hs1, He2, Hb2, Hs2. repeat split.
  - destruct IHg as [He1 [Hb1 Hs1]], IHh as [He2 [Hb2 Hs2]].
    rewrite He1, Hb1, Hs1, He2, Hb2, Hs2. repeat split.
Qed.

Lemma otruth_table_embed :
  forall ob f n a,
    otruth_table ob (embed_formula f) n a = truth_table f n a.
Proof.
  intros ob f n.
  induction n as [| m IH]; intro a; simpl.
  - exact (proj1 (embed_formula_agrees ob f a)).
  - rewrite !IH. reflexivity.
Qed.

Theorem oclassify_embed :
  forall ob f, oclassify ob (embed_formula f) = classify f.
Proof.
  intros ob f.
  unfold oclassify, classify.
  rewrite (proj1 (proj2 (embed_formula_agrees ob f (fun _ => false)))).
  apply otruth_table_embed.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               ORACLE CIRCUITS                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          An oracle circuit contains no projection node; oracle nodes
│          are allowed. Every circuit verifier is an oracle circuit.
│
*)

Fixpoint OracleCircuit (t : ConcreteTerm) : Prop :=
  match t with
  | TConst _ | TBit _ | TOracle _ => True
  | TNot s | TDup s => OracleCircuit s
  | TAnd s u | TOr s u => OracleCircuit s /\ OracleCircuit u
  | TProj _ => False
  end.

Lemma circuit_verifier_oracle_circuit :
  forall t, CircuitVerifier t -> OracleCircuit t.
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intro H; tauto.
Qed.

Definition arg_formula (c : OracleArg) : OFormula :=
  match c with
  | AConst b => OConst b
  | AVar j => OVar j
  end.

(*
│
│          `ospecialize t acc` replaces each input bit `i` by the
│          argument `acc i`. Oracle nodes become oracle atoms over the
│          substituted arguments.
│
*)

Fixpoint ospecialize (t : ConcreteTerm) (acc : nat -> OracleArg) : OFormula :=
  match t with
  | TConst b => OConst b
  | TBit i => arg_formula (acc i)
  | TNot s => ONeg (ospecialize s acc)
  | TAnd s u => OAnd (ospecialize s acc) (ospecialize u acc)
  | TOr s u => OOr (ospecialize s acc) (ospecialize u acc)
  | TDup s => ospecialize s (fun i => acc (Nat.div2 i))
  | TProj _ => OConst false
  | TOracle l => OAtom (map acc l)
  end.

Lemma arg_formula_eval :
  forall ob c a, oformula_eval ob (arg_formula c) a = arg_eval a c.
Proof.
  intros ob c a.
  destruct c; reflexivity.
Qed.

Lemma ospecialize_correct :
  forall ob t,
    OracleCircuit t ->
    forall (acc : nat -> OracleArg) (env x : BitStream),
      (forall i, arg_eval env (acc i) = x i) ->
      (term_sem (bool_oracle ob) t x <->
       oformula_eval ob (ospecialize t acc) env = true).
Proof.
  intro ob.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intros Hcircuit acc env x Hacc.
  - tauto.
  - rewrite arg_formula_eval, Hacc. tauto.
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
  - unfold bool_oracle.
    rewrite map_map.
    rewrite (map_ext (fun i => arg_eval env (acc i)) x Hacc l).
    reflexivity.
Qed.

Lemma ospecialize_size :
  forall t (acc : nat -> OracleArg),
    oformula_size (ospecialize t acc) <= term_size t.
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intro acc.
  - lia.
  - destruct (acc i); simpl; lia.
  - specialize (IH acc). lia.
  - specialize (IHs acc). specialize (IHu acc). lia.
  - specialize (IHs acc). specialize (IHu acc). lia.
  - specialize (IH (fun i => acc (Nat.div2 i))). lia.
  - lia.
  - lia.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          RELATIVIZED SPECIALIZATION                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

Definition claim_args (v : ConcreteTerm) : nat -> OracleArg :=
  fun i =>
    if Nat.even i
    then AConst
           (stream_pair (term_code (diagonal_term v))
                        (term_code (diagonal_term v)) (Nat.div2 i))
    else AVar (Nat.div2 i).

Definition oracle_specialized_formula (v : ConcreteTerm) : OFormula :=
  ospecialize v (claim_args v).

Lemma claim_args_eval :
  forall v w i,
    arg_eval w (claim_args v i) =
    stream_pair
      (stream_pair (term_code (diagonal_term v)) (term_code (diagonal_term v)))
      w i.
Proof.
  intros v w i.
  unfold claim_args, stream_pair.
  destruct (Nat.even i); reflexivity.
Qed.

(*
│
│          On circuit verifiers the relativized specialization is the
│          plain one: the oracle formula is the embedded `psi_v`, so
│          its classification agrees with plain `classify`.
│
*)

Lemma ospecialize_embed :
  forall t (acc : nat -> PropFormula) (acc' : nat -> OracleArg),
    CircuitVerifier t ->
    (forall i, arg_formula (acc' i) = embed_formula (acc i)) ->
    ospecialize t acc' = embed_formula (specialize_term t acc).
Proof.
  induction t as [b | i | s IH | s IHs u IHu | s IHs u IHu | s IH | s IH | l];
    simpl; intros acc acc' Hcircuit Hacc.
  - reflexivity.
  - apply Hacc.
  - rewrite (IH acc acc' Hcircuit Hacc). reflexivity.
  - rewrite (IHs acc acc' (proj1 Hcircuit) Hacc),
      (IHu acc acc' (proj2 Hcircuit) Hacc).
    reflexivity.
  - rewrite (IHs acc acc' (proj1 Hcircuit) Hacc),
      (IHu acc acc' (proj2 Hcircuit) Hacc).
    reflexivity.
  - apply IH; [exact Hcircuit |].
    intro i. apply Hacc.
  - contradiction.
  - contradiction.
Qed.

Theorem relativized_agrees_on_circuits :
  forall ob v,
    CircuitVerifier v ->
    oracle_specialized_formula v = embed_formula (specialized_formula v) /\
    oclassify ob (oracle_specialized_formula v) = classify (specialized_formula v).
Proof.
  intros ob v Hcircuit.
  assert (Heq :
    oracle_specialized_formula v = embed_formula (specialized_formula v)).
  { apply ospecialize_embed; [exact Hcircuit |].
    intro i.
    unfold claim_args, claim_assignment.
    destruct (Nat.even i); reflexivity. }
  split; [exact Heq |].
  rewrite Heq.
  apply oclassify_embed.
Qed.

(*
│
│          Relativized specialization: for every Boolean oracle, an
│          oracle circuit accepts its own diagonal claim exactly when
│          its oracle formula is satisfiable relative to the oracle,
│          and that formula is no larger than the circuit.
│
*)

Theorem relativized_specialization :
  forall ob v,
    OracleCircuit v ->
    (ConcreteAccepted (bool_oracle ob) v <->
     OSatisfiable ob (oracle_specialized_formula v)) /\
    oformula_size (oracle_specialized_formula v) <= term_size v /\
    3 * oformula_size (oracle_specialized_formula v) <= term_level v.
Proof.
  intros ob v Hcircuit.
  assert (Hsize : oformula_size (oracle_specialized_formula v) <= term_size v)
    by apply ospecialize_size.
  split; [| split; [exact Hsize | pose proof (term_size_level v); lia]].
  unfold ConcreteAccepted, OSatisfiable, oracle_specialized_formula.
  split; intros [w Hw]; exists w.
  - exact
      (proj1
        (ospecialize_correct ob v Hcircuit (claim_args v) w _
           (claim_args_eval v w)) Hw).
  - exact
      (proj2
        (ospecialize_correct ob v Hcircuit (claim_args v) w _
           (claim_args_eval v w)) Hw).
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         RELATIVIZED SOLVER'S PARADOX                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          For every Boolean oracle and every oracle circuit `v`: the
│          oracle formula is no larger than `v`; relativized truth
│          tables classify it correctly; the diagonal claim holds
│          exactly when it is unsatisfiable; and exactly one of the
│          two branches holds.
│
*)

Theorem relativized_solvers_paradox :
  forall ob v,
    OracleCircuit v ->
    oformula_size (oracle_specialized_formula v) <= term_size v /\
    3 * oformula_size (oracle_specialized_formula v) <= term_level v /\
    (oclassify ob (oracle_specialized_formula v) = true <->
     OSatisfiable ob (oracle_specialized_formula v)) /\
    (ConcreteDiagonalClaim (bool_oracle ob) v <->
     ~ OSatisfiable ob (oracle_specialized_formula v)) /\
    ((OSatisfiable ob (oracle_specialized_formula v) /\
      ConcreteAccepted (bool_oracle ob) v /\
      ~ ConcreteDiagonalClaim (bool_oracle ob) v) \/
     (~ OSatisfiable ob (oracle_specialized_formula v) /\
      ~ ConcreteAccepted (bool_oracle ob) v /\
      ConcreteDiagonalClaim (bool_oracle ob) v)) /\
    ~ ((OSatisfiable ob (oracle_specialized_formula v) /\
        ConcreteAccepted (bool_oracle ob) v /\
        ~ ConcreteDiagonalClaim (bool_oracle ob) v) /\
       (~ OSatisfiable ob (oracle_specialized_formula v) /\
        ~ ConcreteAccepted (bool_oracle ob) v /\
        ConcreteDiagonalClaim (bool_oracle ob) v)).
Proof.
  intros ob v Hcircuit.
  destruct (relativized_specialization ob v Hcircuit) as [Hacc [Hsize Hlevel]].
  pose proof (concrete_fixed_point (bool_oracle ob) v) as Hfixed.
  assert (Hclaim :
    ConcreteDiagonalClaim (bool_oracle ob) v <->
    ~ OSatisfiable ob (oracle_specialized_formula v)).
  { rewrite Hfixed, Hacc. reflexivity. }
  split; [exact Hsize |].
  split; [exact Hlevel |].
  split; [apply oclassify_correct |].
  split; [exact Hclaim |].
  split.
  - destruct (osatisfiability_decidable ob (oracle_specialized_formula v))
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
│          The relativized obstruction is the abstract dichotomy, with
│          decidability supplied by relativized truth tables.
│
*)

Corollary relativized_universality_obstruction :
  forall ob v,
    OracleCircuit v ->
    CertificationFailsAtDiagonal (concrete_structure (bool_oracle ob)) v.
Proof.
  intros ob v Hcircuit.
  apply certification_dichotomy.
  destruct (relativized_specialization ob v Hcircuit) as [Hacc _].
  destruct (osatisfiability_decidable ob (oracle_specialized_formula v))
    as [Hsat | Hunsat].
  - left. exact (proj2 Hacc Hsat).
  - right. intro Ha. exact (Hunsat (proj1 Hacc Ha)).
Qed.
