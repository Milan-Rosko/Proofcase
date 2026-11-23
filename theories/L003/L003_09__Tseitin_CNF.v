(*L003_09__Tseitin_CNF.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / L003_09__Tseitin_CNF                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Tseitin conversion of plain propositional formulas into CNF. Each formula
  node receives a fresh variable constrained by at most three clauses of
  width at most three; the root variable is asserted. The CNF is
  equisatisfiable with the formula and linear in its size, so the
  specialization of every circuit verifier lands directly in the clause
  language.

*)

From L003 Require Export L003_08__Plain_SAT.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                   CLAUSES                                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A literal is a polarity and a variable; a clause is a
│          disjunction of literals; a CNF is a conjunction of clauses.
│
*)

Definition Literal : Type := (bool * nat)%type.
Definition Clause : Type := list Literal.
Definition CNF : Type := list Clause.

Definition lit_eval (a : BitStream) (l : Literal) : bool :=
  let (b, j) := l in if b then a j else negb (a j).

Definition clause_eval (a : BitStream) (c : Clause) : bool :=
  existsb (lit_eval a) c.

Definition cnf_eval (a : BitStream) (F : CNF) : bool :=
  forallb (clause_eval a) F.

Definition CNFSatisfiable (F : CNF) : Prop :=
  exists a : BitStream, cnf_eval a F = true.

(*
│
│          Every variable of `F` lies below `n`.
│
*)

Definition CNFBelow (F : CNF) (n : nat) : Prop :=
  forall c, In c F -> forall l, In l c -> snd l < n.

Lemma cnf_eval_agree :
  forall F n a b,
    CNFBelow F n ->
    (forall i, i < n -> a i = b i) ->
    cnf_eval a F = cnf_eval b F.
Proof.
  induction F as [| c F IH]; intros n a b Hbelow Hagree; [reflexivity |].
  simpl.
  rewrite (IH n a b); [| intros c' Hc'; apply Hbelow; right; exact Hc' | exact Hagree].
  f_equal.
  unfold clause_eval.
  assert (Hc : forall l, In l c -> snd l < n).
  { apply Hbelow. left. reflexivity. }
  clear IH Hbelow.
  induction c as [| [p j] c IHc]; [reflexivity |].
  simpl.
  rewrite (Hagree j (Hc (p, j) (or_introl eq_refl))).
  rewrite IHc; [reflexivity |].
  intros l Hl. apply Hc. right. exact Hl.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              TSEITIN CONVERSION                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `tseitin_aux f next` returns the variable carrying the
│          value of `f`, the next free variable, and the defining
│          clauses. Variables of `f` are reused; constants, negations,
│          conjunctions, and disjunctions get fresh variables from
│          `next` on.
│
*)

Fixpoint tseitin_aux (f : PropFormula) (next : nat) : nat * nat * CNF :=
  match f with
  | PConst b => (next, S next, [[(b, next)]])
  | PVar j => (j, next, [])
  | PNeg g =>
      let '(o, n1, C) := tseitin_aux g next in
      (n1, S n1, [(false, n1); (false, o)] :: [(true, n1); (true, o)] :: C)
  | PAnd g h =>
      let '(o1, n1, C1) := tseitin_aux g next in
      let '(o2, n2, C2) := tseitin_aux h n1 in
      (n2, S n2,
       [(false, n2); (true, o1)] :: [(false, n2); (true, o2)] ::
       [(false, o1); (false, o2); (true, n2)] :: C1 ++ C2)
  | POr g h =>
      let '(o1, n1, C1) := tseitin_aux g next in
      let '(o2, n2, C2) := tseitin_aux h n1 in
      (n2, S n2,
       [(false, n2); (true, o1); (true, o2)] :: [(false, o1); (true, n2)] ::
       [(false, o2); (true, n2)] :: C1 ++ C2)
  end.

(*
│
│          Fresh variables start above every variable of the formula;
│          the root variable is asserted by a unit clause.
│
*)

Definition tseitin (f : PropFormula) : CNF :=
  let '(o, _, C) := tseitin_aux f (formula_var_bound f) in
  [(true, o)] :: C.

Ltac split_andb :=
  repeat match goal with
         | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
         end.

(*
│
│          Any assignment satisfying the defining clauses gives the
│          root variable the value of the formula. No freshness is
│          needed in this direction.
│
*)

Lemma tseitin_aux_sound :
  forall f next o n' C a,
    tseitin_aux f next = (o, n', C) ->
    cnf_eval a C = true ->
    a o = formula_eval f a.
Proof.
  induction f as [b | j | g IH | g IHg h IHh | g IHg h IHh];
    intros next o n' C a Haux HC; simpl in Haux.
  - injection Haux as <- <- <-.
    simpl in HC.
    destruct b, (a next); simpl in *; congruence.
  - injection Haux as <- <- <-. reflexivity.
  - destruct (tseitin_aux g next) as [[o1 n1] C1] eqn:Eg.
    injection Haux as <- <- <-.
    simpl in HC.
    split_andb.
    pose proof (IH next o1 n1 C1 a Eg ltac:(assumption)) as Ho.
    simpl.
    rewrite <- Ho.
    destruct (a n1), (a o1); simpl in *; congruence.
  - destruct (tseitin_aux g next) as [[o1 n1] C1] eqn:Eg.
    destruct (tseitin_aux h n1) as [[o2 n2] C2] eqn:Eh.
    injection Haux as <- <- <-.
    unfold cnf_eval in HC.
    simpl in HC.
    rewrite forallb_app in HC.
    split_andb.
    pose proof (IHg next o1 n1 C1 a Eg ltac:(assumption)) as Ho1.
    pose proof (IHh n1 o2 n2 C2 a Eh ltac:(assumption)) as Ho2.
    simpl.
    rewrite <- Ho1, <- Ho2.
    destruct (a n2), (a o1), (a o2); simpl in *; congruence.
  - destruct (tseitin_aux g next) as [[o1 n1] C1] eqn:Eg.
    destruct (tseitin_aux h n1) as [[o2 n2] C2] eqn:Eh.
    injection Haux as <- <- <-.
    unfold cnf_eval in HC.
    simpl in HC.
    rewrite forallb_app in HC.
    split_andb.
    pose proof (IHg next o1 n1 C1 a Eg ltac:(assumption)) as Ho1.
    pose proof (IHh n1 o2 n2 C2 a Eh ltac:(assumption)) as Ho2.
    simpl.
    rewrite <- Ho1, <- Ho2.
    destruct (a n2), (a o1), (a o2); simpl in *; congruence.
Qed.

(*
│
│          Bounds: fresh variables are allocated upward, at most one
│          per node; the root and every clause variable lie below the
│          next free variable; there are at most three clauses per
│          node, each of width at most three.
│
*)

Ltac small_clause_bound :=
  let c := fresh "c" in
  let Hc := fresh "Hc" in
  let l := fresh "l" in
  let Hl := fresh "Hl" in
  intros c Hc l Hl;
  simpl in Hc;
  repeat (destruct Hc as [Hc | Hc];
          [subst c; simpl in Hl;
           repeat (destruct Hl as [Hl | Hl]; [subst l; simpl; lia |]);
           contradiction |]).

Ltac small_clause_width :=
  let c := fresh "c" in
  let Hc := fresh "Hc" in
  intros c Hc;
  simpl in Hc;
  repeat (destruct Hc as [Hc | Hc]; [subst c; simpl; lia |]).

Lemma tseitin_aux_bounds :
  forall f next o n' C,
    tseitin_aux f next = (o, n', C) ->
    formula_var_bound f <= next ->
    next <= n' /\
    n' <= next + formula_size f /\
    o < n' /\
    CNFBelow C n' /\
    length C <= 3 * formula_size f /\
    (forall c, In c C -> length c <= 3).
Proof.
  induction f as [b | j | g IH | g IHg h IHh | g IHg h IHh];
    intros next o n' C Haux Hbound; simpl in Haux, Hbound.
  - injection Haux as <- <- <-.
    simpl.
    repeat split; try lia.
    + small_clause_bound. contradiction.
    + small_clause_width. contradiction.
  - injection Haux as <- <- <-.
    simpl.
    repeat split; try lia.
    all: intros c [].
  - destruct (tseitin_aux g next) as [[o1 n1] C1] eqn:Eg.
    injection Haux as <- <- <-.
    destruct (IH next o1 n1 C1 Eg Hbound)
      as [Hle [Hsize [Ho [Hbelow [Hlen Hwidth]]]]].
    simpl.
    repeat split; try lia.
    + small_clause_bound.
      pose proof (Hbelow _ Hc _ Hl). lia.
    + small_clause_width.
      exact (Hwidth _ Hc).
  - destruct (tseitin_aux g next) as [[o1 n1] C1] eqn:Eg.
    destruct (tseitin_aux h n1) as [[o2 n2] C2] eqn:Eh.
    injection Haux as <- <- <-.
    destruct (IHg next o1 n1 C1 Eg ltac:(lia))
      as [Hle1 [Hsize1 [Ho1 [Hbelow1 [Hlen1 Hwidth1]]]]].
    destruct (IHh n1 o2 n2 C2 Eh ltac:(lia))
      as [Hle2 [Hsize2 [Ho2 [Hbelow2 [Hlen2 Hwidth2]]]]].
    simpl.
    rewrite length_app.
    repeat split; try lia.
    + small_clause_bound.
      apply in_app_or in Hc as [Hc | Hc].
      * pose proof (Hbelow1 _ Hc _ Hl). lia.
      * pose proof (Hbelow2 _ Hc _ Hl). lia.
    + small_clause_width.
      apply in_app_or in Hc as [Hc | Hc];
        [exact (Hwidth1 _ Hc) | exact (Hwidth2 _ Hc)].
  - destruct (tseitin_aux g next) as [[o1 n1] C1] eqn:Eg.
    destruct (tseitin_aux h n1) as [[o2 n2] C2] eqn:Eh.
    injection Haux as <- <- <-.
    destruct (IHg next o1 n1 C1 Eg ltac:(lia))
      as [Hle1 [Hsize1 [Ho1 [Hbelow1 [Hlen1 Hwidth1]]]]].
    destruct (IHh n1 o2 n2 C2 Eh ltac:(lia))
      as [Hle2 [Hsize2 [Ho2 [Hbelow2 [Hlen2 Hwidth2]]]]].
    simpl.
    rewrite length_app.
    repeat split; try lia.
    + small_clause_bound.
      apply in_app_or in Hc as [Hc | Hc].
      * pose proof (Hbelow1 _ Hc _ Hl). lia.
      * pose proof (Hbelow2 _ Hc _ Hl). lia.
    + small_clause_width.
      apply in_app_or in Hc as [Hc | Hc];
        [exact (Hwidth1 _ Hc) | exact (Hwidth2 _ Hc)].
Qed.

(*
│
│          Every assignment extends, by setting the fresh variables to
│          the values of their subformulas, to one satisfying the
│          defining clauses. The extension agrees with the original
│          below `next`.
│
*)

Lemma tseitin_aux_complete :
  forall f next o n' C a,
    tseitin_aux f next = (o, n', C) ->
    formula_var_bound f <= next ->
    exists a',
      (forall i, i < next -> a' i = a i) /\
      cnf_eval a' C = true /\
      a' o = formula_eval f a.
Proof.
  induction f as [b | j | g IH | g IHg h IHh | g IHg h IHh];
    intros next o n' C a Haux Hbound; simpl in Haux, Hbound.
  - injection Haux as <- <- <-.
    exists (stream_update a next b).
    assert (Hnew : stream_update a next b next = b).
    { unfold stream_update. rewrite Nat.eqb_refl. reflexivity. }
    split.
    + intros i Hi.
      unfold stream_update.
      destruct (Nat.eqb_spec i next); [lia | reflexivity].
    + split; [| exact Hnew].
      unfold cnf_eval. simpl.
      rewrite Hnew.
      destruct b; reflexivity.
  - injection Haux as <- <- <-.
    exists a.
    split; [reflexivity |].
    split; reflexivity.
  - destruct (tseitin_aux g next) as [[o1 n1] C1] eqn:Eg.
    injection Haux as <- <- <-.
    destruct (IH next o1 n1 C1 a Eg Hbound) as [a1 [Hagree1 [HC1 Ho1]]].
    destruct (tseitin_aux_bounds g next o1 n1 C1 Eg Hbound)
      as [Hle [_ [Hlt [Hbelow _]]]].
    exists (stream_update a1 n1 (negb (formula_eval g a))).
    assert (Hkeep : forall i, i < n1 ->
              stream_update a1 n1 (negb (formula_eval g a)) i = a1 i).
    { intros i Hi. unfold stream_update.
      destruct (Nat.eqb_spec i n1); [lia | reflexivity]. }
    split.
    + intros i Hi. rewrite Hkeep by lia. apply Hagree1. exact Hi.
    + assert (Hnew : stream_update a1 n1 (negb (formula_eval g a)) n1 =
                     negb (formula_eval g a)).
      { unfold stream_update. rewrite Nat.eqb_refl. reflexivity. }
      split.
      * unfold cnf_eval. simpl.
        fold (cnf_eval (stream_update a1 n1 (negb (formula_eval g a))) C1).
        rewrite (cnf_eval_agree C1 n1 _ a1 Hbelow Hkeep), HC1.
        rewrite Hnew, (Hkeep o1 Hlt), Ho1.
        destruct (formula_eval g a); reflexivity.
      * rewrite Hnew. reflexivity.
  - destruct (tseitin_aux g next) as [[o1 n1] C1] eqn:Eg.
    destruct (tseitin_aux h n1) as [[o2 n2] C2] eqn:Eh.
    injection Haux as <- <- <-.
    destruct (IHg next o1 n1 C1 a Eg ltac:(lia)) as [a1 [Hagree1 [HC1 Ho1]]].
    destruct (tseitin_aux_bounds g next o1 n1 C1 Eg ltac:(lia))
      as [Hle1 [_ [Hlt1 [Hbelow1 _]]]].
    assert (Hh : formula_eval h a1 = formula_eval h a).
    { apply formula_eval_agree. intros i Hi. apply Hagree1. lia. }
    destruct (IHh n1 o2 n2 C2 a1 Eh ltac:(lia)) as [a2 [Hagree2 [HC2 Ho2]]].
    destruct (tseitin_aux_bounds h n1 o2 n2 C2 Eh ltac:(lia))
      as [Hle2 [_ [Hlt2 [Hbelow2 _]]]].
    set (val := formula_eval g a && formula_eval h a).
    exists (stream_update a2 n2 val).
    assert (Hkeep : forall i, i < n2 -> stream_update a2 n2 val i = a2 i).
    { intros i Hi. unfold stream_update.
      destruct (Nat.eqb_spec i n2); [lia | reflexivity]. }
    assert (Hnew : stream_update a2 n2 val n2 = val).
    { unfold stream_update. rewrite Nat.eqb_refl. reflexivity. }
    assert (Ho1' : stream_update a2 n2 val o1 = formula_eval g a).
    { rewrite Hkeep by lia. rewrite Hagree2 by lia. exact Ho1. }
    assert (Ho2' : stream_update a2 n2 val o2 = formula_eval h a).
    { rewrite Hkeep by lia. rewrite Ho2. exact Hh. }
    assert (HC1' : cnf_eval (stream_update a2 n2 val) C1 = true).
    { rewrite (cnf_eval_agree C1 n1 _ a1 Hbelow1); [exact HC1 |].
      intros i Hi. rewrite Hkeep by lia. apply Hagree2. exact Hi. }
    assert (HC2' : cnf_eval (stream_update a2 n2 val) C2 = true).
    { rewrite (cnf_eval_agree C2 n2 _ a2 Hbelow2); [exact HC2 | exact Hkeep]. }
    split.
    + intros i Hi.
      rewrite Hkeep by lia. rewrite Hagree2 by lia. apply Hagree1. exact Hi.
    + split.
      * unfold cnf_eval in HC1', HC2' |- *.
        simpl.
        rewrite forallb_app, HC1', HC2'.
        rewrite Hnew, Ho1', Ho2'.
        unfold val.
        destruct (formula_eval g a), (formula_eval h a); reflexivity.
      * rewrite Hnew. reflexivity.
  - destruct (tseitin_aux g next) as [[o1 n1] C1] eqn:Eg.
    destruct (tseitin_aux h n1) as [[o2 n2] C2] eqn:Eh.
    injection Haux as <- <- <-.
    destruct (IHg next o1 n1 C1 a Eg ltac:(lia)) as [a1 [Hagree1 [HC1 Ho1]]].
    destruct (tseitin_aux_bounds g next o1 n1 C1 Eg ltac:(lia))
      as [Hle1 [_ [Hlt1 [Hbelow1 _]]]].
    assert (Hh : formula_eval h a1 = formula_eval h a).
    { apply formula_eval_agree. intros i Hi. apply Hagree1. lia. }
    destruct (IHh n1 o2 n2 C2 a1 Eh ltac:(lia)) as [a2 [Hagree2 [HC2 Ho2]]].
    destruct (tseitin_aux_bounds h n1 o2 n2 C2 Eh ltac:(lia))
      as [Hle2 [_ [Hlt2 [Hbelow2 _]]]].
    set (val := formula_eval g a || formula_eval h a).
    exists (stream_update a2 n2 val).
    assert (Hkeep : forall i, i < n2 -> stream_update a2 n2 val i = a2 i).
    { intros i Hi. unfold stream_update.
      destruct (Nat.eqb_spec i n2); [lia | reflexivity]. }
    assert (Hnew : stream_update a2 n2 val n2 = val).
    { unfold stream_update. rewrite Nat.eqb_refl. reflexivity. }
    assert (Ho1' : stream_update a2 n2 val o1 = formula_eval g a).
    { rewrite Hkeep by lia. rewrite Hagree2 by lia. exact Ho1. }
    assert (Ho2' : stream_update a2 n2 val o2 = formula_eval h a).
    { rewrite Hkeep by lia. rewrite Ho2. exact Hh. }
    assert (HC1' : cnf_eval (stream_update a2 n2 val) C1 = true).
    { rewrite (cnf_eval_agree C1 n1 _ a1 Hbelow1); [exact HC1 |].
      intros i Hi. rewrite Hkeep by lia. apply Hagree2. exact Hi. }
    assert (HC2' : cnf_eval (stream_update a2 n2 val) C2 = true).
    { rewrite (cnf_eval_agree C2 n2 _ a2 Hbelow2); [exact HC2 | exact Hkeep]. }
    split.
    + intros i Hi.
      rewrite Hkeep by lia. rewrite Hagree2 by lia. apply Hagree1. exact Hi.
    + split.
      * unfold cnf_eval in HC1', HC2' |- *.
        simpl.
        rewrite forallb_app, HC1', HC2'.
        rewrite Hnew, Ho1', Ho2'.
        unfold val.
        destruct (formula_eval g a), (formula_eval h a); reflexivity.
      * rewrite Hnew. reflexivity.
Qed.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               TSEITIN THEOREM                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          Tseitin: the CNF is equisatisfiable with the formula, has
│          at most `3 |f| + 1` clauses of width at most three, and
│          uses at most `|f|` fresh variables.
│
*)

Theorem tseitin_correct :
  forall f,
    (Satisfiable f <-> CNFSatisfiable (tseitin f)) /\
    length (tseitin f) <= 3 * formula_size f + 1 /\
    (forall c, In c (tseitin f) -> length c <= 3) /\
    CNFBelow (tseitin f) (formula_var_bound f + formula_size f).
Proof.
  intro f.
  unfold tseitin.
  destruct (tseitin_aux f (formula_var_bound f)) as [[o n'] C] eqn:Ef.
  destruct (tseitin_aux_bounds f _ o n' C Ef (le_n _))
    as [Hle [Hsize [Ho [Hbelow [Hlen Hwidth]]]]].
  split.
  - split.
    + intros [a Ha].
      destruct (tseitin_aux_complete f _ o n' C a Ef (le_n _))
        as [a' [_ [HC Ho']]].
      exists a'.
      unfold cnf_eval. simpl.
      fold (cnf_eval a' C).
      rewrite HC, Ho', Ha.
      reflexivity.
    + intros [a Ha].
      unfold cnf_eval in Ha. simpl in Ha.
      fold (cnf_eval a C) in Ha.
      split_andb.
      exists a.
      rewrite <- (tseitin_aux_sound f _ o n' C a Ef ltac:(assumption)).
      destruct (a o); [reflexivity | discriminate].
  - split; [simpl; lia |].
    split.
    + intros c [Hc | Hc]; [subst; simpl; lia | exact (Hwidth c Hc)].
    + intros c [Hc | Hc] l Hl.
      * subst. destruct Hl as [Hl | []]. subst. simpl. lia.
      * pose proof (Hbelow c Hc l Hl). lia.
Qed.

(*
│
│          Clause-level specialization: relative to every oracle, a
│          circuit verifier accepts its own diagonal claim exactly
│          when the Tseitin CNF of `psi_v` is satisfiable, and that
│          CNF has at most `lvl v + 1` clauses.
│
*)

Corollary clause_level_specialization :
  forall O v,
    CircuitVerifier v ->
    (ConcreteAccepted O v <-> CNFSatisfiable (tseitin (specialized_formula v))) /\
    length (tseitin (specialized_formula v)) <= 3 * term_size v + 1 /\
    length (tseitin (specialized_formula v)) <= term_level v + 1.
Proof.
  intros O v Hcircuit.
  destruct (specialization O v Hcircuit) as [Hacc [Hsize Hlevel]].
  destruct (tseitin_correct (specialized_formula v)) as [Hequi [Hlen _]].
  split; [rewrite Hacc; exact Hequi |].
  split; lia.
Qed.
