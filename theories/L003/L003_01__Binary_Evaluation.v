(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Binary evaluation layer for L003. We derive the constructive consequences of exact binary totality: uniqueness separates verdicts `0` and `1`, while existence makes each verdict equivalent to the negation of the other.]]@*)

(*@head.end@*)

From L003 Require Export L003_00_Premises.

(*@section@[[UNIQUENESS AND BINARY EXHAUSTION]]@*)

(*@inline@[[Any two binary outputs produced by the same total evaluator on the same query must coincide.]]@*)

Theorem tot2_output_unique :
  forall (out : OutputRelation)
         (h : Code)
         (q : Input)
         (b0 b1 : Output),
    Tot2 out h ->
    BinaryOutput b0 ->
    BinaryOutput b1 ->
    out h q b0 ->
    out h q b1 ->
    b0 = b1.
Proof.
  intros out h q b0 b1 Htotal Hb0 Hb1 Hout0 Hout1.
  destruct (Htotal q) as [b [[Hb Hout] Hunique]].
  transitivity b.
  - symmetry. apply Hunique. split; assumption.
  - apply Hunique. split; assumption.
Qed.

(*@inline@[[Every query to a `Tot2` evaluator produces one of the two distinguished verdicts.]]@*)

(*@unicodemath@[[Tot2(out,h) ⇒ ∀ q, ∃ b, (b = 0 ∨ b = 1) ∧ out(h,q,b).]]@*)

Theorem tot2_has_zero_or_one :
  forall (out : OutputRelation)
         (h : Code)
         (q : Input),
    Tot2 out h ->
    exists b : Output,
      (b = 0 \/ b = 1) /\ out h q b.
Proof.
  intros out h q Htotal.
  destruct (Htotal q) as [b [[Hb Hout] Hunique]].
  exists b.
  split.
  - unfold BinaryOutput in Hb. lia.
  - exact Hout.
Qed.

(*@section@[[CONSTRUCTIVE BINARY COMPLEMENTS]]@*)

(*@inline@[[For a total binary evaluator, producing verdict `0` is equivalent to not producing verdict `1`.]]@*)

(*@unicodemath@[[Tot2(out,h) ⇒ (out(h,q,0) ⇔ ¬ out(h,q,1)).]]@*)

Theorem tot2_zero_iff_not_one :
  forall (out : OutputRelation)
         (h : Code)
         (q : Input),
    Tot2 out h ->
    (out h q 0 <-> ~ out h q 1).
Proof.
  intros out h q Htotal.
  split.
  - intros Hzero Hone.
    assert (Heq : 0 = 1).
    {
      eapply (tot2_output_unique out h q 0 1).
      - exact Htotal.
      - unfold BinaryOutput. lia.
      - unfold BinaryOutput. lia.
      - exact Hzero.
      - exact Hone.
    }
    discriminate.
  - intro Hnot_one.
    destruct (tot2_has_zero_or_one out h q Htotal)
      as [b [[Hb | Hb] Hout]].
    + subst b. exact Hout.
    + subst b. exfalso. exact (Hnot_one Hout).
Qed.

(*@inline@[[Symmetrically, producing verdict `1` is equivalent to not producing verdict `0`.]]@*)

(*@unicodemath@[[Tot2(out,h) ⇒ (out(h,q,1) ⇔ ¬ out(h,q,0)).]]@*)

Theorem tot2_one_iff_not_zero :
  forall (out : OutputRelation)
         (h : Code)
         (q : Input),
    Tot2 out h ->
    (out h q 1 <-> ~ out h q 0).
Proof.
  intros out h q Htotal.
  split.
  - intros Hone Hzero.
    assert (Heq : 1 = 0).
    {
      eapply (tot2_output_unique out h q 1 0).
      - exact Htotal.
      - unfold BinaryOutput. lia.
      - unfold BinaryOutput. lia.
      - exact Hone.
      - exact Hzero.
    }
    discriminate.
  - intro Hnot_zero.
    destruct (tot2_has_zero_or_one out h q Htotal)
      as [b [[Hb | Hb] Hout]].
    + subst b. exfalso. exact (Hnot_zero Hout).
    + subst b. exact Hout.
Qed.
