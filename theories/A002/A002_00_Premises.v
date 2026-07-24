(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Arithmetic substrate for A002/CARRYLESS SEQUENT. We fix the shared standard-library and A001 carryless-pairing environment, then define result conventions, canonical A001 destructuring, tagged lists, and formula syntax used by the executable verifier layers.]]@*)

(*@doc.pl@[[The verifier surface of A002 is deliberately arithmetic: every structured value and checking result is a natural number interpreted through the certified A001 pairing function. This consolidated base contains the effective data representation and its elementary constructor facts, but no proof search or semantic verification.]]@*)

(*@doc.pl@[[A001 decoding is total, so decoding alone is never treated as evidence that a number is structured. Every destructor below is paired with a canonicity test requiring the input to be a fixed point of decode followed by encode. The later normalization layer replaces these rapidly growing arithmetic containers with inductive data after this representation boundary has been made explicit.]]@*)

(*@head.end@*)

From Stdlib Require Export Arith PeanoNat Bool Lia List Ring ZArith Extraction.
From A001 Require Export A001_95_API.
Export ListNotations.
Global Open Scope list_scope.

(*@section@[[ARITHMETIC RESULT CONVENTIONS]]@*)

(*@inline@[[A002 returns A001-coded status/payload pairs. Status `0` means rejection and status `1` means acceptance.]]@*)

(*@unicodemath@[[result = encode(status,payload),   status ∈ {0,1}.]]@*)

Definition STATUS_REJECT : nat := 0.
Definition STATUS_ACCEPT : nat := 1.

(*@inline@[[`accept payload` packages a successful arithmetic result. The payload is always an explicit natural-number certificate or local certificate component.]]@*)

(*@unicodemath@[[accept(p) ≔ encode(1,p).]]@*)

Definition accept (payload : nat) : nat :=
  encode STATUS_ACCEPT payload.

(*@inline@[[`code_error stage index detail` records the first local failure seen by a checker. The stage identifies the verifier layer, the index identifies the global or line-local position, and the detail identifies the concrete failure.]]@*)

(*@unicodemath@[[code_error(s,i,d) ≔ encode(s,encode(i,d)).]]@*)

Definition code_error (stage index detail : nat) : nat :=
  encode stage (encode index detail).

(*@inline@[[`reject` packages an arithmetic failure result. No rejection branch returns an uncoded diagnostic.]]@*)

(*@unicodemath@[[reject(s,i,d) ≔ encode(0,code_error(s,i,d)).]]@*)

Definition reject (stage index detail : nat) : nat :=
  encode STATUS_REJECT (code_error stage index detail).

(*@section@[[ERROR STAGES]]@*)

(*@inline@[[The stage constants partition errors by verifier layer. Global errors use index `0`; line-local errors use the current line index.]]@*)

Definition STAGE_DERIVATION_HEADER : nat := 0.
Definition STAGE_LIST_STRUCTURE : nat := 1.
Definition STAGE_LINE : nat := 2.
Definition STAGE_TAG : nat := 3.
Definition STAGE_FORMULA : nat := 4.
Definition STAGE_RULE : nat := 5.
Definition STAGE_CONCLUSION : nat := 6.

(*@section@[[COMMON ERROR DETAILS]]@*)

(*@inline@[[Common structural errors are shared by parsers, list destructors, and the main verifier.]]@*)

Definition ERR_NONCANONICAL_DERIVATION : nat := 0.
Definition ERR_BAD_DERIVATION_LENGTH : nat := 1.
Definition ERR_EMPTY_DERIVATION : nat := 2.
Definition ERR_BAD_CONCLUSION : nat := 3.
Definition ERR_FUEL_EXHAUSTED : nat := 4.
Definition ERR_NONCANONICAL_NODE : nat := 5.
Definition ERR_BAD_TAG : nat := 6.
Definition ERR_BAD_LIST_TAG : nat := 7.
Definition ERR_INDEX_OUT_OF_RANGE : nat := 10.
Definition ERR_NONCANONICAL_LINE : nat := 11.
Definition ERR_UNKNOWN_RULE : nat := 13.

(*@inline@[[`ERR_NORMALIZED_STEP_REJECTED` is reserved for a well-formed normalized line whose K, S, or MP obligation fails. Its accompanying index is the first failing line, unlike arithmetic normalization failures which are reported at their own input stage.]]@*)

Definition ERR_NORMALIZED_STEP_REJECTED : nat := 14.

(*@inline@[[Formula-parser errors distinguish non-canonical inputs, non-implication nodes, and malformed implication payloads.]]@*)

Definition ERR_NONCANONICAL_FORMULA : nat := 20.
Definition ERR_BAD_FORMULA_TAG : nat := 21.
Definition ERR_BAD_IMP_PAYLOAD : nat := 23.
Definition ERR_NOT_IMP : nat := 24.

(*@inline@[[K-axiom errors identify the first failed syntactic obligation in the shape `A -> (B -> A)`.]]@*)

Definition ERR_AXK_NOT_IMP_1 : nat := 40.
Definition ERR_AXK_NOT_IMP_2 : nat := 41.
Definition ERR_AXK_A_MISMATCH : nat := 42.
Definition ERR_AXK_BAD_A : nat := 43.
Definition ERR_AXK_BAD_B : nat := 44.

(*@inline@[[S-axiom errors identify the first failed syntactic obligation in the shape `(A -> (B -> C)) -> ((A -> B) -> (A -> C))`.]]@*)

Definition ERR_AXS_NOT_IMP_1 : nat := 60.
Definition ERR_AXS_NOT_IMP_2 : nat := 61.
Definition ERR_AXS_NOT_IMP_3 : nat := 62.
Definition ERR_AXS_NOT_IMP_4 : nat := 63.
Definition ERR_AXS_NOT_IMP_5 : nat := 64.
Definition ERR_AXS_NOT_IMP_6 : nat := 65.
Definition ERR_AXS_A_MISMATCH_LEFT : nat := 66.
Definition ERR_AXS_A_MISMATCH_RIGHT : nat := 67.
Definition ERR_AXS_B_MISMATCH : nat := 68.
Definition ERR_AXS_C_MISMATCH : nat := 69.
Definition ERR_AXS_BAD_A : nat := 70.
Definition ERR_AXS_BAD_B : nat := 71.
Definition ERR_AXS_BAD_C : nat := 72.

(*@inline@[[Modus-ponens errors identify malformed citations, malformed cited lines, and mismatch against the cited implication.]]@*)

Definition ERR_MP_P_NOT_LT_J : nat := 92.
Definition ERR_MP_Q_NOT_LT_J : nat := 93.
Definition ERR_MP_BAD_LINE_J : nat := 94.
Definition ERR_MP_BAD_LINE_P : nat := 95.
Definition ERR_MP_BAD_LINE_Q : nat := 96.
Definition ERR_MP_Q_NOT_IMP : nat := 97.
Definition ERR_MP_ANTECEDENT_MISMATCH : nat := 98.
Definition ERR_MP_CONSEQUENT_MISMATCH : nat := 99.

(*@section@[[PUBLIC SHAPE TYPES]]@*)

(*@inline@[[The exported verifier consumes a derivation code and a target formula code, and returns an A001-coded arithmetic result.]]@*)

Definition verifier_t : Type := nat -> nat -> nat.

(*@inline@[[The standalone certificate checker consumes a derivation code, a target formula code, and a certificate payload, and returns an executable Boolean.]]@*)

Definition cert_checker_t : Type := nat -> nat -> nat -> bool.

(*@section@[[A001 CANONICAL DESTRUCTURING]]@*)

(*@inline@[[`fst001` is the left projection exposed by the certified A001 decoder. It is a total arithmetic observation, not by itself a proof that `c` is a genuine pair code.]]@*)

Definition fst001 (c : nat) : nat :=
  fst (decode c).

(*@inline@[[`snd001` is the corresponding right projection. Structured consumers must establish `canonical001b c = true` before interpreting either projection.]]@*)

Definition snd001 (c : nat) : nat :=
  snd (decode c).

(*@inline@[[`recode001` sends an arbitrary number to the canonical A001 code of the pair visible through total decoding. It is the normalization map whose fixed points constitute the accepted arithmetic representation.]]@*)

(*@unicodemath@[[recode001(c) ≔ encode(π₁(decode(c)), π₂(decode(c))).]]@*)

Definition recode001 (c : nat) : nat :=
  encode (fst001 c) (snd001 c).

(*@inline@[[`canonical001b` is the Boolean representation guard. It distinguishes actual A001 image points from arbitrary naturals that the total decoder would otherwise silently normalize.]]@*)

(*@unicodemath@[[canonical001b(c) = true ⇔ recode001(c) = c.]]@*)

Definition canonical001b (c : nat) : bool :=
  Nat.eqb (recode001 c) c.

(*@inline@[[`is_pair001b c a b` combines the fixed-point guard with exact equality of both decoded coordinates. It is the strongest local test used for constructor-specific nodes such as the unique nil node.]]@*)

(*@unicodemath@[[is_pair001b(c,a,b) = canonical001b(c) ∧? (fst001(c)=?a) ∧? (snd001(c)=?b).]]@*)

Definition is_pair001b (c a b : nat) : bool :=
  canonical001b c
  && Nat.eqb (fst001 c) a
  && Nat.eqb (snd001 c) b.

(*@inline@[[The left projection law transports A001's certified roundtrip theorem to the local wrapper vocabulary.]]@*)

Lemma fst001_encode :
  forall a b, fst001 (encode a b) = a.
Proof.
  intros a b.
  unfold fst001.
  rewrite decode_encode.
  reflexivity.
Qed.

(*@inline@[[The right projection law is the second coordinate of the same certified A001 roundtrip.]]@*)

Lemma snd001_encode :
  forall a b, snd001 (encode a b) = b.
Proof.
  intros a b.
  unfold snd001.
  rewrite decode_encode.
  reflexivity.
Qed.

(*@inline@[[Every value constructed with `encode` is a fixed point of `recode001`, hence passes the canonical representation guard.]]@*)

Lemma canonical001b_encode :
  forall a b, canonical001b (encode a b) = true.
Proof.
  intros a b.
  unfold canonical001b, recode001.
  rewrite fst001_encode.
  rewrite snd001_encode.
  apply Nat.eqb_refl.
Qed.

(*@inline@[[Freshly encoded coordinates pass the combined canonical-and-projection test exactly.]]@*)

Lemma is_pair001b_encode :
  forall a b, is_pair001b (encode a b) a b = true.
Proof.
  intros a b.
  unfold is_pair001b.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*@inline@[[A successful Boolean canonicity check reflects to the propositional fixed-point equation required by later representation proofs.]]@*)

Lemma canonical001b_eq :
  forall c,
    canonical001b c = true ->
    recode001 c = c.
Proof.
  intros c Hc.
  unfold canonical001b in Hc.
  apply Nat.eqb_eq.
  exact Hc.
Qed.

(*@inline@[[Successful exact pair recognition reflects all three obligations: outer canonicity and equality of both exposed coordinates.]]@*)

Lemma is_pair001b_sound :
  forall c a b,
    is_pair001b c a b = true ->
    canonical001b c = true /\
    fst001 c = a /\
    snd001 c = b.
Proof.
  intros c a b Hpair.
  unfold is_pair001b in Hpair.
  repeat rewrite Bool.andb_true_iff in Hpair.
  destruct Hpair as [[Hcanon Hfst] Hsnd].
  repeat split.
  - exact Hcanon.
  - apply Nat.eqb_eq. exact Hfst.
  - apply Nat.eqb_eq. exact Hsnd.
Qed.

(*@section@[[TAGGED LISTS]]@*)

(*@inline@[[Arithmetic lists use disjoint outer tags: `0` for nil and `1` for cons. The cons payload is itself a canonical A001 pair containing head and tail codes.]]@*)

Definition TAG_NIL : nat := 0.
Definition TAG_CONS : nat := 1.

(*@inline@[[`code_nil` is the unique canonical empty-list node; fixing its payload to zero rules out alternate encodings of nil.]]@*)

(*@unicodemath@[[code_nil ≔ encode(0,0).]]@*)

Definition code_nil : nat :=
  encode TAG_NIL 0.

(*@inline@[[`code_cons h t` nests the head/tail pair beneath the cons tag. At this raw constructor boundary `t` is merely a number; bounded list recognition validates the chain separately.]]@*)

(*@unicodemath@[[code_cons(h,t) ≔ encode(1, encode(h,t)).]]@*)

Definition code_cons (h t : nat) : nat :=
  encode TAG_CONS (encode h t).

(*@inline@[[A derivation header records a claimed list length and the arithmetic code of its line body. Exact agreement between the claim and body is checked before verification begins.]]@*)

(*@unicodemath@[[code_derivation(n,body) ≔ encode(n,body).]]@*)

Definition code_derivation (n body : nat) : nat :=
  encode n body.

(*@inline@[[`list_tag` reads the outer constructor tag. Its value is interpreted only on branches where the enclosing node has passed `canonical001b`.]]@*)

Definition list_tag (body : nat) : nat :=
  fst001 body.

(*@inline@[[`list_payload` reads the outer constructor payload under the same guarded-destructuring discipline.]]@*)

Definition list_payload (body : nat) : nat :=
  snd001 body.

(*@inline@[[Nil recognition requires the complete canonical pair `(TAG_NIL,0)`, not merely a decoded zero tag.]]@*)

Definition is_nil_nodeb (body : nat) : bool :=
  is_pair001b body TAG_NIL 0.

(*@inline@[[Cons recognition checks only the canonical outer node and its tag. The nested head/tail payload is checked independently by `cons_payloadb`.]]@*)

Definition is_cons_nodeb (body : nat) : bool :=
  canonical001b body && Nat.eqb (list_tag body) TAG_CONS.

(*@inline@[[A cons payload is admissible exactly when it is itself a canonical A001 pair, ensuring that head and tail projections are not taken from a non-image code.]]@*)

Definition cons_payloadb (payload : nat) : bool :=
  canonical001b payload.

(*@inline@[[`list_exact_lengthb n body` consumes exactly `n` canonical cons nodes and then requires the unique nil node. The claimed derivation length therefore supplies both the traversal bound and the exact-shape specification.]]@*)

(*@unicodemath@[[list_exact_lengthb(0,body)=is_nil_nodeb(body).]]@*)
(*@unicodemath@[[list_exact_lengthb(n+1,cons(h,t))=list_exact_lengthb(n,t).]]@*)

Fixpoint list_exact_lengthb (n body : nat) : bool :=
  match n with
  | 0 => is_nil_nodeb body
  | S n' =>
      if canonical001b body then
        if Nat.eqb (list_tag body) TAG_CONS then
          let payload := list_payload body in
          if cons_payloadb payload then
            list_exact_lengthb n' (snd001 payload)
          else false
        else false
      else false
  end.

(*@inline@[[`nth_list_fuel fuel body i` performs guarded zero-based indexing. Every recursive step consumes one unit of fuel and one cons cell; all structural failures are returned through the uniform arithmetic rejection channel.]]@*)

Fixpoint nth_list_fuel (fuel body i : nat) : nat :=
  match fuel with
  | 0 => reject STAGE_LIST_STRUCTURE i ERR_FUEL_EXHAUSTED
  | S fuel' =>
      if canonical001b body then
        let tag := list_tag body in
        let payload := list_payload body in
        if Nat.eqb tag TAG_CONS then
          if cons_payloadb payload then
            let h := fst001 payload in
            let t := snd001 payload in
            if Nat.eqb i 0 then
              accept h
            else
              nth_list_fuel fuel' t (Nat.pred i)
          else
            reject STAGE_LIST_STRUCTURE i ERR_NONCANONICAL_NODE
        else if Nat.eqb tag TAG_NIL then
          reject STAGE_LIST_STRUCTURE i ERR_INDEX_OUT_OF_RANGE
        else
          reject STAGE_LIST_STRUCTURE i ERR_BAD_LIST_TAG
      else
        reject STAGE_LIST_STRUCTURE i ERR_NONCANONICAL_NODE
  end.

(*@inline@[[`nth_list` supplies the tight structural budget `S i`: locating index `i` requires inspection of at most `i+1` cons nodes.]]@*)

Definition nth_list (body i : nat) : nat :=
  nth_list_fuel (S i) body i.

(*@inline@[[The canonical empty-list constructor satisfies the nil recognizer.]]@*)

Lemma is_nil_nodeb_code_nil :
  is_nil_nodeb code_nil = true.
Proof.
  unfold is_nil_nodeb, code_nil.
  apply is_pair001b_encode.
Qed.

(*@inline@[[Every constructed cons cell satisfies the canonical outer-node and tag test, independently of whether its tail later forms a complete list.]]@*)

Lemma is_cons_nodeb_code_cons :
  forall h t, is_cons_nodeb (code_cons h t) = true.
Proof.
  intros h t.
  unfold is_cons_nodeb, code_cons, list_tag.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  apply Nat.eqb_refl.
Qed.

(*@inline@[[The unique nil constructor is recognized as a list of exact length zero.]]@*)

Lemma list_exact_lengthb_code_nil :
  list_exact_lengthb 0 code_nil = true.
Proof.
  cbn [list_exact_lengthb].
  apply is_nil_nodeb_code_nil.
Qed.

(*@inline@[[Prepending a constructed cons cell transports exact-length recognition from `n` to `S n`.]]@*)

Lemma list_exact_lengthb_code_cons :
  forall n h t,
    list_exact_lengthb n t = true ->
    list_exact_lengthb (S n) (code_cons h t) = true.
Proof.
  intros n h t Hlen.
  cbn [list_exact_lengthb].
  unfold code_cons, list_tag, list_payload, cons_payloadb.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite Nat.eqb_refl.
  rewrite canonical001b_encode.
  rewrite snd001_encode.
  exact Hlen.
Qed.

(*@inline@[[Index zero of a constructed cons cell returns its head whenever at least one unit of fuel is available.]]@*)

Lemma nth_list_fuel_code_cons_zero :
  forall fuel h t,
    nth_list_fuel (S fuel) (code_cons h t) 0 = accept h.
Proof.
  intros fuel h t.
  cbn [nth_list_fuel].
  unfold code_cons, list_tag, list_payload, cons_payloadb.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite Nat.eqb_refl.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  reflexivity.
Qed.

(*@inline@[[Successor indexing through a constructed cons cell removes that cell, decrements the requested index, and continues with the remaining fuel.]]@*)

Lemma nth_list_fuel_code_cons_succ :
  forall fuel h t i,
    nth_list_fuel (S fuel) (code_cons h t) (S i) =
    nth_list_fuel fuel t i.
Proof.
  intros fuel h t i.
  cbn [nth_list_fuel].
  unfold code_cons, list_tag, list_payload, cons_payloadb.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite canonical001b_encode.
  rewrite Nat.eqb_refl.
  rewrite snd001_encode.
  reflexivity.
Qed.

(*@section@[[FORMULA SYNTAX]]@*)

(*@inline@[[The arithmetic object language has two disjoint outer tags: variables carry tag `0`, while implications carry tag `1` and a nested antecedent/consequent pair.]]@*)

Definition TAG_VAR : nat := 0.
Definition TAG_IMP : nat := 1.

(*@inline@[[`code_var i` represents the object-language variable with numerical index `i`. Every natural payload is a valid variable name.]]@*)

(*@unicodemath@[[code_var(i) ≔ encode(0,i).]]@*)

Definition code_var (i : nat) : nat :=
  encode TAG_VAR i.

(*@inline@[[`code_imp a b` represents implication by storing the canonical pair `(a,b)` beneath the implication tag. Well-formedness of the two component codes is a separate recursive obligation.]]@*)

(*@unicodemath@[[code_imp(a,b) ≔ encode(1, encode(a,b)).]]@*)

Definition code_imp (a b : nat) : nat :=
  encode TAG_IMP (encode a b).

(*@inline@[[`formula_tag` reads the outer formula constructor exposed by A001 decoding; callers interpret it only after checking outer canonicity.]]@*)

Definition formula_tag (c : nat) : nat :=
  fst001 c.

(*@inline@[[`formula_payload` reads the variable index or implication payload selected by the guarded outer tag.]]@*)

Definition formula_payload (c : nat) : nat :=
  snd001 c.

(*@inline@[[`is_formula_fuel fuel c` is bounded structural recognition for arithmetic formula trees. Variables terminate immediately; implications consume one unit of fuel and require a canonical component pair whose two children both normalize recursively.]]@*)

(*@unicodemath@[[is_formula_fuel(S f, code_var(i)) = true.]]@*)
(*@unicodemath@[[is_formula_fuel(S f, code_imp(a,b)) = is_formula_fuel(f,a) ∧? is_formula_fuel(f,b).]]@*)

Fixpoint is_formula_fuel (fuel c : nat) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      if canonical001b c then
        let tag := formula_tag c in
        let payload := formula_payload c in
        if Nat.eqb tag TAG_VAR then
          true
        else if Nat.eqb tag TAG_IMP then
          if canonical001b payload then
            is_formula_fuel fuel' (fst001 payload)
            && is_formula_fuel fuel' (snd001 payload)
          else false
        else false
      else false
  end.

(*@inline@[[`formula_bound c = S c` supplies a total arithmetic fuel budget without requiring a separate size field in the encoded syntax. The later inductive normalization layer avoids computing with this large numerical bound.]]@*)

Definition formula_bound (c : nat) : nat :=
  S c.

(*@inline@[[`is_formula` is the total arithmetic recognizer obtained by instantiating the bounded descent with `formula_bound`.]]@*)

Definition is_formula (c : nat) : bool :=
  is_formula_fuel (formula_bound c) c.

(*@inline@[[`parse_imp phi` performs only the guarded outer-shape inversion needed by rule checkers. On success it returns the canonical antecedent/consequent payload; it does not recursively certify the two formulas.]]@*)

(*@unicodemath@[[parse_imp(code_imp(a,b)) = accept(encode(a,b)).]]@*)

Definition parse_imp (phi : nat) : nat :=
  if canonical001b phi then
    let tag := formula_tag phi in
    let payload := formula_payload phi in
    if Nat.eqb tag TAG_IMP then
      if canonical001b payload then
        accept payload
      else
        reject STAGE_FORMULA 0 ERR_BAD_IMP_PAYLOAD
    else
      reject STAGE_FORMULA 0 ERR_NOT_IMP
  else
    reject STAGE_FORMULA 0 ERR_NONCANONICAL_FORMULA.

(*@inline@[[`parse_formula_diagnostic` lifts total formula recognition into the uniform arithmetic result convention, returning the original code on success and a formula-stage diagnostic on failure.]]@*)

Definition parse_formula_diagnostic (phi : nat) : nat :=
  if is_formula phi then
    accept phi
  else
    reject STAGE_FORMULA 0 ERR_BAD_FORMULA_TAG.

(*@inline@[[Every constructed variable is accepted by bounded formula recognition for any positive fuel budget.]]@*)

Lemma is_formula_fuel_var :
  forall fuel i,
    0 < fuel ->
    is_formula_fuel fuel (code_var i) = true.
Proof.
  intros fuel i Hfuel.
  destruct fuel as [|fuel']; [lia|].
  cbn [is_formula_fuel].
  unfold code_var, formula_tag, formula_payload.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*@inline@[[The total wrapper recognizes every constructed variable by specializing the positive-fuel lemma to `formula_bound`.]]@*)

Lemma is_formula_var :
  forall i, is_formula (code_var i) = true.
Proof.
  intro i.
  unfold is_formula, formula_bound.
  apply is_formula_fuel_var.
  lia.
Qed.

(*@inline@[[If both children are recognized with fuel `f`, their implication is recognized with one additional step. This is the structural constructor rule used when relating arithmetic syntax to inductive normal forms.]]@*)

Lemma is_formula_fuel_imp :
  forall fuel a b,
    is_formula_fuel fuel a = true ->
    is_formula_fuel fuel b = true ->
    is_formula_fuel (S fuel) (code_imp a b) = true.
Proof.
  intros fuel a b Ha Hb.
  cbn [is_formula_fuel].
  unfold code_imp, formula_tag, formula_payload.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  cbn [TAG_VAR TAG_IMP].
  rewrite Nat.eqb_refl.
  rewrite canonical001b_encode.
  apply Bool.andb_true_iff.
  split.
  - rewrite fst001_encode. exact Ha.
  - rewrite snd001_encode. exact Hb.
Qed.

(*@inline@[[Guarded implication parsing is a left inverse of the arithmetic implication constructor: the original canonical child pair is recovered exactly.]]@*)

Lemma parse_imp_code_imp :
  forall a b, parse_imp (code_imp a b) = accept (encode a b).
Proof.
  intros a b.
  unfold parse_imp, code_imp, formula_tag, formula_payload.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  cbn [TAG_VAR TAG_IMP].
  rewrite Nat.eqb_refl.
  rewrite canonical001b_encode.
  reflexivity.
Qed.
