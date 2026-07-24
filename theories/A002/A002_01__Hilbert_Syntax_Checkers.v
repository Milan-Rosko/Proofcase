(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[Hilbert syntax and checker layer for CARRYLESS SEQUENT. We encode proof lines as A001-canonical pairs of a rule tag and displayed formula, define the fixed K, S, and modus-ponens tags, and implement their total arithmetic checkers.]]@*)

(*@doc.pl@[[Line and tag parsing establishes the arithmetic outer shape before rule-specific checking begins. The K and S checkers validate their complete formula schemas; the MP checker validates earlier citations and syntactic antecedent/consequent alignment. No checker performs proof search or semantic evaluation.]]@*)

(*@doc.pl@[[The executable flow is deliberately staged: canonical line parsing yields a tag/formula pair; canonical tag parsing yields a rule/payload pair; the selected local checker then returns either a rule-specific certificate payload or the first deterministic arithmetic error. The normalization layer consumes this surface but proves schema validity over inductive syntax, avoiding closed computation over the large arithmetic containers.]]@*)

(*@head.end@*)

From A002 Require Export A002_00_Premises.

(*@section@[[LINE CONSTRUCTOR]]@*)

(*@inline@[[A proof line pairs a rule tag code with the formula displayed on that line.]]@*)

(*@unicodemath@[[code_line(tag,φ) ≔ encode(tag,φ).]]@*)

Definition code_line (tag formula : nat) : nat :=
  encode tag formula.

(*@inline@[[`line_tag` reads the rule tag exposed by A001 decoding. It is dispatched as a rule tag only after the enclosing line has passed the canonical A001 test.]]@*)

Definition line_tag (ell : nat) : nat :=
  fst001 ell.

(*@inline@[[`line_formula` reads the displayed formula exposed by A001 decoding. Rule checkers decide whether this number is a well-formed formula of the required syntactic shape.]]@*)

Definition line_formula (ell : nat) : nat :=
  snd001 ell.

(*@section@[[RULE TAGS]]@*)

(*@inline@[[The fixed CARRYLESS SEQUENT rule code for the K axiom schema.]]@*)

Definition RULE_AXK : nat := 0.

(*@inline@[[The fixed CARRYLESS SEQUENT rule code for the S axiom schema.]]@*)

Definition RULE_AXS : nat := 1.

(*@inline@[[The fixed CARRYLESS SEQUENT rule code for modus ponens.]]@*)

Definition RULE_MP : nat := 2.

(*@inline@[[The K-axiom tag has rule code `RULE_AXK` and empty payload `0`.]]@*)

(*@unicodemath@[[tag_axk ≔ encode(0,0).]]@*)

Definition tag_axk : nat :=
  encode RULE_AXK 0.

(*@inline@[[The S-axiom tag has rule code `RULE_AXS` and empty payload `0`.]]@*)

(*@unicodemath@[[tag_axs ≔ encode(1,0).]]@*)

Definition tag_axs : nat :=
  encode RULE_AXS 0.

(*@inline@[[The modus-ponens tag has rule code `RULE_MP` and a canonical A001 pair of cited line indices.]]@*)

(*@unicodemath@[[tag_mp(p,q) ≔ encode(2,encode(p,q)).]]@*)

Definition tag_mp (p q : nat) : nat :=
  encode RULE_MP (encode p q).

(*@section@[[RULE TAG PARSING]]@*)

(*@inline@[[`rule_code` reads the outer rule code exposed by A001 decoding. It is dispatched only after tag canonicity has been checked.]]@*)

Definition rule_code (tag : nat) : nat :=
  fst001 tag.

(*@inline@[[`rule_payload` reads the outer rule payload exposed by A001 decoding. Its expected shape depends on the checked rule code.]]@*)

Definition rule_payload (tag : nat) : nat :=
  snd001 tag.

(*@inline@[[`parse_rule_tag tag` returns `accept (encode rule payload)` when `tag` is one of the three canonical CARRYLESS SEQUENT rule tags.]]@*)

(*@unicodemath@[[parse_rule_tag(tag_axk)=accept(encode(0,0)).]]@*)
(*@unicodemath@[[parse_rule_tag(tag_axs)=accept(encode(1,0)).]]@*)
(*@unicodemath@[[parse_rule_tag(tag_mp(p,q))=accept(encode(2,encode(p,q))).]]@*)

Definition parse_rule_tag (tag : nat) : nat :=
  if canonical001b tag then
    let rule := rule_code tag in
    let payload := rule_payload tag in
    if Nat.eqb rule RULE_AXK then
      if Nat.eqb payload 0 then
        accept (encode RULE_AXK 0)
      else
        reject STAGE_TAG 0 ERR_BAD_TAG
    else if Nat.eqb rule RULE_AXS then
      if Nat.eqb payload 0 then
        accept (encode RULE_AXS 0)
      else
        reject STAGE_TAG 0 ERR_BAD_TAG
    else if Nat.eqb rule RULE_MP then
      if canonical001b payload then
        accept (encode RULE_MP payload)
      else
        reject STAGE_TAG 0 ERR_NONCANONICAL_NODE
    else
      reject STAGE_TAG 0 ERR_UNKNOWN_RULE
  else
    reject STAGE_TAG 0 ERR_BAD_TAG.

(*@section@[[LINE PARSING]]@*)

(*@inline@[[`parse_line ell` returns the canonical tag/formula payload of a line after checking that the line itself is canonical and its tag is a valid CARRYLESS SEQUENT rule tag. If tag parsing fails, the tag parser's encoded diagnostic is carried as the line parser detail.]]@*)

(*@unicodemath@[[parse_rule_tag(tag)=accept(encode(rule,payload))]][[⇒ parse_line(code_line(tag,φ))=accept(encode(tag,φ)).]]@*)

Definition parse_line (ell : nat) : nat :=
  if canonical001b ell then
    let tag := line_tag ell in
    let phi := line_formula ell in
    let parsed_tag := parse_rule_tag tag in
    if Nat.eqb (fst001 parsed_tag) STATUS_ACCEPT then
      accept (encode tag phi)
    else
      reject STAGE_TAG 0 (snd001 parsed_tag)
  else
    reject STAGE_LINE 0 ERR_NONCANONICAL_LINE.

(*@section@[[CONSTRUCTOR FACTS]]@*)

(*@inline@[[The constructed K tag parses as the K rule with empty payload.]]@*)

(*@unicodemath@[[parse_rule_tag(tag_axk)=accept(encode(RULE_AXK,0)).]]@*)

Lemma parse_rule_tag_axk :
  parse_rule_tag tag_axk = accept (encode RULE_AXK 0).
Proof.
  unfold parse_rule_tag, tag_axk, rule_code, rule_payload.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*@inline@[[The constructed S tag parses as the S rule with empty payload.]]@*)

(*@unicodemath@[[parse_rule_tag(tag_axs)=accept(encode(RULE_AXS,0)).]]@*)

Lemma parse_rule_tag_axs :
  parse_rule_tag tag_axs = accept (encode RULE_AXS 0).
Proof.
  unfold parse_rule_tag, tag_axs, rule_code, rule_payload.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  cbn [RULE_AXK RULE_AXS].
  rewrite Nat.eqb_refl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*@inline@[[A constructed modus-ponens tag parses as the MP rule with canonical citation payload.]]@*)

(*@unicodemath@[[parse_rule_tag(tag_mp(p,q))=accept(encode(RULE_MP,encode(p,q))).]]@*)

Lemma parse_rule_tag_mp :
  forall p q,
    parse_rule_tag (tag_mp p q) = accept (encode RULE_MP (encode p q)).
Proof.
  intros p q.
  unfold parse_rule_tag, tag_mp, rule_code, rule_payload.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  cbn [RULE_AXK RULE_AXS RULE_MP].
  rewrite Nat.eqb_refl.
  rewrite canonical001b_encode.
  reflexivity.
Qed.

(*@inline@[[A line built with the K tag parses to its original tag/formula payload.]]@*)

(*@unicodemath@[[parse_line(code_line(tag_axk,φ))=accept(encode(tag_axk,φ)).]]@*)

Lemma parse_line_axk :
  forall phi,
    parse_line (code_line tag_axk phi) = accept (encode tag_axk phi).
Proof.
  intro phi.
  unfold parse_line, code_line, line_tag, line_formula.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite parse_rule_tag_axk.
  unfold accept.
  rewrite fst001_encode.
  cbn [STATUS_ACCEPT].
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*@inline@[[A line built with the S tag parses to its original tag/formula payload.]]@*)

(*@unicodemath@[[parse_line(code_line(tag_axs,φ))=accept(encode(tag_axs,φ)).]]@*)

Lemma parse_line_axs :
  forall phi,
    parse_line (code_line tag_axs phi) = accept (encode tag_axs phi).
Proof.
  intro phi.
  unfold parse_line, code_line, line_tag, line_formula.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite parse_rule_tag_axs.
  unfold accept.
  rewrite fst001_encode.
  cbn [STATUS_ACCEPT].
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*@inline@[[A line built with an MP tag parses to its original tag/formula payload.]]@*)

(*@unicodemath@[[parse_line(code_line(tag_mp(p,q),φ))=accept(encode(tag_mp(p,q),φ)).]]@*)

Lemma parse_line_mp :
  forall p q phi,
    parse_line (code_line (tag_mp p q) phi) =
    accept (encode (tag_mp p q) phi).
Proof.
  intros p q phi.
  unfold parse_line, code_line, line_tag, line_formula.
  rewrite canonical001b_encode.
  rewrite fst001_encode.
  rewrite snd001_encode.
  rewrite parse_rule_tag_mp.
  unfold accept.
  rewrite fst001_encode.
  cbn [STATUS_ACCEPT].
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*@section@[[RESULT PROJECTIONS]]@*)

(*@inline@[[Every parser and local checker in this file uses the common result envelope `encode status payload`. The following projections and Boolean acceptance test keep downstream control flow independent of the rule-specific payload shape.]]@*)

(*@inline@[[`result_status` reads the status component of an A002 arithmetic result. All results built by A002 are canonical A001 pairs.]]@*)

(*@unicodemath@[[result_status(encode(s,p))=s.]]@*)

Definition result_status (r : nat) : nat :=
  fst001 r.

(*@inline@[[`result_payload` reads the payload component of an A002 arithmetic result. Its meaning is determined by the status and by the checker that produced it.]]@*)

(*@unicodemath@[[result_payload(encode(s,p))=p.]]@*)

Definition result_payload (r : nat) : nat :=
  snd001 r.

(*@inline@[[`acceptedb` is the common executable test for a successful checker result.]]@*)

(*@unicodemath@[[acceptedb(r) ≔ (result_status(r)=?STATUS_ACCEPT).]]@*)

Definition acceptedb (r : nat) : bool :=
  Nat.eqb (result_status r) STATUS_ACCEPT.

(*@section@[[PARSED LINE ACCESS]]@*)

(*@inline@[[A successful `parse_line` result carries `encode tag phi`; this projection extracts the displayed formula from that payload.]]@*)

Definition parsed_line_formula (payload : nat) : nat :=
  snd001 payload.

(*@inline@[[`nth_line` fetches a line from a tagged derivation body using fuel bounded by the claimed derivation length.]]@*)

(*@unicodemath@[[nth_line(n,body,i) ≔ nth_list_fuel(n+1,body,i).]]@*)

Definition nth_line (n body i : nat) : nat :=
  nth_list_fuel (S n) body i.

(*@inline@[[`nth_formula` fetches and parses a line, returning the displayed formula when both operations succeed. It is used by later soundness statements as the arithmetic formula-view interface.]]@*)

(*@unicodemath@[[nth_list(body,i)=accept(ℓ) ∧ parse_line(ℓ)=accept(encode(tag,φ))]][[⇒ nth_formula(body,i)=accept(φ).]]@*)

Definition nth_formula (body i : nat) : nat :=
  let fetched := nth_list (body) i in
  if acceptedb fetched then
    let parsed := parse_line (result_payload fetched) in
    if acceptedb parsed then
      accept (parsed_line_formula (result_payload parsed))
    else parsed
  else fetched.

(*@section@[[K AXIOM CHECKER]]@*)

(*@inline@[[`check_axk phi` checks the K schema `A -> (B -> A)` by two implication parses, one equality test, and formula checks for the exposed metavariables.]]@*)

(*@unicodemath@[[is_formula(A)=true ∧ is_formula(B)=true]][[⇒ check_axk(code_imp(A,code_imp(B,A)))=accept(encode(RULE_AXK,encode(A,B))).]]@*)

Definition check_axk (phi : nat) : nat :=
  let outer := parse_imp phi in
  if acceptedb outer then
    let outer_payload := result_payload outer in
    let A := fst001 outer_payload in
    let rhs := snd001 outer_payload in
    let inner := parse_imp rhs in
    if acceptedb inner then
      let inner_payload := result_payload inner in
      let B := fst001 inner_payload in
      let A2 := snd001 inner_payload in
      if Nat.eqb A A2 then
        if is_formula A then
          if is_formula B then
            accept (encode RULE_AXK (encode A B))
          else
            reject STAGE_RULE 0 ERR_AXK_BAD_B
        else
          reject STAGE_RULE 0 ERR_AXK_BAD_A
      else
        reject STAGE_RULE 0 ERR_AXK_A_MISMATCH
    else
      reject STAGE_RULE 0 ERR_AXK_NOT_IMP_2
  else
    reject STAGE_RULE 0 ERR_AXK_NOT_IMP_1.

(*@section@[[S AXIOM CHECKER]]@*)

(*@inline@[[`check_axs phi` checks the S schema `(A -> (B -> C)) -> ((A -> B) -> (A -> C))` by six implication parses, four equality tests, and formula checks for `A`, `B`, and `C`.]]@*)

(*@unicodemath@[[S(A,B,C) ≔ (A → (B → C)) → ((A → B) → (A → C)).]]@*)
(*@unicodemath@[[is_formula(A)=true ∧ is_formula(B)=true ∧ is_formula(C)=true]][[⇒ check_axs(code_imp(code_imp(A,code_imp(B,C)),code_imp(code_imp(A,B),code_imp(A,C))))]][[= accept(encode(RULE_AXS,encode(A,encode(B,C)))).]]@*)

Definition check_axs (phi : nat) : nat :=
  let imp1 := parse_imp phi in
  if acceptedb imp1 then
    let p1 := result_payload imp1 in
    let X := fst001 p1 in
    let Y := snd001 p1 in
    let imp2 := parse_imp X in
    if acceptedb imp2 then
      let p2 := result_payload imp2 in
      let A := fst001 p2 in
      let BC := snd001 p2 in
      let imp3 := parse_imp BC in
      if acceptedb imp3 then
        let p3 := result_payload imp3 in
        let B := fst001 p3 in
        let C := snd001 p3 in
        let imp4 := parse_imp Y in
        if acceptedb imp4 then
          let p4 := result_payload imp4 in
          let AB := fst001 p4 in
          let AC := snd001 p4 in
          let imp5 := parse_imp AB in
          if acceptedb imp5 then
            let p5 := result_payload imp5 in
            let A1 := fst001 p5 in
            let B1 := snd001 p5 in
            let imp6 := parse_imp AC in
            if acceptedb imp6 then
              let p6 := result_payload imp6 in
              let A2 := fst001 p6 in
              let C1 := snd001 p6 in
              if Nat.eqb A A1 then
                if Nat.eqb A A2 then
                  if Nat.eqb B B1 then
                    if Nat.eqb C C1 then
                      if is_formula A then
                        if is_formula B then
                          if is_formula C then
                            accept
                              (encode RULE_AXS
                                (encode A (encode B C)))
                          else
                            reject STAGE_RULE 0 ERR_AXS_BAD_C
                        else
                          reject STAGE_RULE 0 ERR_AXS_BAD_B
                      else
                        reject STAGE_RULE 0 ERR_AXS_BAD_A
                    else
                      reject STAGE_RULE 0 ERR_AXS_C_MISMATCH
                  else
                    reject STAGE_RULE 0 ERR_AXS_B_MISMATCH
                else
                  reject STAGE_RULE 0 ERR_AXS_A_MISMATCH_RIGHT
              else
                reject STAGE_RULE 0 ERR_AXS_A_MISMATCH_LEFT
            else
              reject STAGE_RULE 0 ERR_AXS_NOT_IMP_6
          else
            reject STAGE_RULE 0 ERR_AXS_NOT_IMP_5
        else
          reject STAGE_RULE 0 ERR_AXS_NOT_IMP_4
      else
        reject STAGE_RULE 0 ERR_AXS_NOT_IMP_3
    else
      reject STAGE_RULE 0 ERR_AXS_NOT_IMP_2
  else
    reject STAGE_RULE 0 ERR_AXS_NOT_IMP_1.

(*@section@[[MODUS PONENS CHECKER]]@*)

(*@inline@[[`line_formula_result n body i detail` fetches and parses line `i`; on success it returns the displayed formula, and on failure it returns the supplied MP-specific error detail.]]@*)

(*@unicodemath@[[line_formula_result(n,body,i,d)=accept(φ)]][[⇔ line i is fetchable, canonical, and displays φ.]]@*)

Definition line_formula_result
  (n body i detail : nat)
  : nat :=
  let fetched := nth_line n body i in
  if acceptedb fetched then
    let parsed := parse_line (result_payload fetched) in
    if acceptedb parsed then
      accept (parsed_line_formula (result_payload parsed))
    else
      reject STAGE_RULE i detail
  else
    reject STAGE_RULE i detail.

(*@inline@[[`check_mp n body j p q` checks that line `j` follows from earlier lines `p` and `q`, where line `q` displays an implication whose antecedent is line `p` and consequent is line `j`.]]@*)

(*@unicodemath@[[p<j ∧ q<j<n ∧ body[p]=A ∧ body[q]=(A→B) ∧ body[j]=B]][[⇒ check_mp(n,body,j,p,q)=accept(encode(RULE_MP,encode(p,encode(q,encode(A,B))))).]]@*)

Definition check_mp (n body j p q : nat) : nat :=
  if Nat.ltb p j then
    if Nat.ltb q j then
      if Nat.ltb j n then
        let rj := line_formula_result n body j ERR_MP_BAD_LINE_J in
        if acceptedb rj then
          let phi_j := result_payload rj in
          let rp := line_formula_result n body p ERR_MP_BAD_LINE_P in
          if acceptedb rp then
            let phi_p := result_payload rp in
            let rq := line_formula_result n body q ERR_MP_BAD_LINE_Q in
            if acceptedb rq then
              let phi_q := result_payload rq in
              let parsed_q := parse_imp phi_q in
              if acceptedb parsed_q then
                let q_payload := result_payload parsed_q in
                let A := fst001 q_payload in
                let B := snd001 q_payload in
                if Nat.eqb A phi_p then
                  if Nat.eqb B phi_j then
                    accept
                      (encode RULE_MP
                        (encode p (encode q (encode A B))))
                  else
                    reject STAGE_RULE j ERR_MP_CONSEQUENT_MISMATCH
                else
                  reject STAGE_RULE j ERR_MP_ANTECEDENT_MISMATCH
              else
                reject STAGE_RULE j ERR_MP_Q_NOT_IMP
            else
              reject STAGE_RULE q ERR_MP_BAD_LINE_Q
          else
            reject STAGE_RULE p ERR_MP_BAD_LINE_P
        else
          reject STAGE_RULE j ERR_MP_BAD_LINE_J
      else
        reject STAGE_RULE j ERR_MP_BAD_LINE_J
    else
      reject STAGE_RULE j ERR_MP_Q_NOT_LT_J
  else
    reject STAGE_RULE j ERR_MP_P_NOT_LT_J.

(*@section@[[BASIC RESULT FACTS]]@*)

(*@inline@[[The status projection of an accepted result is the acceptance status.]]@*)

(*@unicodemath@[[acceptedb(accept(p))=true.]]@*)

Lemma acceptedb_accept :
  forall payload, acceptedb (accept payload) = true.
Proof.
  intro payload.
  unfold acceptedb, result_status, accept.
  rewrite fst001_encode.
  apply Nat.eqb_refl.
Qed.

(*@inline@[[The payload projection of an accepted result is the original payload.]]@*)

(*@unicodemath@[[result_payload(accept(p))=p.]]@*)

Lemma result_payload_accept :
  forall payload, result_payload (accept payload) = payload.
Proof.
  intro payload.
  unfold result_payload, accept.
  apply snd001_encode.
Qed.
