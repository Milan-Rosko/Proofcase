(*A002_05__Rule_Checkers_Hilbert.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                  Proofcase / A002_05__Rule_Checkers_Hilbert                  │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Hilbert-rule checker layer for A002-Core. We implement the fixed arithmetic
  checkers for the implicational K axiom, S axiom, and modus ponens over
  A001-coded derivation lists.

  Each checker is total and returns an A001-coded status/payload result.
  Acceptance produces an explicit numerical local certificate payload;
  rejection produces the first local syntactic failure selected by the
  checker. No checker searches for a proof or evaluates a semantic truth
  condition.

*)

From A002 Require Export A002_04__Line_Syntax.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              RESULT PROJECTIONS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `result_status` reads the status component of an A002
│          arithmetic result. All results built by A002 are canonical
│          A001 pairs.
│
*)

Definition result_status (r : nat) : nat :=
  fst001 r.

(*
│
│          `result_payload` reads the payload component of an A002
│          arithmetic result. Its meaning is determined by the status
│          and by the checker that produced it.
│
*)

Definition result_payload (r : nat) : nat :=
  snd001 r.

(*
│
│          `acceptedb` is the common executable test for a successful
│          checker result.
│
*)

Definition acceptedb (r : nat) : bool :=
  Nat.eqb (result_status r) STATUS_ACCEPT.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              PARSED LINE ACCESS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A successful `parse_line` result carries `encode tag phi`;
│          this projection extracts the tag from that payload.
│
*)

Definition parsed_line_tag (payload : nat) : nat :=
  fst001 payload.

(*
│
│          A successful `parse_line` result carries `encode tag phi`;
│          this projection extracts the displayed formula from that
│          payload.
│
*)

Definition parsed_line_formula (payload : nat) : nat :=
  snd001 payload.

(*
│
│          `nth_line` fetches a line from a tagged derivation body
│          using fuel bounded by the claimed derivation length.
│
*)

Definition nth_line (n body i : nat) : nat :=
  nth_list_fuel (S n) body i.

(*
│
│          `nth_formula` fetches and parses a line, returning the
│          displayed formula when both operations succeed. It is used
│          by later soundness statements as the arithmetic
│          formula-view interface.
│
*)

Definition nth_formula (body i : nat) : nat :=
  let fetched := nth_list (body) i in
  if acceptedb fetched then
    let parsed := parse_line (result_payload fetched) in
    if acceptedb parsed then
      accept (parsed_line_formula (result_payload parsed))
    else parsed
  else fetched.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               K AXIOM CHECKER                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `check_axk phi` checks the K schema `A -> (B -> A)` by two
│          implication parses, one equality test, and formula checks
│          for the exposed metavariables.
│
*)

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

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               S AXIOM CHECKER                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `check_axs phi` checks the S schema `(A -> (B -> C)) -> ((A
│          -> B) -> (A -> C))` by six implication parses, four
│          equality tests, and formula checks for `A`, `B`, and `C`.
│
*)

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

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             MODUS PONENS CHECKER                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `line_formula_result n body i detail` fetches and parses
│          line `i`; on success it returns the displayed formula, and
│          on failure it returns the supplied MP-specific error
│          detail.
│
*)

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

(*
│
│          `check_mp n body j p q` checks that line `j` follows from
│          earlier lines `p` and `q`, where line `q` displays an
│          implication whose antecedent is line `p` and consequent is
│          line `j`.
│
*)

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

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              BASIC RESULT FACTS                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The status projection of an accepted result is the
│          acceptance status.
│
*)

Lemma acceptedb_accept :
  forall payload, acceptedb (accept payload) = true.
Proof.
  intro payload.
  unfold acceptedb, result_status, accept.
  rewrite fst001_encode.
  apply Nat.eqb_refl.
Qed.

(*
│
│          The payload projection of an accepted result is the
│          original payload.
│
*)

Lemma result_payload_accept :
  forall payload, result_payload (accept payload) = payload.
Proof.
  intro payload.
  unfold result_payload, accept.
  apply snd001_encode.
Qed.
