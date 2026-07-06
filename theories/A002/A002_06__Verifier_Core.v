(*A002_06__Verifier_Core.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                      Proofcase / A002_06__Verifier_Core                      │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Verifier-core layer for A002-Core. We implement the bounded line loop over
  a length-indexed derivation body, dispatch each canonical line to the fixed
  Hilbert rule checkers, and assemble the final arithmetic certificate
  payload.

  The verifier checks only a supplied finite derivation code. It performs no
  proof search, no semantic truth test, and no lambda-calculus evaluation.
  Every loop is structurally recursive on explicit fuel derived from the
  claimed derivation length.

*)

From A002 Require Export A002_05__Rule_Checkers_Hilbert.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          LOCAL CERTIFICATE PAYLOADS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `code_local_cert j checked_rule` records that line `j` was
│          accepted by a local rule checker whose successful payload
│          is `checked_rule`. The payload itself is already of the
│          form `encode rule data`.
│
*)

Definition code_local_cert_payload (j checked_rule : nat) : nat :=
  encode j checked_rule.

(*
│
│          `code_final_cert_payload` records the claimed length,
│          target, local certificate list, and final displayed
│          formula. The local list is accumulated in reverse
│          verification order by the core loop.
│
*)

Definition code_final_cert_payload
  (n theta certs final_formula : nat)
  : nat :=
  encode n (encode theta (encode certs final_formula)).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                LINE DISPATCH                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `verify_line n body j` fetches line `j`, checks its
│          canonical line shape and rule tag, dispatches to the
│          corresponding rule checker, and returns the local
│          certificate payload on success.
│
*)

Definition verify_line (n body j : nat) : nat :=
  let fetched := nth_line n body j in
  if acceptedb fetched then
    let ell := result_payload fetched in
    if canonical001b ell then
      let tag := line_tag ell in
      let phi := line_formula ell in
      let parsed_tag := parse_rule_tag tag in
      if acceptedb parsed_tag then
        let tag_payload := result_payload parsed_tag in
        let rule := fst001 tag_payload in
        let payload := snd001 tag_payload in
        if Nat.eqb rule RULE_AXK then
          let checked := check_axk phi in
          if acceptedb checked then
            accept (code_local_cert_payload j (result_payload checked))
          else
            reject STAGE_RULE j (result_payload checked)
        else if Nat.eqb rule RULE_AXS then
          let checked := check_axs phi in
          if acceptedb checked then
            accept (code_local_cert_payload j (result_payload checked))
          else
            reject STAGE_RULE j (result_payload checked)
        else if Nat.eqb rule RULE_MP then
          if canonical001b payload then
            let p := fst001 payload in
            let q := snd001 payload in
            let checked := check_mp n body j p q in
            if acceptedb checked then
              accept (code_local_cert_payload j (result_payload checked))
            else
              reject STAGE_RULE j (result_payload checked)
          else
            reject STAGE_TAG j ERR_NONCANONICAL_NODE
        else
          reject STAGE_TAG j ERR_UNKNOWN_RULE
      else
        reject STAGE_TAG j (result_payload parsed_tag)
    else
      reject STAGE_LINE j ERR_NONCANONICAL_LINE
  else
    reject STAGE_LINE j (result_payload fetched).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              BOUNDED LINE LOOP                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `verify_lines fuel n body j certs` checks lines `j` through
│          `n - 1`, consuming one unit of fuel per line. The
│          accumulator `certs` is a tagged list of local certificates.
│
*)

Fixpoint verify_lines
  (fuel n body j certs : nat)
  : nat :=
  match fuel with
  | 0 =>
      if Nat.eqb j n then
        accept certs
      else
        reject STAGE_RULE j ERR_FUEL_EXHAUSTED
  | S fuel' =>
      if Nat.eqb j n then
        accept certs
      else
        let checked := verify_line n body j in
        if acceptedb checked then
          let local_cert := result_payload checked in
          verify_lines fuel' n body (S j) (code_cons local_cert certs)
        else
          checked
  end.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               FINAL CONCLUSION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `final_formula_result n body` fetches the last line of a
│          nonempty derivation and returns its displayed formula. It
│          is used only after the bounded line loop has accepted.
│
*)

Definition final_formula_result (n body : nat) : nat :=
  let last := Nat.pred n in
  let fetched := nth_line n body last in
  if acceptedb fetched then
    let parsed := parse_line (result_payload fetched) in
    if acceptedb parsed then
      accept (parsed_line_formula (result_payload parsed))
    else
      reject STAGE_CONCLUSION last (result_payload parsed)
  else
    reject STAGE_CONCLUSION last (result_payload fetched).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                MAIN VERIFIER                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `A002_Verify d theta` checks the canonical derivation
│          header, exact body length, every local line, and final
│          conclusion equality against `theta`. Success returns
│          `accept p`; failure returns the first deterministic
│          arithmetic error.
│
*)

Definition A002_Verify (d theta : nat) : nat :=
  if canonical001b d then
    let n := fst001 d in
    let body := snd001 d in
    if list_exact_lengthb n body then
      if Nat.eqb n 0 then
        reject STAGE_CONCLUSION 0 ERR_EMPTY_DERIVATION
      else
        let checked_lines := verify_lines n n body 0 code_nil in
        if acceptedb checked_lines then
          let certs := result_payload checked_lines in
          let final_formula := final_formula_result n body in
          if acceptedb final_formula then
            let phi_last := result_payload final_formula in
            if Nat.eqb phi_last theta then
              accept (code_final_cert_payload n theta certs phi_last)
            else
              reject STAGE_CONCLUSION (Nat.pred n) ERR_BAD_CONCLUSION
          else
            final_formula
        else
          checked_lines
    else
      reject STAGE_LIST_STRUCTURE 0 ERR_BAD_DERIVATION_LENGTH
  else
    reject STAGE_DERIVATION_HEADER 0 ERR_NONCANONICAL_DERIVATION.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               BASIC LOOP FACTS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          At the end index, the bounded verifier loop accepts the
│          accumulated certificate list without inspecting fuel beyond
│          the guard.
│
*)

Lemma verify_lines_at_end :
  forall fuel n body certs,
    verify_lines (S fuel) n body n certs = accept certs.
Proof.
  intros fuel n body certs.
  cbn [verify_lines].
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(*
│
│          The main verifier is a deterministic function. This theorem
│          is included here as the computational determinism fact; the
│          exported soundness layer may re-export it.
│
*)

Theorem A002_Verify_deterministic :
  forall d theta r1 r2,
    A002_Verify d theta = r1 ->
    A002_Verify d theta = r2 ->
    r1 = r2.
Proof.
  intros d theta r1 r2 H1 H2.
  rewrite <- H1.
  exact H2.
Qed.
