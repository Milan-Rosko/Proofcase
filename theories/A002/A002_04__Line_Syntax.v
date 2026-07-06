(*A002_04__Line_Syntax.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                       Proofcase / A002_04__Line_Syntax                       │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  Line-syntax layer for A002-Core. We encode proof lines as A001-canonical
  pairs of a rule tag and displayed formula, and encode the fixed Hilbert
  rule tags for K, S, and modus ponens.

  This layer validates only line and rule-tag structure. It does not certify
  formula well-formedness; the corresponding rule checker performs that check
  at the first rule-local obligation that needs formula shape.

*)

From A002 Require Export A002_03__Formula_Syntax.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               LINE CONSTRUCTOR                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          A proof line pairs a rule tag code with the formula
│          displayed on that line.
│
*)

Definition code_line (tag formula : nat) : nat :=
  encode tag formula.

(*
│
│          `line_tag` reads the rule tag exposed by A001 decoding. It
│          is dispatched as a rule tag only after the enclosing line
│          has passed the canonical A001 test.
│
*)

Definition line_tag (ell : nat) : nat :=
  fst001 ell.

(*
│
│          `line_formula` reads the displayed formula exposed by A001
│          decoding. Rule checkers decide whether this number is a
│          well-formed formula of the required syntactic shape.
│
*)

Definition line_formula (ell : nat) : nat :=
  snd001 ell.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                  RULE TAGS                                   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The fixed A002-Core rule code for the K axiom schema.
│
*)

Definition RULE_AXK : nat := 0.

(*
│
│          The fixed A002-Core rule code for the S axiom schema.
│
*)

Definition RULE_AXS : nat := 1.

(*
│
│          The fixed A002-Core rule code for modus ponens.
│
*)

Definition RULE_MP : nat := 2.

(*
│
│          The K-axiom tag has rule code `RULE_AXK` and empty payload
│          `0`.
│
*)

Definition tag_axk : nat :=
  encode RULE_AXK 0.

(*
│
│          The S-axiom tag has rule code `RULE_AXS` and empty payload
│          `0`.
│
*)

Definition tag_axs : nat :=
  encode RULE_AXS 0.

(*
│
│          The modus-ponens tag has rule code `RULE_MP` and a
│          canonical A001 pair of cited line indices.
│
*)

Definition tag_mp (p q : nat) : nat :=
  encode RULE_MP (encode p q).

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               RULE TAG PARSING                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `rule_code` reads the outer rule code exposed by A001
│          decoding. It is dispatched only after tag canonicity has
│          been checked.
│
*)

Definition rule_code (tag : nat) : nat :=
  fst001 tag.

(*
│
│          `rule_payload` reads the outer rule payload exposed by A001
│          decoding. Its expected shape depends on the checked rule
│          code.
│
*)

Definition rule_payload (tag : nat) : nat :=
  snd001 tag.

(*
│
│          `parse_rule_tag tag` returns `accept (encode rule payload)`
│          when `tag` is one of the three canonical A002-Core rule
│          tags.
│
*)

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

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                 LINE PARSING                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          `parse_line ell` returns the canonical tag/formula payload
│          of a line after checking that the line itself is canonical
│          and its tag is a valid A002-Core rule tag. If tag parsing
│          fails, the tag parser's encoded diagnostic is carried as
│          the line parser detail.
│
*)

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

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              CONSTRUCTOR FACTS                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*
│
│          The constructed K tag parses as the K rule with empty
│          payload.
│
*)

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

(*
│
│          The constructed S tag parses as the S rule with empty
│          payload.
│
*)

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

(*
│
│          A constructed modus-ponens tag parses as the MP rule with
│          canonical citation payload.
│
*)

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

(*
│
│          A line built with the K tag parses to its original
│          tag/formula payload.
│
*)

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

(*
│
│          A line built with the S tag parses to its original
│          tag/formula payload.
│
*)

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

(*
│
│          A line built with an MP tag parses to its original
│          tag/formula payload.
│
*)

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
