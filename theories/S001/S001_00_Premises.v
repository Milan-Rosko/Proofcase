(*S001_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / S001_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  We start with a tutorial layer for elementary propositional reasoning in a
  lambda shaped setting. We show the smallest possible examples: How to
  declare propositions; how to start a proof; how to use assumptions; and how
  to finish proofs. Every theorem here is intentionally tiny and readable.

*)

(*
│
│          We import the basic logical foundations from the standard
│          library.
│
*)

From Stdlib Require Export Init.Logic.

(*
│
│          `Check` asks Rocq to display the type of a term. In type
│          theory, every well-formed term has a type. For functions,
│          the displayed type describes the kinds of arguments the
│          function expects and the kind of result it returns.
│
*)

Check (fun x => x).

(*
│
│          The result says that Rocq inferred a polymorphic identity
│          function. Informally: for any type `A`, if given a value of
│          type `A`, the function returns a value of type `A`.
│
*)

(*
│
│          In traditional lambda calculus, functions are written with
│          the Greek letter λ. Rocq writes λ using the keyword `fun`.
│          The lambda term λx.x becomes:
│
*)

Check (fun x => x).

(*
│
│          The lambda term λx.λy.x becomes:
│
*)

Check (fun x => fun y => x).

(*
│
│          While λx.x is valid in pure lambda calculus, Rocq usually
│          asks: “What kind of thing is x?” Here `x` is explicitly
│          declared to be a natural number.
│
*)

Check (fun x : nat => x).

(*
│
│          But we could use λ also.
│
*)

Notation "'λ' x , t" := (fun x => t)
  (at level 200, x binder, right associativity).

Check (λ x, x).

(*
│
│          The type `nat` is an inductive datatype provided by Rocq's
│          standard foundations. It is not part of pure lambda
│          calculus itself. `bool` is the type of booleans, `Prop` is
│          the universe of logical propositions.
│
*)

Check nat.
Check bool.
Check Prop.

(*
│
│          We can see that rocq follows a functional paradigm.
│
*)

Inductive german_day : Type :=
  | Montag
  | Dienstag
  | Mittwoch
  | Donnerstag
  | Freitag
  | Samstag
  | Sonntag.
  
Definition next_german_day (d:german_day) : german_day :=
  match d with
  | Montag => Dienstag
  | Dienstag => Mittwoch
  | Mittwoch => Donnerstag
  | Donnerstag => Freitag
  | Freitag => Samstag
  | Samstag => Sonntag
  | Sonntag => Montag
  end.

Compute (next_german_day Freitag).


(*
│
│          Applying a function means substituting an argument into its
│          body. Rocq can compute such reductions automatically.
│
*)

Definition id_nat := fun x : nat => x.

Compute id_nat 5.

(*
│
│          Functions may also return functions. The term λx.λy.x is a
│          curried function: it remembers the first argument and
│          ignores the second.
│
*)

Definition first_nat :=
  fun x : nat =>
  fun y : nat =>
    x.

Compute first_nat 3 7.

(*
│
│          In dependent type theory, propositions are types. A proof
│          of a proposition is simply a term inhabiting that type.
│
*)

Check forall n : nat, nat.

(*
│
│          Suppose we have three propositions: “it is raining”, “the
│          street is wet”, and “people carry umbrellas”.
│
*)

Section Rain_Examples.

Variables Rain WetStreet Umbrella : Prop.

(*
│
│          Logical implication behaves like a function type. A proof
│          of: Rain -> WetStreet is a function transforming proofs of
│          `Rain` into proofs of `WetStreet`.
│
*)

Variable rain_causes_wet : Rain -> WetStreet.

(*
│
│          Likewise, rain may also cause umbrellas to appear.
│
*)

Variable rain_causes_umbrellas : Rain -> Umbrella.

(*
│
│          To prove an implication, we assume its premise.
│
*)

Theorem rain_makes_wet :
  Rain -> WetStreet.
Proof.
  intro HRain.
  apply rain_causes_wet.
  exact HRain.
Qed.

(*
│
│          After `intro HRain`, the assumption `HRain : Rain` is
│          available in the local context.
│
*)

(*
│
│          Internally, the previous proof behaves exactly like a
│          lambda function.
│
*)

Check (fun HRain : Rain => rain_causes_wet HRain).

(*
│
│          We can define the same theorem directly as a proof term.
│
*)

Theorem rain_makes_wet_term :
  Rain -> WetStreet.
Proof.
  exact (fun HRain => rain_causes_wet HRain).
Qed.

(*
│
│          Suppose wet streets imply umbrellas.
│
*)

Variable wet_implies_umbrellas :
  WetStreet -> Umbrella.

(*
│
│          Now we can chain implications together: Rain -> WetStreet
│          -> Umbrella
│
*)

Theorem rain_implies_umbrellas :
  Rain -> Umbrella.
Proof.
  intro HRain.
  apply wet_implies_umbrellas.
  apply rain_causes_wet.
  exact HRain.
Qed.

(*
│
│          The proof above can also be written compactly as a single
│          lambda expression.
│
*)

Theorem rain_implies_umbrellas_term :
  Rain -> Umbrella.
Proof.
  exact
    (fun HRain =>
       wet_implies_umbrellas
         (rain_causes_wet HRain)).
Qed.

(*
│
│          Every proposition implies itself.
│
*)

Theorem identity_prop :
  forall P : Prop, P -> P.
Proof.
  intro P.
  intro HP.
  exact HP.
Qed.

(*
│
│          If we already possess a proof of `Rain`, and a rule saying
│          rain causes wet streets, then we may directly conclude
│          `WetStreet`.
│
*)

Theorem use_existing_assumptions :
  Rain ->
  (Rain -> WetStreet) ->
  WetStreet.
Proof.
  intro HRain.
  intro HRule.
  apply HRule.
  exact HRain.
Qed.

End Rain_Examples.

(*
│
│          This concludes the miniature introduction.
│
*)
