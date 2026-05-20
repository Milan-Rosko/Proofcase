(*S001_01__Lambda_Calculus.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                     Proofcase / S001_01__Lambda_Calculus                     │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file begins the lambda-calculus tutorial. We do not introduce an
  untyped syntax tree yet; instead, we emulate lambda terms inside dependent
  type theory. Rocq functions represent lambda abstraction, ordinary
  application represents term application, and the type checker keeps all
  displayed equations typed. The formal laws are shown in conventional
  notation, while the Rocq examples use everyday scenes.

  Note. This is a guided tutorial, not a full object-language formalization
  of untyped lambda calculus. The early beta and eta examples are
  definitional equalities in Rocq. The later confluence, standardization,
  normal-form, fixed-point, subject-reduction, and normalization sections
  illustrate the shape of the corresponding lambda-calculus theorems through
  small typed scenes.

*)

From S001 Require Export S001_00_Premises.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                    SYNTAX                                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                         M,N ::= x | (M N) | (λx.M)                         *)

(*
│
│          The three syntactic forms of the lambda calculus are
│          visible in a kitchen: an ingredient is a variable, cooking
│          an ingredient is an application, and a recipe waiting for
│          an ingredient is an abstraction.
│
*)

Section Kitchen_Syntax.

Variables Ingredient Meal Receipt : Type.

Variable tomato : Ingredient.
Variable cook : Ingredient -> Meal.
Variable plate : Meal -> Receipt.

(*
│
│          A variable term is like an ingredient already on the
│          counter.
│
*)

Definition ingredient_on_counter : Ingredient := tomato.

(*
│
│          An application term `(M N)` is like applying the cooking
│          step to that ingredient.
│
*)

Definition cooked_tomato : Meal := cook tomato.

(*
│
│          An abstraction term `(λx.M)` is like a recipe: it waits for
│          an ingredient and then cooks it.
│
*)

Definition recipe_waiting_for_ingredient : Ingredient -> Meal :=
  fun ingredient : Ingredient => cook ingredient.

(*
│
│          Nested application is ordinary sequencing: cook the
│          ingredient, then plate the meal.
│
*)

Definition plated_cooked_tomato : Receipt :=
  plate (cook tomato).

End Kitchen_Syntax.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                BETA REDUCTION                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                          ((λx.M) N) →β M⟦x := N⟧                           *)

(*
│
│          Beta-reduction says that handing an input to a waiting
│          recipe is the same as running the recipe with that input.
│          In the host dependent type theory, this is computation:
│          both sides simplify to the same term.
│
*)

Section Cafe_Order.

Variables Order Drink : Type.
Variable make_drink : Order -> Drink.
Variable todays_order : Order.

Theorem handing_order_to_recipe_makes_the_drink :
  (fun order : Order => make_drink order) todays_order =
  make_drink todays_order.
Proof.
  reflexivity.
Qed.

(*
│
│          A closed example is a ticket machine that immediately
│          returns the ticket it receives.
│
*)

Theorem ticket_machine_returns_ticket :
  (fun ticket : nat => ticket) 3 = 3.
Proof.
  reflexivity.
Qed.

(*
│
│          A body may use the input inside a larger statement; after
│          beta-computation, the specific input appears in that
│          statement.
│
*)

Theorem name_badge_checks_its_own_number :
  forall badge_number : nat,
    (fun n : nat => n = n) badge_number =
    (badge_number = badge_number).
Proof.
  intro badge_number.
  reflexivity.
Qed.

End Cafe_Order.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                ETA REDUCTION                                 │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                               λx.(M x) →η M                                *)
(*                                if x ∉ FV(M)                                *)

(*
│
│          Eta-reduction says that a wrapper which only receives a
│          thing and immediately forwards it to `M` behaves as `M`
│          itself. The side condition is represented by the fact that
│          `M` is already in the surrounding context and the displayed
│          binder only names the incoming item.
│
*)

Section Courier_Forwarding.

Variables Parcel Delivered : Type.
Variable courier : Parcel -> Delivered.

Theorem front_desk_that_only_calls_courier_is_courier :
  (fun parcel : Parcel => courier parcel) = courier.
Proof.
  reflexivity.
Qed.

(*
│
│          The same forwarding shape appears after part of a job has
│          already been fixed: once the table is known, a waiter who
│          only forwards the side order is just the kitchen station
│          for that table.
│
*)

Theorem waiter_for_fixed_table_only_forwards_side_order :
  forall (Table Side Plate : Type)
         (kitchen : Table -> Side -> Plate)
         (table : Table),
    (fun side : Side => kitchen table side) = kitchen table.
Proof.
  intros Table Side Plate kitchen table.
  reflexivity.
Qed.

End Courier_Forwarding.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               ALPHA CONVERSION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                            λx.M ≡α λy.M⟦x := y⟧                            *)

(*
│
│          Alpha-conversion says that the private name of a bound
│          input can be changed. A recipe does not care whether its
│          incoming item is called `parcel` or `package`; what matters
│          is that the body uses the same incoming item consistently.
│
*)

Section Name_Tag_Change.

Variables Parcel Delivered : Type.
Variable courier : Parcel -> Delivered.

Theorem parcel_name_tag_can_be_renamed :
  (fun parcel : Parcel => courier parcel) =
  (fun package : Parcel => courier package).
Proof.
  reflexivity.
Qed.

(*
│
│          The same idea applies inside a larger everyday task: the
│          side-order name is private to the waiter function.
│
*)

Theorem side_order_name_tag_can_be_renamed :
  forall (Table Side Plate : Type)
         (kitchen : Table -> Side -> Plate)
         (table : Table),
    (fun side_order : Side => kitchen table side_order) =
    (fun extra : Side => kitchen table extra).
Proof.
  intros Table Side Plate kitchen table.
  reflexivity.
Qed.

End Name_Tag_Change.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                FREE VARIABLES                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                                FV(x) = {x}                                 *)
(*                          FV(M N) = FV(M) ∪ FV(N)                           *)
(*                           FV(λx.M) = FV(M) \ {x}                           *)

(*
│
│          In this typed embedding, we do not compute a syntactic set
│          of free variables. Rocq tracks the same idea through the
│          surrounding context: a term may depend on names from the
│          context, while a lambda binder makes its own input local to
│          the function body.
│
*)

Section Grocery_List_Dependencies.

Variables Ingredient Meal Garnish Label : Type.

Variable tomato : Ingredient.
Variable cook : Ingredient -> Meal.
Variable herb : Garnish.
Variable label_plate : Garnish -> Meal -> Label.

(*
│
│          A variable by itself depends on the matching outside item:
│          the tomato on the counter.
│
*)

Definition counter_item_mentions_tomato : Ingredient := tomato.

(*
│
│          An application depends on the outside names used by both
│          parts: the cooking step and the tomato.
│
*)

Definition cooked_counter_item_mentions_cook_and_tomato : Meal :=
  cook tomato.

(*
│
│          A lambda binds its incoming ingredient. The ingredient name
│          is no longer free outside the recipe, while the herb and
│          cooking step remain outside dependencies.
│
*)

Definition garnish_recipe_keeps_herb_free : Ingredient -> Label :=
  fun ingredient : Ingredient =>
    label_plate herb (cook ingredient).

(*
│
│          Applying the recipe shows which outside names remain and
│          which item is supplied locally.
│
*)

Theorem garnish_recipe_uses_supplied_ingredient :
  forall carrot : Ingredient,
    garnish_recipe_keeps_herb_free carrot =
    label_plate herb (cook carrot).
Proof.
  intro carrot.
  reflexivity.
Qed.

End Grocery_List_Dependencies.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              SUBSTITUTION LEMMA                              │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                               M⟦x := x⟧ = M                                *)
(*                           x ≠ y ⇒ x⟦y := N⟧ = x                            *)
(*                (M₁ M₂)⟦x := N⟧ = (M₁⟦x := N⟧) (M₂⟦x := N⟧)                 *)
(*                           (λx.M)⟦x := N⟧ = λx.M                            *)
(*            y ≠ x ∧ y ∉ FV(N) ⇒ (λy.M)⟦x := N⟧ = λy.(M⟦x := N⟧)             *)

(*
│
│          Substitution is the operational heart of beta-reduction. In
│          Rocq's host theory, these examples appear as ordinary
│          computation: put an everyday item into a waiting expression
│          and both sides reduce to the same result.
│
*)

Section Mailroom_Substitution.

(*
│
│          Substituting a thing for itself changes nothing.
│
*)

Theorem returning_the_same_ticket_changes_nothing :
  forall ticket : nat,
    (fun replacement_ticket : nat => replacement_ticket) ticket =
    ticket.
Proof.
  intro ticket.
  reflexivity.
Qed.

(*
│
│          Changing an unused field does not alter a different outside
│          item.
│
*)

Theorem changing_unused_order_does_not_move_waiter :
  forall (Waiter Order : Type)
         (waiter : Waiter)
         (new_order : Order),
    (fun _ : Order => waiter) new_order = waiter.
Proof.
  intros Waiter Order waiter new_order.
  reflexivity.
Qed.

(*
│
│          Substitution distributes through an application: the chosen
│          order is used both where the drink is made and where the
│          receipt is printed.
│
*)

Theorem chosen_order_flows_through_drink_and_receipt :
  forall (Order Drink Receipt : Type)
         (make_drink : Order -> Drink)
         (print_receipt : Drink -> Receipt)
         (chosen_order : Order),
    (fun order : Order => print_receipt (make_drink order)) chosen_order =
    print_receipt (make_drink chosen_order).
Proof.
  intros Order Drink Receipt make_drink print_receipt chosen_order.
  reflexivity.
Qed.

(*
│
│          If the same name is rebound inside, the outside replacement
│          stops at the new binder.
│
*)

Theorem inner_ticket_window_shadows_outer_ticket :
  forall outside_ticket : nat,
    (fun _ : nat => fun inside_ticket : nat => inside_ticket) outside_ticket =
    (fun inside_ticket : nat => inside_ticket).
Proof.
  intro outside_ticket.
  reflexivity.
Qed.

(*
│
│          If the inner name is different and does not occur in the
│          replacement, substitution safely moves under the lambda. A
│          table is fixed first; the side order remains an incoming
│          local item.
│
*)

Theorem fixed_table_still_waits_for_side_order :
  forall (Table Side Plate : Type)
         (kitchen : Table -> Side -> Plate)
         (selected_table : Table),
    (fun table : Table =>
       fun side_order : Side =>
         kitchen table side_order) selected_table =
    (fun side_order : Side =>
       kitchen selected_table side_order).
Proof.
  intros Table Side Plate kitchen selected_table.
  reflexivity.
Qed.

End Mailroom_Substitution.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         COMPOSITION OF SUBSTITUTIONS                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                             x ≠ y ∧ x ∉ FV(L)                              *)
(*              ⇒ M⟦x := N⟧⟦y := L⟧ = M⟦y := L⟧⟦x := N⟦y := L⟧⟧               *)

(*
│
│          Composing substitutions is like updating two independent
│          fields on the same work order. If the later replacement
│          does not depend on the earlier field, doing the edits in
│          the coordinated order gives the same finished work order.
│
*)

Section Work_Order_Edit_Composition.

Variables Table Order Ticket : Type.
Variable prepare_ticket : Table -> Order -> Ticket.

Theorem table_and_order_edits_arrive_at_same_ticket :
  forall (selected_table : Table) (selected_order : Order),
    (fun order : Order =>
       (fun table : Table =>
          prepare_ticket table order) selected_table) selected_order =
    (fun table : Table =>
       (fun order : Order =>
          prepare_ticket table order) selected_order) selected_table.
Proof.
  intros selected_table selected_order.
  reflexivity.
Qed.

(*
│
│          If one replacement itself is prepared by another ordinary
│          function, the same computation shows that the nested update
│          is accounted for on the right-hand side.
│
*)

Theorem translated_order_edit_is_accounted_for :
  forall (RawOrder CookedOrder PrintedTicket : Type)
         (translate : RawOrder -> CookedOrder)
         (print_ticket : CookedOrder -> PrintedTicket)
         (raw_order : RawOrder),
    (fun cooked_order : CookedOrder =>
       print_ticket cooked_order) (translate raw_order) =
    print_ticket (translate raw_order).
Proof.
  intros RawOrder CookedOrder PrintedTicket translate print_ticket raw_order.
  reflexivity.
Qed.

End Work_Order_Edit_Composition.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               CONTEXT CLOSURE                                │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                                   M →β N                                   *)
(*                                ⇒ M P →β N P                                *)
(*                                ⇒ P M →β P N                                *)
(*                               ⇒ λx.M →β λx.N                               *)

(*
│
│          Context closure says that a local computation is still
│          valid when placed inside a larger scene: on the left of an
│          application, on the right of an application, or under a
│          lambda.
│
*)

Section Kitchen_Context_Closure.

Variables Order Drink Receipt Tray : Type.
Variable make_drink : Order -> Drink.
Variable print_receipt : Drink -> Receipt.
Variable put_on_tray : Tray -> Drink -> Receipt.
Variable tray : Tray.
Variable order : Order.

(*
│
│          A beta step on the function side stays valid after the
│          receipt printer is applied to its result.
│
*)

Theorem receipt_printer_accepts_finished_drink_step :
  print_receipt ((fun order : Order => make_drink order) order) =
  print_receipt (make_drink order).
Proof.
  reflexivity.
Qed.

(*
│
│          A beta step on the argument side stays valid when a fixed
│          tray operation waits for that drink.
│
*)

Theorem tray_station_accepts_finished_drink_step :
  put_on_tray tray ((fun order : Order => make_drink order) order) =
  put_on_tray tray (make_drink order).
Proof.
  reflexivity.
Qed.

(*
│
│          A beta step also stays valid inside a recipe that is
│          waiting for a future order.
│
*)

Theorem waiting_recipe_accepts_inner_drink_step :
  (fun future_order : Order =>
     print_receipt ((fun order : Order => make_drink order) future_order)) =
  (fun future_order : Order =>
     print_receipt (make_drink future_order)).
Proof.
  reflexivity.
Qed.

End Kitchen_Context_Closure.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                         REFLEXIVE-TRANSITIVE CLOSURE                         │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                                   M →* N                                   *)

(*
│
│          A reflexive-transitive closure means zero or more small
│          steps. Rather than building a separate reduction relation
│          here, we use equality as the host-language record of
│          completed computation: zero steps are reflexivity, and
│          several ordinary beta-computations can be chained by
│          simplification.
│
*)

Section Delivery_Route_Closure.

Variables Address Parcel Label : Type.
Variable wrap : Address -> Parcel.
Variable label : Parcel -> Label.
Variable home : Address.

(*
│
│          Zero steps: the package already at the desk is the same
│          package.
│
*)

Theorem package_can_stay_where_it_is :
  home = home.
Proof.
  reflexivity.
Qed.

(*
│
│          Several small beta computations in a row still give the
│          same final labeled package.
│
*)

Theorem address_can_be_wrapped_and_labeled_in_several_steps :
  (fun address : Address =>
     (fun parcel : Parcel =>
        label parcel) (wrap address)) home =
  label (wrap home).
Proof.
  reflexivity.
Qed.

End Delivery_Route_Closure.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               BETA-EQUIVALENCE                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                                   M ≡β N                                   *)
(*                           ⇔ ∃P. M →* P ∧ N →* P                            *)

(*
│
│          Beta-equivalence says that two descriptions are the same
│          for computation when they can be finished to one common
│          result. At the cafe counter, two ways of describing the
│          same receipt meet at the same printed receipt.
│
*)

Section Cafe_Counter_Equivalence.

Variables Order Drink Receipt : Type.
Variable make_drink : Order -> Drink.
Variable print_receipt : Drink -> Receipt.
Variable order : Order.

Theorem two_cafe_descriptions_share_a_finished_receipt :
  exists finished_receipt : Receipt,
    (fun current_order : Order =>
       print_receipt (make_drink current_order)) order =
    finished_receipt /\
    print_receipt ((fun current_order : Order =>
                      make_drink current_order) order) =
    finished_receipt.
Proof.
  exists (print_receipt (make_drink order)).
  split.
  - reflexivity.
  - reflexivity.
Qed.

(*
│
│          The witness is the shared final receipt. Both descriptions
│          compute until they reach it.
│
*)

Theorem direct_and_wrapped_receipt_have_common_counter :
  print_receipt (make_drink order) =
  (fun drink : Drink => print_receipt drink) (make_drink order).
Proof.
  reflexivity.
Qed.

End Cafe_Counter_Equivalence.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                               DIAMOND PROPERTY                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                              M ⇉ N₁ ∧ M ⇉ N₂                               *)
(*                           ⇒ ∃P. N₁ ⇉ P ∧ N₂ ⇉ P                            *)

(*
│
│          The diamond property says that if one instruction card is
│          simplified in two compatible ways, both simplified cards
│          can still be finished to a common card. In the barista
│          example, one worker simplifies the drink-making step first,
│          while another simplifies the labeling wrapper first.
│
*)

Section Barista_Diamond.

Variables Order Drink Label : Type.
Variable make_drink : Order -> Drink.
Variable label_drink : Drink -> Label.
Variable order : Order.

Theorem two_baristas_finish_at_same_labeled_drink :
  exists finished_label : Label,
    (fun drink : Drink =>
       label_drink drink) ((fun current_order : Order =>
                              make_drink current_order) order) =
    finished_label /\
    (fun current_order : Order =>
       label_drink (make_drink current_order)) order =
    finished_label.
Proof.
  exists (label_drink (make_drink order)).
  split.
  - reflexivity.
  - reflexivity.
Qed.

(*
│
│          The common lower point of the diamond is the labeled drink
│          after both simplifications have been performed.
│
*)

Theorem either_barista_route_reaches_the_same_label :
  (fun drink : Drink =>
     label_drink drink) ((fun current_order : Order =>
                            make_drink current_order) order) =
  (fun current_order : Order =>
     label_drink (make_drink current_order)) order.
Proof.
  reflexivity.
Qed.

End Barista_Diamond.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            CHURCH-ROSSER THEOREM                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                                   M ≡β N                                   *)
(*                           ⇒ ∃P. M →* P ∧ N →* P                            *)

(*
│
│          Church-Rosser is the confluence promise for
│          beta-equivalence: if two instruction sheets describe
│          beta-equivalent work, there is a common finished sheet they
│          can both reach. Here we state the promise as an everyday
│          convergence fact: once each route is known to finish at the
│          same counter label, that label is the shared destination.
│
*)

Section Delivery_Confluence.

Variables Address Parcel Label : Type.
Variable wrap : Address -> Parcel.
Variable label : Parcel -> Label.
Variable home : Address.

Theorem equivalent_delivery_routes_have_shared_label :
  forall left_route right_route : Label,
    left_route = label (wrap home) ->
    right_route = label (wrap home) ->
    exists shared_label : Label,
      left_route = shared_label /\
      right_route = shared_label.
Proof.
  intros left_route right_route Hleft Hright.
  exists (label (wrap home)).
  split.
  - exact Hleft.
  - exact Hright.
Qed.

(*
│
│          A concrete confluence witness can also be read directly
│          from computation: wrapping first or labeling through a
│          wrapper reaches the same final label.
│
*)

Theorem wrapped_then_labeled_routes_converge :
  exists shared_label : Label,
    (fun address : Address =>
       label (wrap address)) home =
    shared_label /\
    (fun parcel : Parcel =>
       label parcel) (wrap home) =
    shared_label.
Proof.
  exists (label (wrap home)).
  split.
  - reflexivity.
  - reflexivity.
Qed.

End Delivery_Confluence.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                           STANDARDIZATION THEOREM                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                                   M →* N                                   *)
(*                      ⇒ ∃ standard reduction sequence                       *)
(*                                from M to N                                 *)

(*
│
│          Standardization says that when a messy computation reaches
│          a result, there is a disciplined left-to-right story
│          reaching the same result. At the counter, a cup may be
│          described by nested work, but it can still be told as the
│          standard route: grind, brew, pour.
│
*)

Section Counter_Standard_Route.

Variables Beans Grounds Coffee Cup : Type.
Variable grind : Beans -> Grounds.
Variable brew : Grounds -> Coffee.
Variable pour : Coffee -> Cup.
Variable beans : Beans.

Inductive counter_route_told_in_order : Cup -> Prop :=
  | grind_then_brew_then_pour :
      counter_route_told_in_order
        (pour (brew (grind beans))).

Theorem messy_counter_work_has_orderly_story :
  forall cup : Cup,
    (fun raw_beans : Beans =>
       (fun grounds : Grounds =>
          (fun coffee : Coffee =>
             pour coffee) (brew grounds)) (grind raw_beans)) beans =
    cup ->
    exists standard_cup : Cup,
      standard_cup = cup /\
      counter_route_told_in_order standard_cup.
Proof.
  intros cup Hcup.
  exists (pour (brew (grind beans))).
  split.
  - exact Hcup.
  - constructor.
Qed.

End Counter_Standard_Route.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                                 NORMAL FORM                                  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                                   NF(M)                                    *)
(*                               ⇔ ¬∃N. M →β N                                *)

(*
│
│          A normal form is a finished item: there is no next local
│          beta-step to perform. In the shelf example below, the
│          relation of pending shelf steps has no constructors, so a
│          shelved label has no further one-step work.
│
*)

Section Shelf_Normal_Form.

Variable Label : Type.

Inductive pending_shelf_step : Label -> Label -> Prop := .

Definition label_is_finished_on_shelf (label : Label) : Prop :=
  ~ exists next_label : Label,
      pending_shelf_step label next_label.

Theorem shelf_label_is_finished_exactly_when_no_step_remains :
  forall label : Label,
    label_is_finished_on_shelf label <->
    ~ exists next_label : Label,
        pending_shelf_step label next_label.
Proof.
  intro label.
  split.
  - intro Hfinished.
    exact Hfinished.
  - intro Hno_step.
    exact Hno_step.
Qed.

Theorem finished_shelf_label_has_no_pending_step :
  forall label : Label,
    label_is_finished_on_shelf label.
Proof.
  intros label [next_label Hstep].
  inversion Hstep.
Qed.

End Shelf_Normal_Form.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                          UNIQUENESS OF NORMAL FORMS                          │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                             M →* N₁ ∧ M →* N₂                              *)
(*                             ∧ NF(N₁) ∧ NF(N₂)                              *)
(*                                 ⇒ N₁ ≡α N₂                                 *)

(*
│
│          Uniqueness of normal forms says that if two finished
│          outcomes come from the same starting work, then the
│          finished outcomes agree up to harmless renaming. In this
│          typed tutorial, the harmless renaming is represented by
│          equality of the final receipt values.
│
*)

Section Finished_Receipt_Uniqueness.

Variable Receipt : Type.
Variable counter_receipt : Receipt.

Definition route_reaches_counter_receipt (receipt : Receipt) : Prop :=
  receipt = counter_receipt.

Definition receipt_is_finished (receipt : Receipt) : Prop :=
  receipt = counter_receipt.

Definition receipts_match_up_to_name_tag
    (left_receipt right_receipt : Receipt) : Prop :=
  left_receipt = right_receipt.

Theorem two_finished_receipts_from_same_counter_match :
  forall left_receipt right_receipt : Receipt,
    route_reaches_counter_receipt left_receipt ->
    route_reaches_counter_receipt right_receipt ->
    receipt_is_finished left_receipt ->
    receipt_is_finished right_receipt ->
    receipts_match_up_to_name_tag left_receipt right_receipt.
Proof.
  intros left_receipt right_receipt Hleft Hright _ _.
  unfold receipts_match_up_to_name_tag.
  rewrite Hleft.
  rewrite Hright.
  reflexivity.
Qed.

End Finished_Receipt_Uniqueness.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                            FIXED-POINT COMBINATOR                            │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                      Y ≡ λf.(λx.f (x x)) (λx.f (x x))                      *)
(*                               Y F →β F (Y F)                               *)

(*
│
│          The untyped fixed-point combinator depends on
│          self-application `x x`, which is exactly the kind of
│          unrestricted expression Rocq's typed core rejects. In this
│          typed tutorial we therefore record the usable fixed-point
│          contract: a recurring schedule is one that unfolds to one
│          more refresh of itself.
│
*)

Section Recurring_Schedule.

Variable Schedule : Type.
Variable refresh : Schedule -> Schedule.
Variable weekly_plan : Schedule.

Hypothesis weekly_plan_is_recurring :
  weekly_plan = refresh weekly_plan.

Theorem weekly_plan_unfolds_to_one_more_refresh :
  weekly_plan = refresh weekly_plan.
Proof.
  exact weekly_plan_is_recurring.
Qed.

(*
│
│          Once the recurring contract is known, anything approved for
│          the refreshed plan is approved for the recurring plan
│          itself.
│
*)

Theorem approval_for_refreshed_plan_applies_to_weekly_plan :
  forall approve : Schedule -> Prop,
    approve (refresh weekly_plan) ->
    approve weekly_plan.
Proof.
  intros approve Happroved.
  rewrite weekly_plan_is_recurring.
  exact Happroved.
Qed.

End Recurring_Schedule.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                              SUBJECT REDUCTION                               │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                             Γ ⊢ M : τ ∧ M →β N                             *)
(*                                ⇒ Γ ⊢ N : τ                                 *)

(*
│
│          Subject reduction says that computation preserves type. At
│          the counter, if a ticket expression has the ticket type
│          before the beta-step, the result after printing is still a
│          ticket. Rocq enforces that directly: both sides of the step
│          below are values of the same type `Ticket`.
│
*)

Section Counter_Type_Badge_Preservation.

Variables Order Ticket : Type.
Variable print_ticket : Order -> Ticket.

Inductive counter_beta_step : Ticket -> Ticket -> Prop :=
  | print_waiting_order :
      forall order : Order,
        counter_beta_step
          ((fun current_order : Order =>
              print_ticket current_order) order)
          (print_ticket order).

Definition has_ticket_badge (_ : Ticket) : Prop := True.

Theorem counter_step_keeps_ticket_badge :
  forall before after : Ticket,
    has_ticket_badge before ->
    counter_beta_step before after ->
    has_ticket_badge after.
Proof.
  intros before after _ _.
  exact I.
Qed.

(*
│
│          A concrete beta-step can be packaged with its typed result.
│
*)

Theorem printing_waiting_order_produces_typed_ticket :
  forall order : Order,
    exists printed : Ticket,
      counter_beta_step
        ((fun current_order : Order =>
            print_ticket current_order) order)
        printed /\
      has_ticket_badge printed.
Proof.
  intro order.
  exists (print_ticket order).
  split.
  - constructor.
  - exact I.
Qed.

End Counter_Type_Badge_Preservation.

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                             STRONG NORMALIZATION                             │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
*)

(*                                 Γ ⊢ M : τ                                  *)
(*                 ⇒ no infinite β-reduction sequence from M                  *)

(*
│
│          Strong normalization says that a well-typed computation
│          cannot keep reducing forever. A full proof for the simply
│          typed lambda calculus is substantial; this tutorial
│          illustrates the shape with a typed checkout queue whose
│          remaining work is a natural-number measure that strictly
│          decreases at every step.
│
*)

Section Checkout_Strong_Normalization.

Inductive checkout_step : nat -> nat -> Prop :=
  | finish_one_ticket :
      forall remaining : nat,
        checkout_step (S remaining) remaining.

Inductive checkout_cannot_run_forever_from : nat -> Prop :=
  | checkout_queue_empty :
      checkout_cannot_run_forever_from O
  | checkout_queue_shortens :
      forall remaining_tickets : nat,
        checkout_cannot_run_forever_from remaining_tickets ->
        checkout_cannot_run_forever_from (S remaining_tickets).

Theorem typed_checkout_queue_cannot_run_forever :
  forall remaining_tickets : nat,
    checkout_cannot_run_forever_from remaining_tickets.
Proof.
  induction remaining_tickets as [| earlier_remaining IH].
  - constructor.
  - constructor.
    exact IH.
Qed.

Theorem checkout_step_reveals_smaller_remaining_queue :
  forall before after : nat,
    checkout_step before after ->
    checkout_cannot_run_forever_from after ->
    checkout_cannot_run_forever_from before.
Proof.
  intros before after Hstep Hafter.
  inversion Hstep.
  subst.
  constructor.
  exact Hafter.
Qed.

(*
│
│          A two-ticket queue demonstrates the same measure argument
│          concretely: after one step there is a one-ticket queue, and
│          after another step there is a finished queue.
│
*)

Theorem two_ticket_queue_has_first_two_steps :
  exists one_ticket no_ticket : nat,
    checkout_step 2 one_ticket /\
    checkout_step one_ticket no_ticket /\
    no_ticket = 0.
Proof.
  exists 1.
  exists 0.
  split.
  - constructor.
  - split.
    + constructor.
    + reflexivity.
Qed.

End Checkout_Strong_Normalization.
