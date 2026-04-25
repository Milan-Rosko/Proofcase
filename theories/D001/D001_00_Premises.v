(*D001_00_Premises.v*)

(*
┌──────────────────────────────────────────────────────────────────────────────┐
│                                      Author and Copyright remark. Author(s): │
│                ╭╮╮╮─╮                Milan Rosko  https://www.milanrosko.com │
│                ││││╭╯                Licence. This file is distributed under │
│                 ╯╯╯╰                 the Mozilla Public License Version 2.0, │
│                                      visit https://www.mozilla.org/en-US/MPL │
└──────────────────────────────────────────────────────────────────────────────┘
┌──────────────────────────────────────────────────────────────────────────────┐
│                         Proofcase / D001_00_Premises                         │
└──────────────────────────────────────────────────────────────────────────────┘

  OVERVIEW

  This file imports the full A001 CARRYLESS PAIRING development as the
  arithmetic substrate of the Iterant layer and records only a minimal public
  contract for D001.

*)

From A001 Require Export A001_98_IO.

Definition pair_encode_t : Type := nat -> nat -> nat.
Definition pair_decode_t : Type := nat -> nat * nat.

Definition state_encoder_t (State : Type) : Type := State -> nat.
Definition state_decoder_t (State : Type) : Type := nat -> State.
Definition state_wf_t (State : Type) : Type := State -> Prop.

Definition structured_run_t (Program State : Type) : Type :=
  Program -> nat -> State -> State.

Definition abstract_run_t (Program Config : Type) : Type :=
  Program -> nat -> Config -> Config.

Definition config_to_state_t (Config State : Type) : Type :=
  Config -> State.

Definition acceptance_t (Program : Type) : Type :=
  Program -> nat -> Prop.

(*
│
│          The arithmetic shell inherits the same exact carryless
│          guarantees as A001: roundtrip and the corresponding
│          injectivity law.
│
*)

Definition pair_roundtrip_spec
    (encode : pair_encode_t) (decode : pair_decode_t) : Prop :=
  forall a b, decode (encode a b) = (a, b).

Definition pair_injective_spec (encode : pair_encode_t) : Prop :=
  forall a b a' b',
    encode a b = encode a' b' ->
    a = a' /\ b = b'.

(*
│
│          The state codec contract is partial: decode after encode is
│          required only on states satisfying the package’s
│          well-formedness discipline.
│
*)

Definition state_codec_roundtrip_spec
    {State : Type}
    (encode_state : state_encoder_t State)
    (decode_state : state_decoder_t State)
    (state_well_formed : state_wf_t State) : Prop :=
  forall st,
    state_well_formed st ->
    decode_state (encode_state st) = st.

(*
│
│          The run bridge says that transporting an abstract
│          configuration into the structured state layer commutes with
│          finite execution.
│
*)

Definition run_bridge_spec
    {Program Config State : Type}
    (config_to_state : config_to_state_t Config State)
    (abstract_run_steps : abstract_run_t Program Config)
    (run_steps : structured_run_t Program State) : Prop :=
  forall prog fuel cfg,
    config_to_state (abstract_run_steps prog fuel cfg) =
    run_steps prog fuel (config_to_state cfg).

(*
│
│          The final abstraction guarantee forgets the chosen band
│          geometry: family acceptance implies classical acceptance.
│
*)

Definition acceptance_bridge_spec
    {Program : Type}
    (FamilyMachineAccepts : acceptance_t Program)
    (ClassicMachineAccepts : acceptance_t Program) : Prop :=
  forall prog input,
    FamilyMachineAccepts prog input ->
    ClassicMachineAccepts prog input.

(*
│
│          `iterant_machine_contract` is the minimal D001 package
│          promise: arithmetic exactness, codec exactness on
│          well-formed states, run compatibility across the
│          structured/classical views, and the acceptance abstraction
│          theorem.
│
*)

Definition iterant_machine_contract
    {Program Config State : Type}
    (encode_pair : pair_encode_t)
    (decode_pair : pair_decode_t)
    (encode_state : state_encoder_t State)
    (decode_state : state_decoder_t State)
    (state_well_formed : state_wf_t State)
    (config_to_state : config_to_state_t Config State)
    (abstract_run_steps : abstract_run_t Program Config)
    (run_steps : structured_run_t Program State)
    (FamilyMachineAccepts : acceptance_t Program)
    (ClassicMachineAccepts : acceptance_t Program) : Prop :=
  pair_roundtrip_spec encode_pair decode_pair /\
  state_codec_roundtrip_spec encode_state decode_state state_well_formed /\
  run_bridge_spec config_to_state abstract_run_steps run_steps /\
  acceptance_bridge_spec FamilyMachineAccepts ClassicMachineAccepts.
