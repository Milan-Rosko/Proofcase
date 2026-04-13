(*@file@*)

(*@head.start@*)
(*@copyright@*)
(*@doc.proofcase@*)

(*@doc.header@[[Overview]]@*)

(*@doc.pl@[[This layer packages three already-computed band codes into one state-code equation.]]@*)

(*@doc.pl@[[Its role for `compile_fm_family_correct` is narrow: it proves the additive aggregation step `state = ip_code + r1_code + r2_code`. It does not, by itself, arithmetize digit extraction or stand alone as a full state decoder.]]@*)

(*@head.end@*)

From P002 Require Export P002_02__Bands.

Definition MachineState : Type := FMState.

Definition emit_state_codec_rhs (ip_var r1_var r2_var : nat) : list term :=
  [ {| coeff := 1; mono := m_linear ip_var |};
    {| coeff := 1; mono := m_linear r1_var |};
    {| coeff := 1; mono := m_linear r2_var |} ].

(*@inline@[[`emit_state_codec_rhs` is only the additive payload of the state codec. The band-code arithmetic lives in `P002_02`; this file merely sums those three pre-established channels.]]@*)

Definition state_codec_equation
    (state_var ip_var r1_var r2_var : nat) : h10_nd3n_equation :=
  {|
    var_count := S (Nat.max state_var (Nat.max ip_var (Nat.max r1_var r2_var)));
    lhs_terms := [{| coeff := 1; mono := m_linear state_var |}];
    rhs_terms := emit_state_codec_rhs ip_var r1_var r2_var
  |}.

Definition state_codec_valuation
    (state_var ip_var r1_var r2_var : nat) (st : MachineState) : valuation :=
  fun n =>
    if Nat.eqb n state_var then encode_state st
    else if Nat.eqb n ip_var then ip_code (state_ip st)
    else if Nat.eqb n r1_var then r1_code (state_r1 st)
    else if Nat.eqb n r2_var then r2_code (state_r2 st)
    else 0.

Definition state_codec_vars_separated
    (state_var ip_var r1_var r2_var : nat) : Prop :=
  state_var <> ip_var /\
  state_var <> r1_var /\
  state_var <> r2_var /\
  ip_var <> r1_var /\
  ip_var <> r2_var /\
  r1_var <> r2_var.

Lemma eval_poly_singleton_term :
  forall (t : term) (rho : valuation),
    eval_poly [t] rho = eval_term rho t.
Proof.
  intros t rho.
  unfold eval_poly.
  simpl.
  lia.
Qed.

Lemma eval_state_codec_rhs :
  forall rho ip_var r1_var r2_var,
    eval_poly (emit_state_codec_rhs ip_var r1_var r2_var) rho =
    rho ip_var + rho r1_var + rho r2_var.
Proof.
  intros rho ip_var r1_var r2_var.
  unfold emit_state_codec_rhs, eval_poly, eval_term.
  simpl.
  lia.
Qed.

Lemma state_codec_equation_wf :
  forall state_var ip_var r1_var r2_var,
    equation_wf (state_codec_equation state_var ip_var r1_var r2_var).
Proof.
  intros state_var ip_var r1_var r2_var.
  unfold state_codec_equation.
  split.
  - constructor.
    + simpl.
      apply Nat.lt_succ_r.
      apply Nat.le_max_l.
    + constructor.
  - constructor.
    + simpl.
      apply Nat.lt_succ_r.
      apply Nat.le_trans with (m := Nat.max ip_var (Nat.max r1_var r2_var)).
      * apply Nat.le_max_l.
      * apply Nat.le_max_r.
    + constructor.
      * simpl.
        apply Nat.lt_succ_r.
        apply Nat.le_trans with (m := Nat.max ip_var (Nat.max r1_var r2_var)).
        -- apply Nat.le_trans with (m := Nat.max r1_var r2_var).
           ++ apply Nat.le_max_l.
           ++ apply Nat.le_max_r.
        -- apply Nat.le_max_r.
      * constructor.
        -- simpl.
           apply Nat.lt_succ_r.
           apply Nat.le_trans with (m := Nat.max ip_var (Nat.max r1_var r2_var)).
           ++ apply Nat.le_trans with (m := Nat.max r1_var r2_var).
              ** apply Nat.le_max_r.
              ** apply Nat.le_max_r.
           ++ apply Nat.le_max_r.
        -- constructor.
Qed.

Lemma state_codec_equation_semantics :
  forall rho state_var ip_var r1_var r2_var,
    solves (state_codec_equation state_var ip_var r1_var r2_var) rho <->
    equation_wf (state_codec_equation state_var ip_var r1_var r2_var) /\
    rho state_var = rho ip_var + rho r1_var + rho r2_var.
Proof.
  intros rho state_var ip_var r1_var r2_var.
  unfold solves, state_codec_equation.
  split.
  - intros [Hwf Hsol].
    split.
    + exact Hwf.
    + change
        (eval_poly [{| coeff := 1; mono := m_linear state_var |}] rho =
         eval_poly (emit_state_codec_rhs ip_var r1_var r2_var) rho) in Hsol.
      rewrite eval_poly_singleton_term in Hsol.
      rewrite eval_state_codec_rhs in Hsol.
      unfold eval_term in Hsol.
      simpl in Hsol.
      lia.
  - intros [Hwf Hsum].
    split.
    + exact Hwf.
    + change
        (eval_poly [{| coeff := 1; mono := m_linear state_var |}] rho =
         eval_poly (emit_state_codec_rhs ip_var r1_var r2_var) rho).
      rewrite eval_poly_singleton_term.
      rewrite eval_state_codec_rhs.
      unfold eval_term.
      simpl.
      lia.
Qed.

(*@inline@[[The semantic content of the emitted state equation is exactly one additive identity: the designated state variable must equal the sum of the three band-code variables. Nothing stronger is hidden here; all digit-level meaning must already have been established upstream in the band layer.]]@*)
(*@unicodemath@[[solves(state\_codec\_equation(s,i,r_1,r_2),\rho)]][[\Leftrightarrow equation\_wf(\cdots)\ \wedge\ \rho(s)=\rho(i)+\rho(r_1)+\rho(r_2).]]@*)

Lemma state_codec_equation_correct :
  forall state_var ip_var r1_var r2_var st,
    state_codec_vars_separated state_var ip_var r1_var r2_var ->
    solves
      (state_codec_equation state_var ip_var r1_var r2_var)
      (state_codec_valuation state_var ip_var r1_var r2_var st).
Proof.
  intros state_var ip_var r1_var r2_var st
    (Hsip & Hsr1 & Hsr2 & Hipr1 & Hipr2 & Hr1r2).
  apply (proj2 (state_codec_equation_semantics
                  (state_codec_valuation state_var ip_var r1_var r2_var st)
                  state_var ip_var r1_var r2_var)).
  split.
  - apply state_codec_equation_wf.
  - unfold state_codec_valuation.
    assert (Hstate :
      (if state_var =? state_var then encode_state st
       else if state_var =? ip_var then ip_code (state_ip st)
       else if state_var =? r1_var then r1_code (state_r1 st)
       else if state_var =? r2_var then r2_code (state_r2 st)
       else 0) = encode_state st).
    { rewrite Nat.eqb_refl. reflexivity. }
    assert (Hip :
      (if ip_var =? state_var then encode_state st
       else if ip_var =? ip_var then ip_code (state_ip st)
       else if ip_var =? r1_var then r1_code (state_r1 st)
       else if ip_var =? r2_var then r2_code (state_r2 st)
       else 0) = ip_code (state_ip st)).
    {
      destruct (Nat.eqb_spec ip_var state_var) as [Heq|Hneq].
      - exfalso. apply Hsip. symmetry. exact Heq.
      - rewrite Nat.eqb_refl.
        reflexivity.
    }
    assert (Hr1 :
      (if r1_var =? state_var then encode_state st
       else if r1_var =? ip_var then ip_code (state_ip st)
       else if r1_var =? r1_var then r1_code (state_r1 st)
       else if r1_var =? r2_var then r2_code (state_r2 st)
       else 0) = r1_code (state_r1 st)).
    {
      destruct (Nat.eqb_spec r1_var state_var) as [Heq|Hneq].
      - exfalso. apply Hsr1. symmetry. exact Heq.
      - destruct (Nat.eqb_spec r1_var ip_var) as [Heq'|Hneq'].
        + exfalso. apply Hipr1. symmetry. exact Heq'.
        + rewrite Nat.eqb_refl.
          reflexivity.
    }
    assert (Hr2 :
      (if r2_var =? state_var then encode_state st
       else if r2_var =? ip_var then ip_code (state_ip st)
       else if r2_var =? r1_var then r1_code (state_r1 st)
       else if r2_var =? r2_var then r2_code (state_r2 st)
       else 0) = r2_code (state_r2 st)).
    {
      destruct (Nat.eqb_spec r2_var state_var) as [Heq|Hneq].
      - exfalso. apply Hsr2. symmetry. exact Heq.
      - destruct (Nat.eqb_spec r2_var ip_var) as [Heq'|Hneq'].
        + exfalso. apply Hipr2. symmetry. exact Heq'.
        + destruct (Nat.eqb_spec r2_var r1_var) as [Heq''|Hneq''].
          * exfalso. apply Hr1r2. symmetry. exact Heq''.
          * rewrite Nat.eqb_refl.
            reflexivity.
    }
    rewrite Hstate, Hip, Hr1, Hr2.
    rewrite encode_state_as_components.
    lia.
Qed.

(*@inline@[[`state_codec_equation_correct` should therefore be read as an aggregation lemma over precomputed band-code variables, not as a self-contained proof that raw digit variables decode to a machine state.]]@*)

Lemma encode_is_canonical :
  forall st,
    state_well_formed st ->
    zeck_valid (state_support st).
Proof.
  exact state_support_valid.
Qed.

Lemma decode_encode_id :
  forall st,
    state_well_formed st ->
    decode_state (encode_state st) = st.
Proof.
  exact decode_state_encode_state.
Qed.

Lemma encode_injective :
  forall st1 st2,
    state_well_formed st1 ->
    state_well_formed st2 ->
    encode_state st1 = encode_state st2 ->
    st1 = st2.
Proof.
  exact encode_state_injective.
Qed.

(*@inline@[[`state_arithmetization_form` is the projection-facing converse used later in P002: whenever a raw code is known to lie in the valid FM image, decoding it and re-expanding its three channels recovers the same arithmetic decomposition. This is the precise point where the total projection semantics of D001 is turned back into a usable additive identity.]]@*)
(*@unicodemath@[[valid\_state\_code(s)\ \wedge\ decode\_state(s)=st]][[\Rightarrow s = r2\_code(st.r_2)+r1\_code(st.r_1)+ip\_code(st.ip).]]@*)

Lemma state_arithmetization_form :
  forall s st,
    valid_state_code s ->
    decode_state s = st ->
    s =
    r2_code (state_r2 st) +
    r1_code (state_r1 st) +
    ip_code (state_ip st).
Proof.
  intros s st Hvalid Hdecode.
  destruct Hvalid as [st' [Hwf Hcode]].
  subst s.
  rewrite decode_state_encode_state in Hdecode by exact Hwf.
  subst st.
  apply encode_state_as_components.
Qed.
