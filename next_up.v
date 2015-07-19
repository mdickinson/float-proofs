(* Definitions of next_up and next_down for binary floats. *)

(* For a positive float f, we can define next_up f as

   (f / twopowerQ (binadeQ f)) + 1) * twopowerQ (binadeQ f) *)

Require Import ZArith.
Require Import QArith.
Require Import Qabs.
Require Import remedial.
Require Import rearrange_tactic.
Require Import floor_and_ceiling.
Require Import twopower.
Require Import twopower_tactics.
Require Import binary_float.

Lemma bob x y : is_integer x -> is_integer y ->
                (x + 1 <= y  <->  x < y).
Proof.
  intros x_integer y_integer; split; intro H.
  - apply Qlt_le_trans with (y := x + 1); [rearrange_goal (0 < 1) | ]; easy.
  - destruct x_integer as [m Hm], y_integer as [n Hn].
    revert H; rewrite <- Hm; rewrite <- Hn; intro H.
    setoid_replace 1 with (inject_Z 1) by now compute.
    rewrite <- inject_Z_plus.
    rewrite <- Zle_Qle.
    apply Zlt_le_succ.
    rewrite Zlt_Qlt.
    easy.
Qed.

Set Implicit Arguments.

(* We need a function to decompose a nonzero float into its exponent
   and significand, as integers. *)

Section NonzeroFloatResults.

  (* First assume that we have a nonzero float. *)
  Variable p : positive.
  Variable f : binary_float p.
  Variable f_nonzero : ~(proj1_sig f == 0).

  Definition float_exponent := (binadeQ (proj1_sig f) f_nonzero - (' p) + 1)%Z.
  Definition float_significand :=
    floor (proj1_sig f / twopowerQ float_exponent).

  Lemma recompose_float :
    proj1_sig f == inject_Z float_significand * twopowerQ float_exponent.
  Proof.
    unfold float_significand, float_exponent;
    destruct f as [x [ m [e [m_small xme]] ]]; simpl.
    twopower_left; symmetry; apply floor_integer.
    (* Now showing that x / twopowerQ (binadeQ x f_nonzero - ' p + 1)
       is an integer. *)
    setoid_replace
      (x / twopowerQ (binadeQ x f_nonzero - 'p + 1))
    with (
      ((x / twopowerQ e) *
       (twopowerQ e / twopowerQ (binadeQ x f_nonzero - 'p + 1))))
      by (field; split; apply twopowerQ_nonzero).
    apply is_integer_mul.
    - exists m; now twopower_left.
    - rewrite <- twopowerQ_div; apply is_integer_twopowerQ.
      assert (binadeQ x f_nonzero < e + ' p)%Z; [ | omega];
      apply twopowerQ_binadeQ_lt; rewrite xme; now twopower_right.
  Qed.

  Lemma significand_bounded :
    twopowerQ (' p - 1) <= Qabs (inject_Z float_significand) < twopowerQ ('p).
  Proof.
    setoid_replace (inject_Z float_significand)
    with (proj1_sig f / twopowerQ float_exponent)
      by (twopower_left; symmetry; apply recompose_float);
    split; unfold float_exponent.
    - twopower_left; apply twopowerQ_binadeQ_le with (q_nonzero := f_nonzero);
      omega.
    - twopower_right; apply twopowerQ_binadeQ_lt with (q_nonzero := f_nonzero);
      omega.
  Qed.

  (* Now we're in a position to define next_up. *)
  Section NextUp.
    (* next_up: we simply increase the significand, except
       in the case where it's -2**(p-1). *)

    Let special_case :=
      Qeq_dec (inject_Z float_significand) (-twopowerQ ('p - 1)).

    Let next_up_significand :=
      if special_case then (2*float_significand + 1)%Z
      else (float_significand + 1)%Z.

    Let next_up_exponent :=
      if special_case then (float_exponent - 1)%Z else float_exponent.

    Lemma next_up_significand_bounded :
      Qabs (inject_Z next_up_significand) <= twopowerQ ('p).
    Proof.
      subst next_up_significand; destruct special_case as [q | q].
      - (* Case where significand == -(2**(p-1)). *)
        rewrite inject_Z_plus; rewrite inject_Z_mult;
        setoid_replace (inject_Z 1) with 1 by easy;
        setoid_replace (inject_Z 2) with 2 by easy;
        rewrite q.
        rewrite Qabs_neg.
        (* map inject_Z through *)
        rearrange_goal (2 * twopowerQ ('p - 1) - 1 <= twopowerQ (' p)).
        setoid_replace 2 with (twopowerQ 1) by easy.
        rewrite <- twopowerQ_mul.
        ring_simplify (1 + (' p - 1))%Z.
        rearrange_goal (-(1) <= 0).
        now compute.

        rearrange_goal (1 <= 2 * twopowerQ ('p - 1)).
        setoid_replace 2 with (twopowerQ 1) by easy.
        rewrite <- twopowerQ_mul.
        setoid_replace 1 with (twopowerQ 0) by easy.
        apply twopowerQ_monotonic_le.
        ring_simplify.
        easy.
      - rewrite inject_Z_plus.
        apply Qle_trans
        with (y := Qabs (inject_Z float_significand) + Qabs (inject_Z 1)).
        + apply Qabs_triangle.
        + setoid_replace (Qabs (inject_Z 1)) with 1 by easy.
          apply bob.
          SearchAbout (Qabs (inject_Z _)).
          rewrite Qabs_Zabs.
          apply is_integer_inject_Z.
          apply is_integer_twopowerQ.
          easy.
          apply significand_bounded.
    Qed.

    Definition next_up :=
      float_from_significand_and_exponent
        p next_up_significand next_up_exponent next_up_significand_bounded.

  End NextUp.

End NonzeroFloatResults.
