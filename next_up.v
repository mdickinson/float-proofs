(* Definitions of next_up and next_down for binary floats. *)

(* For a positive float f, we can define next_up f as

   (f / twopowerQ (binadeQ f)) + 1) * twopowerQ (binadeQ f) *)

Require Import ZArith.
Require Import QArith.
Require Import Qabs.
Require Import remedial.
Require Import rearrange_tactic.
Require Import floor_and_ceiling.
Require Import qpos.
Require Import twopower.
Require Import cobinade.
Require Import twopower_tactics.
Require Import binary_float.

Lemma Qlt_le_succ x y : is_integer x -> is_integer y ->
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
          apply Qlt_le_succ.
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

Definition nonzero_lt_dec q : ~(q == 0) -> { 0 < q } + { 0 < -q }.
Proof.
  intro; destruct (Qlt_le_dec q 0).
  - right; rearrange.
  - left; apply Qle_not_eq; try apply Qnot_eq_sym; easy.
Defined.


Section NextUpAgain.
  Variable p : positive.
  Variable f : binary_float p.
  Variable f_nonzero : ~(proj1_sig f == 0).

  (* If f is positive then 1 <= f / 2^(binade f) < 2, so
                        2^(p-1) <= f / 2^(binade f - p + 1) < 2^p.

     If f is negative then 1/2 < (-f) / 2^(binade -f) <= 1, so
        - (2^p) <= f / 2^(cobinade (-f) - p) < 2^(p-1).
   *)

  Let next_up_exponent :=
    match nonzero_lt_dec f_nonzero with
    | left q_positive => (binade (exist _ _ q_positive) - ' p + 1)%Z
    | right negq_positive => (cobinade (exist _ _ negq_positive) - ' p)%Z
    end.

  Let next_up_significandQ := proj1_sig f / twopowerQ next_up_exponent.

  Lemma next_up_significand_is_integral :
    is_integer next_up_significandQ.
  Proof.
    subst next_up_significandQ next_up_exponent.
    destruct (nonzero_lt_dec f_nonzero).
    - (* positive case *)
      destruct f as [x [m [e [m_bounded x_eq_m2e]]]].
      simpl in *.
      setoid_replace (x / twopowerQ (binade (exist (Qlt 0) x q) - ' p + 1))
      with ((x / twopowerQ e) *
            (twopowerQ e / twopowerQ (binade (exist (Qlt 0) x q) - ' p + 1))).
      apply is_integer_mul.
      + rewrite x_eq_m2e.
        setoid_replace (inject_Z m * twopowerQ e / twopowerQ e) with (inject_Z m).
        apply is_integer_inject_Z.
        field.
        apply twopowerQ_nonzero.
      + rewrite <- twopowerQ_div.
        apply is_integer_twopowerQ.
        assert (binade (exist (Qlt 0) x q) < e + 'p)%Z.
        apply twopower_binade_lt.
        unfold QPos.lt. simpl.
        rewrite x_eq_m2e.
        setoid_replace (inject_Z 2 ^ (e + 'p)) with (twopowerQ (e + 'p)) by easy.
        twopower_right.
        apply Qle_lt_trans with (y := Qabs (inject_Z m)).
        apply Qle_Qabs.
        assumption.
        omega.
      + field.
        split.
        apply twopowerQ_nonzero.
        apply twopowerQ_nonzero.
    - (* negative case *)
      destruct f as [x [m [e [m_bounded x_eq_m2e]]]].
      simpl in *.
      remember (cobinade (exist (Qlt 0) (- x)%Q q) - ' p)%Z as b.
      rewrite x_eq_m2e.
      setoid_replace (inject_Z m * twopowerQ e / twopowerQ b)
      with (inject_Z m * (twopowerQ e / twopowerQ b)).
      apply is_integer_mul.
      apply is_integer_inject_Z.
      rewrite <- twopowerQ_div.
      apply is_integer_twopowerQ.
      rewrite Heqb.
      assert (cobinade (exist (Qlt 0) (-x)%Q q) <= e + ' p)%Z.
      apply twopower_cobinade_le.
      unfold QPos.le. simpl.
      rewrite x_eq_m2e.
      change (inject_Z 2 ^ (e + ' p)) with (twopowerQ (e + ' p)).
      twopower_right.
      apply Qlt_le_weak.
      apply Qle_lt_trans with (y := Qabs (inject_Z m)).
      apply Qle_Qabs_neg.
      easy.
      omega.
      field.
      apply twopowerQ_nonzero.
  Qed.



End NextUpAgain.