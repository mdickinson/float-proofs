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

(* Move this to remedial results. *)

Lemma Zle_ge_succ (x y : Z) : (x <= y  \/  y + 1 <= x)%Z.
Proof.
  omega.
Qed.

Lemma Zle_ge_pred (x y : Z) : (x <= y - 1  \/  y <= x)%Z.
Proof.
  omega.
Qed.

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

Lemma Qlt_le_pred x y : is_integer x -> is_integer y ->
                        (x < y  <->  x <= y - 1).
Proof.
  setoid_replace (x <= y - 1) with (x + 1 <= y) by (split; intro; rearrange).
  intros; split; now apply Qlt_le_succ.
Qed.

(* Move these elsewhere *)

Set Implicit Arguments.

Lemma float_lt_le_dec p (x : binary_float p) (y : binary_float p) :
  { (x < y)%float } + { (y <= x)%float }.
Proof.
  apply Qlt_le_dec.
Qed.

(* Some preparation.  First we show that if a rational x satisfies 2**e <= x <=
   2**(e+1) then x is representable in precision p if and only if x /
   2**(e-p+1) is an integer. *)

Lemma per_binade_representability x e p :
  twopowerQ e <= x <= twopowerQ (e + 1)  ->
  (representable p x  <->  is_integer (x / twopowerQ (e - ' p + 1))).
Proof.
  intro H; split.
  - unfold representable.
    destruct 1 as [m [a [m_small x_in_terms_of_m_and_a]]].
    rewrite x_in_terms_of_m_and_a in *; clear x_in_terms_of_m_and_a.
    setoid_replace (inject_Z m * twopowerQ a / twopowerQ (e - 'p + 1))
    with (inject_Z m * (twopowerQ a / twopowerQ (e - 'p + 1))).
    apply is_integer_mul.
    apply is_integer_inject_Z.
    rewrite <- twopowerQ_div.
    apply is_integer_twopowerQ.
    assert (e <= a + 'p - 1)%Z.
    apply Z.lt_le_pred.
    apply twopowerQ_injective_lt.
    apply Qle_lt_trans with (y := inject_Z m * twopowerQ a).
    easy.
    twopower_right.
    apply Qle_lt_trans with (y := Qabs (inject_Z m)).
    apply Qle_Qabs.
    easy.
    omega.
    field.
    apply twopowerQ_nonzero.
  - destruct 1 as [m x_scaled_is_m].
    assert (x == inject_Z m * twopowerQ (e - 'p + 1)) as H0.
    twopower_left.
    easy.
    rewrite H0.
    apply representable_le_bound.
    rewrite x_scaled_is_m.
    twopower_right.
    rewrite Qabs_pos.
    easy.
    apply Qle_trans with (y := twopowerQ e).
    apply Qlt_le_weak, twopowerQ_positive.
    easy.
Qed.

(* Let's begin by defining next_up and next_down for positive floats,
   and showing their properties. *)

Section NextUpNextDownPositive.

  Variable p : positive.
  Variable f : binary_float p.
  Variable f_positive : (0 < f)%float.

  Lemma f_nonzero : ~(proj1_sig f == 0).
  Proof.
    now apply Qnot_eq_sym, Qlt_not_eq.
  Qed.

  Let f_as_qpos : QPos := exist _ (proj1_sig f) f_positive.

  Section NextUpPositive.

  Let next_up_exponent := (binade f_as_qpos - 'p + 1)%Z.

  Lemma _next_up_significand_is_integer :
    is_integer (proj1_sig f / twopowerQ next_up_exponent).
  Proof.
    apply per_binade_representability;
    change (proj1_sig f) with (proj1_sig f_as_qpos).
    - split.
      + apply twopower_binade_le; omega.
      + apply Qlt_le_weak, twopower_binade_lt; omega.
    - now destruct f.
  Qed.

  Let next_up_significand :=
    (floor (proj1_sig f / twopowerQ next_up_exponent) + 1)%Z.

  Lemma _next_up_positive_significand_bound :
    proj1_sig f / twopowerQ next_up_exponent < twopowerQ (' p).
  Proof.
    unfold next_up_exponent; twopower_right.
    change (proj1_sig f) with (proj1_sig f_as_qpos).
    apply twopower_binade_lt.
    omega.
  Qed.

  Definition next_up_positive : binary_float p.
  Proof.
    refine (float_from_significand_and_exponent
              p next_up_significand next_up_exponent _).
    rewrite Qabs_pos.
    - unfold next_up_significand.
      rewrite inject_Z_plus.
      change (inject_Z 1) with 1.
      apply Qlt_le_succ.
      apply is_integer_inject_Z.
      apply is_integer_twopowerQ.
      easy.
      apply Qle_lt_trans with (y := proj1_sig f / twopowerQ next_up_exponent).
      apply floor_spec. apply Z.le_refl.
      apply _next_up_positive_significand_bound.
    - unfold next_up_significand.
      rewrite inject_Z_plus.
      change (inject_Z 1) with 1.
      rearrange_goal
        (-(1) <= inject_Z (floor (proj1_sig f / twopowerQ next_up_exponent))).
      apply Qle_trans with (y := 0).
      easy.
      change 0 with (inject_Z 0).
      rewrite <- Zle_Qle.
      apply floor_spec.
      change (inject_Z 0) with 0.
      twopower_left.
      apply Qlt_le_weak.
      easy.
  Defined.

  (* Now we show that next_up_positive is in the same closed binade. *)

  Lemma _f_lower_bound : twopowerQ (binade f_as_qpos) <= proj1_sig f.
  Proof.
    change (proj1_sig f) with (proj1_sig f_as_qpos).
    apply twopower_binade_le.
    apply Z.le_refl.
  Qed.

  Lemma _next_up_positive_upper_bound :
    proj1_sig next_up_positive <= twopowerQ (binade f_as_qpos + 1).
  Proof.
    unfold next_up_positive, next_up_significand, next_up_exponent.
    simpl.
    twopower_right.
    rewrite inject_Z_plus.
    change (inject_Z 1) with 1.
    apply Qlt_le_succ.
    apply is_integer_inject_Z.
    apply is_integer_twopowerQ.
    easy.
    apply Qle_lt_trans with (y := proj1_sig f / twopowerQ (binade f_as_qpos - 'p + 1)).
    apply floor_spec. apply Z.le_refl.
    twopower_right.
    change (proj1_sig f) with (proj1_sig f_as_qpos).
    apply twopower_binade_lt.
    omega.
  Qed.

  (* Basic result: f < next_up f *)

  Theorem lt_next_up_positive : (f < next_up_positive)%float.
  Proof.
    unfold float_lt, next_up_positive, next_up_significand. simpl.
    twopower_left.
    generalize (proj1_sig f / twopowerQ next_up_exponent).
    intro q.
    rewrite inject_Z_plus.
    change (inject_Z 1) with 1.
    now apply floor_spec_alt.
  Qed.

  (* Now the result that completely specifies next_up_positive:
     there are no floats between f and next_up_positive f. *)

  Let e := binade f_as_qpos.

  Theorem next_up_positive_is_next_up (g : binary_float p) :
    (g <= f)%float  \/  (next_up_positive <= g)%float.
  Proof.
    (* Divide into cases. *)
    destruct (Qlt_le_dec (proj1_sig g) (twopowerQ e));
    [ | destruct (Qlt_le_dec (twopowerQ (e + 1)) (proj1_sig g))].
    - (* Case g < 2**e. *)
      left.
      apply Qlt_le_weak.
      apply Qlt_le_trans with (y := twopowerQ e).
      easy.
      apply _f_lower_bound.
    - (* Case 2**(e+1) < g. *)
      right.
      apply Qlt_le_weak.
      apply Qle_lt_trans with (y := twopowerQ (e + 1)).
      apply _next_up_positive_upper_bound.
      easy.
    - (* Case 2**e <= g <= 2**(e + 1) *)
      assert (is_integer (proj1_sig g / twopowerQ next_up_exponent)).
      apply per_binade_representability.
      auto.
      now destruct g.
      unfold float_le.
      destruct (Zle_ge_succ (floor (proj1_sig g / twopowerQ next_up_exponent))
                           (floor (proj1_sig f / twopowerQ next_up_exponent))).
      + (* Case g / 2**e <= f / 2**e *)
        left.
        scale_by (/ twopowerQ next_up_exponent).
        rewrite <- twopowerQ_inv.
        apply twopowerQ_positive.
        change (proj1_sig g * / twopowerQ next_up_exponent)
        with (proj1_sig g / twopowerQ next_up_exponent).
        change (proj1_sig f * / twopowerQ next_up_exponent)
        with (proj1_sig f / twopowerQ next_up_exponent).
        setoid_replace (proj1_sig g / twopowerQ next_up_exponent)
        with (inject_Z (floor (proj1_sig g / twopowerQ next_up_exponent))).
        setoid_replace (proj1_sig f / twopowerQ next_up_exponent)
        with (inject_Z (floor (proj1_sig f / twopowerQ next_up_exponent))).
        now rewrite <- Zle_Qle.
        symmetry.
        apply floor_integer.
        apply _next_up_significand_is_integer.
        symmetry.
        apply floor_integer.
        assumption.
      + (* Case f / 2**e + 1 <= g / 2**e. *)
        right.
        unfold next_up_positive, next_up_significand. simpl.
        twopower_right.
        setoid_replace (proj1_sig g / twopowerQ next_up_exponent)
        with (inject_Z (floor (proj1_sig g / twopowerQ next_up_exponent))).
        now rewrite <- Zle_Qle.

        symmetry.
        apply floor_integer.
        easy.
  Qed.

  End NextUpPositive.

  (* The definition of next_down is mostly analogous, using cobinade
     instead of binade. *)

  Section NextDownPositive.

  Let next_down_exponent := (cobinade f_as_qpos - ' p)%Z.

  Lemma _next_down_significand_is_integer :
    is_integer (proj1_sig f / twopowerQ next_down_exponent).
  Proof.
    destruct f as [x [m [e [H0 H1]]]].
    simpl.
    rewrite H1.
    unfold Qdiv.
    rewrite <- twopowerQ_inv.
    rewrite <- Qmult_assoc.
    rewrite <- twopowerQ_mul.
    unfold next_down_exponent.
    apply is_integer_mul.
    apply is_integer_inject_Z.
    apply is_integer_twopowerQ.
    assert (cobinade f_as_qpos <= e + 'p)%Z.
    apply twopower_cobinade_le.
    subst f_as_qpos.
    simpl.
    unfold QPos.le.
    simpl.
    change (inject_Z 2^(e + 'p)) with (twopowerQ (e + 'p)).
    (* Showing that x <= 2^(e - 'p). *)
    rewrite H1.
    twopower_right.
    rewrite <- Qabs_pos.
    apply Qlt_le_weak.
    easy.
    scale_by (twopowerQ e).
    apply twopowerQ_positive.
    rewrite <- H1.
    twopower_right.
    twopower_left.
    simpl in f_positive.
    unfold float_lt in f_positive.
    simpl in f_positive.
    apply Qlt_le_weak.
    easy.
    omega.
  Qed.

  Let next_down_significand :=
    (ceiling (proj1_sig f / twopowerQ next_down_exponent) - 1)%Z.

  
  Lemma stuart :
    inject_Z (ceiling (proj1_sig f / twopowerQ next_down_exponent)) <=
    twopowerQ (' p).
  Proof.
    apply integer_le_ceiling.
    apply is_integer_twopowerQ.
    easy.
    unfold next_down_exponent.
    twopower_right.
    change (proj1_sig f) with (proj1_sig f_as_qpos).
    apply twopower_cobinade_le.
    apply Z.le_refl.
  Qed.

  Lemma kevin :
    twopowerQ ('p - 1) <= inject_Z next_down_significand.
  Proof.
    unfold next_down_significand.

    unfold Z.sub.
    rewrite inject_Z_plus.
    rewrite inject_Z_opp.
    (* change (inject_Z 1) with 1. *)
    apply Qlt_le_pred.
    apply is_integer_twopowerQ.
    assert (0 < ' p)%Z.
    easy.
    omega.
    apply is_integer_inject_Z.
    apply Qlt_le_trans
    with (y := proj1_sig f / twopowerQ next_down_exponent).
    unfold next_down_exponent.
    twopower_left.
    change (proj1_sig f) with (proj1_sig f_as_qpos).
    apply twopower_cobinade_lt.
    omega.
    apply ceiling_spec.
    apply Z.le_refl.
  Qed.

  Definition next_down_positive : binary_float p.
  Proof.
    refine (float_from_significand_and_exponent
              p next_down_significand next_down_exponent _).
    rewrite Qabs_pos.
    apply Qle_trans
    with (y := inject_Z (ceiling (proj1_sig f /
                                            twopowerQ next_down_exponent))).
    unfold next_down_significand.
    rewrite <- Zle_Qle.
    omega.
    apply stuart.
    apply Qle_trans with (y := twopowerQ ('p - 1)).
    apply Qlt_le_weak.
    apply twopowerQ_positive.
    apply kevin.
  Defined.

  Theorem lt_next_down_positive : (next_down_positive < f)%float.
  Proof.
    unfold float_lt, next_down_positive, next_down_significand. simpl.
    twopower_right.
    generalize (proj1_sig f / twopowerQ next_down_exponent).
    intro.
    apply ceiling_spec_lt.
    omega.
  Qed.

  Let e := cobinade f_as_qpos.

  Theorem next_down_positive_is_next_down (g : binary_float p) :
    (g <= next_down_positive)%float  \/  (f <= g)%float.
  Proof.
    destruct (Qlt_le_dec (proj1_sig g) (twopowerQ (e - 1)));
    [ | destruct (Qlt_le_dec (twopowerQ e) (proj1_sig g))].
    - (* Case g < 2**(e - 1) *)
      left.
      apply Qle_trans with (y := twopowerQ (e - 1)).
      now apply Qlt_le_weak.

      (* showing that ... *)
      subst e.
      unfold next_down_positive, next_down_exponent. simpl.
      twopower_left.
      apply kevin.
    - (* Case 2**e < g *)
      right.
      apply Qle_trans with (y := twopowerQ e).
      change (proj1_sig f) with (proj1_sig f_as_qpos).
      apply twopower_cobinade_le.
      subst e.
      apply Z.le_refl.
      apply Qlt_le_weak.
      easy.
    - (* Case 2^(e-1) <= g <= 2^e. *)
      (* Either g/2^exp <= f/2^exp - 1, or g/2^exp >= f/2^exp. *)
      destruct (Zle_ge_pred
                  (ceiling (proj1_sig g / twopowerQ next_down_exponent))
                  (ceiling (proj1_sig f / twopowerQ next_down_exponent))).
      + left.
        unfold float_le, next_down_positive, next_down_significand. simpl.
        twopower_left.
        now apply ceiling_spec.
      + right.
        unfold float_le.
        scale_by (/ twopowerQ next_down_exponent).
        apply Qinv_lt_0_compat, twopowerQ_positive.
        change (proj1_sig g * / twopowerQ next_down_exponent)
        with (proj1_sig g / twopowerQ next_down_exponent).
        change (proj1_sig f * / twopowerQ next_down_exponent)
        with (proj1_sig f / twopowerQ next_down_exponent).
        setoid_replace (proj1_sig g / twopowerQ next_down_exponent)
        with (inject_Z (ceiling (proj1_sig g / twopowerQ next_down_exponent))).
        setoid_replace (proj1_sig f / twopowerQ next_down_exponent)
        with (inject_Z (ceiling (proj1_sig f / twopowerQ next_down_exponent))).
        now rewrite <- Zle_Qle.
        symmetry.
        apply ceiling_integer.
        apply _next_down_significand_is_integer.
        symmetry.
        apply ceiling_integer.

        apply large_representable_is_integer with (p := p).
        apply scaled_representable_is_representable_div.
        now destruct g.
        unfold next_down_exponent.
        twopower_left.
        unfold e in q0.
        rewrite Qabs_pos.
        easy.
        apply Qle_trans with (y := twopowerQ (e - 1)).
        apply Qlt_le_weak.
        apply twopowerQ_positive.
        easy.
  Qed.

  End NextDownPositive.

End NextUpNextDownPositive.

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
        setoid_replace (inject_Z m * twopowerQ e / twopowerQ e)
        with (inject_Z m).
        apply is_integer_inject_Z.
        field.
        apply twopowerQ_nonzero.
      + rewrite <- twopowerQ_div.
        apply is_integer_twopowerQ.
        assert (binade (exist (Qlt 0) x q) < e + 'p)%Z.
        apply twopower_binade_lt.
        unfold QPos.lt. simpl.
        rewrite x_eq_m2e.
        setoid_replace (inject_Z 2 ^ (e + 'p))
        with (twopowerQ (e + 'p)) by easy.
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