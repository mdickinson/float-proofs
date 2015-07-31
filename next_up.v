(* Definitions of next_up and next_down for binary floats. *)

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

Notation "[ e ]" := (exist _ e _).
Notation "' x" := (proj1_sig x).

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

(* Let's begin by defining next_up and next_down for positive floats,
   and showing their properties. *)

Section NextUpNextDownPositive.

  Variable p : positive.
  Variable f : binary_float p.
  Variable f_positive : (0 < f)%float.

  Let f_as_qpos : QPos := exist _ (proj1_sig f) f_positive.

  Section NextUpPositive.

    Let next_up_exponent := (binade f_as_qpos - 'p + 1)%Z.

    Let significand := proj1_sig f_as_qpos / twopowerQ next_up_exponent.

    Let next_up_significand :=
      (floor (proj1_sig f_as_qpos / twopowerQ next_up_exponent) + 1)%Z.

    Lemma significand_bounded_below :
      twopowerQ (' p - 1) <= significand.
    Proof.
      unfold significand, next_up_exponent; twopower_left;
      apply twopower_binade_le, Z.le_refl.
    Qed.

    Lemma significand_lt_next_up_significand :
      significand < inject_Z next_up_significand.
    Proof.
      unfold significand, next_up_significand; apply floor_spec_lt; omega.
    Qed.

    Lemma next_up_significand_bounded_above :
      inject_Z next_up_significand <= twopowerQ (' p).
    Proof.
      unfold next_up_significand; rewrite inject_Z_plus;
      change (inject_Z 1) with 1; apply Qlt_le_succ;
      [ apply is_integer_inject_Z | now apply is_integer_twopowerQ | ];
      apply Qle_lt_trans
        with (y := proj1_sig f_as_qpos / twopowerQ next_up_exponent).
      - apply floor_spec, Z.le_refl.
      - unfold next_up_exponent; twopower_right;
        apply twopower_binade_lt; omega.
    Qed.

    Definition _next_up_positive : binary_float p.
    Proof.
      refine (float_from_significand_and_exponent
                p next_up_significand next_up_exponent _);
      rewrite Qabs_pos.
      - apply next_up_significand_bounded_above.
      - apply Qle_trans with (y := twopowerQ ('p -1));
        [ | apply Qle_trans
            with (y := (proj1_sig f_as_qpos / twopowerQ next_up_exponent))].
        + apply Qlt_le_weak, twopowerQ_positive.
        + apply significand_bounded_below.
        + apply Qlt_le_weak, significand_lt_next_up_significand.
    Defined.

    (* The next two results completely determine _next_up_positive:
       we have f < _next_up_positive, and there are no floats
       between f and _next_up_positive. *)

    Theorem lt_next_up_positive : (f < _next_up_positive)%float.
    Proof.
      unfold float_lt, _next_up_positive; simpl;
      change (proj1_sig f) with (proj1_sig f_as_qpos);
      twopower_left; apply significand_lt_next_up_significand.
    Qed.

    Theorem next_up_positive_positive : (0 < _next_up_positive)%float.
    Proof.
      apply float_lt_trans with (y := f); try easy; apply lt_next_up_positive.
    Qed.

    Theorem next_up_positive_is_next_up (g : binary_float p) :
      (g <= f)%float  \/  (_next_up_positive <= g)%float.
    Proof.
      destruct (Qlt_le_dec (proj1_sig g) (twopowerQ (binade f_as_qpos))).
      - (* Case g < twopowerQ (binade f_as_qpos) *)
        left; apply Qlt_le_weak;
        apply Qlt_le_trans with (y := twopowerQ (binade f_as_qpos)).
        + easy.
        + change (proj1_sig f) with (proj1_sig f_as_qpos);
          apply twopower_binade_le, Z.le_refl.
      - (* Case twopowerQ (binade f_as_qpos) <= g *)
        destruct (Zle_ge_succ
                    (floor (proj1_sig g / twopowerQ next_up_exponent))
                    (floor (proj1_sig f / twopowerQ next_up_exponent))).
        (* Case (g / 2^exp) <= (f / 2^exp). *)
        + left.
          unfold float_le.
          scale_by (/ twopowerQ next_up_exponent);
            [ rewrite <- twopowerQ_inv; apply twopowerQ_positive | ].
          apply Qle_trans
          with (y := inject_Z (floor (proj1_sig f /
                                                twopowerQ next_up_exponent))).
          * change (proj1_sig g * / twopowerQ next_up_exponent)
            with (proj1_sig g / twopowerQ next_up_exponent);
            setoid_replace (proj1_sig g / twopowerQ next_up_exponent)
            with (inject_Z (floor (proj1_sig g / twopowerQ next_up_exponent)));
            [ now rewrite <- Zle_Qle | symmetry; apply floor_integer].
            apply (large_representable_is_integer p).
            apply scaled_representable_is_representable_div;
              now destruct g.
            unfold next_up_exponent; twopower_left;
            rewrite Qabs_pos; try easy.
            (* Showing that 0 <= proj1_sig g. *)
            apply Qle_trans with (2 := q), Qlt_le_weak, twopowerQ_positive.
          * apply floor_spec, Z.le_refl.
        + (* Case (f / 2^exp) + 1 <= (g / 2^exp) *)
          right.
          unfold float_le, _next_up_positive.
          simpl.
          twopower_right.
          unfold next_up_significand.
          apply Qle_trans
          with
          (y := inject_Z (floor (proj1_sig g / twopowerQ next_up_exponent))).
          * now rewrite <- Zle_Qle.
          * apply floor_spec, Z.le_refl.
    Qed.

  End NextUpPositive.

  (* The definition of next_down is mostly analogous, using cobinade
     instead of binade. *)

  Section NextDownPositive.

    Let next_down_exponent := (cobinade f_as_qpos - ' p)%Z.

    Let significand := proj1_sig f_as_qpos / twopowerQ next_down_exponent.

    Let next_down_significand :=
      (ceiling (proj1_sig f_as_qpos / twopowerQ next_down_exponent) - 1)%Z.

    Lemma next_down_significand_bounded_below :
      twopowerQ ('p - 1) <= inject_Z next_down_significand.
    Proof.
      unfold next_down_significand, Z.sub; rewrite inject_Z_plus;
      change (inject_Z (- (1))) with (-(1)); apply Qlt_le_pred.
      - apply is_integer_twopowerQ; assert (0 < ' p)%Z by easy; omega.
      - apply is_integer_inject_Z.
      - apply Qlt_le_trans
        with (y := proj1_sig f_as_qpos / twopowerQ next_down_exponent).
        + unfold next_down_exponent; twopower_left;
          apply twopower_cobinade_lt; omega.
        + apply ceiling_spec, Z.le_refl.
    Qed.

    Lemma next_down_significand_lt_significand :
      inject_Z next_down_significand < significand.
    Proof.
      unfold significand, next_down_significand; apply ceiling_spec_lt; omega.
    Qed.

    Lemma significand_bounded_above :
      significand <= twopowerQ (' p).
    Proof.
      unfold significand, next_down_exponent; twopower_right;
      apply twopower_cobinade_le, Z.le_refl.
    Qed.

    Definition _next_down_positive : binary_float p.
    Proof.
      refine (float_from_significand_and_exponent
                p next_down_significand next_down_exponent _);
      rewrite Qabs_pos.
      - apply Qle_trans with (y := significand).
        + apply Qlt_le_weak, next_down_significand_lt_significand.
        + apply significand_bounded_above.
      - (* Showing that next_down_significand_is_nonnegative *)
        apply Qle_trans with (y := twopowerQ ('p - 1)).
        + apply twopowerQ_nonnegative.
        + apply next_down_significand_bounded_below.
    Defined.

    Theorem lt_next_down_positive : (_next_down_positive < f)%float.
    Proof.
      unfold float_lt, _next_down_positive; simpl;
      change (proj1_sig f) with (proj1_sig f_as_qpos);
      twopower_right; apply next_down_significand_lt_significand.
    Qed.

    Theorem next_down_positive_positive : (0 < _next_down_positive)%float.
    Proof.
      unfold float_lt, _next_down_positive; simpl; twopower_left;
      apply Qlt_le_trans with (y := twopowerQ ('p - 1)).
      + apply twopowerQ_positive.
      + apply next_down_significand_bounded_below.
    Qed.

    Theorem next_down_positive_is_next_down (g : binary_float p) :
      (g <= _next_down_positive)%float  \/  (f <= g)%float.
    Proof.
      destruct (Qlt_le_dec (proj1_sig g) (twopowerQ (cobinade f_as_qpos - 1))).
      - (* Case g < 2^(cobinade f - 1) *)
        left; apply Qlt_le_weak, Qlt_le_trans with (1 := q).
        unfold _next_down_positive, next_down_significand, next_down_exponent;
        simpl; twopower_left; apply next_down_significand_bounded_below.
      - (* Case 2^(cobinade f - 1) <= g *)
        destruct
          (Zle_ge_pred
             (ceiling (proj1_sig g / twopowerQ next_down_exponent))
             (ceiling (proj1_sig f_as_qpos / twopowerQ next_down_exponent))).
        + (* Case g / 2^exp <= f / 2^exp - 1. *)
          left.
          unfold float_le, _next_down_positive. simpl.
          twopower_left.
          setoid_replace (proj1_sig g / twopowerQ next_down_exponent)
          with (inject_Z (ceiling (proj1_sig g /
                                             twopowerQ next_down_exponent))).
          rewrite <- Zle_Qle.
          easy.
          symmetry.
          apply ceiling_integer.
          apply (large_representable_is_integer p).
          apply scaled_representable_is_representable_div; now destruct g.
          rewrite Qabs_pos.
          unfold next_down_exponent.
          twopower_left.
          easy.
          twopower_left.
          apply Qle_trans with (y := twopowerQ (cobinade f_as_qpos - 1)).
          apply twopowerQ_nonnegative.
          easy.
        + (* Case f / 2^exp <= g / 2^exp. *)
          right.
          unfold float_le.
          scale_by (/ twopowerQ next_down_exponent).
          apply Qinv_lt_0_compat.
          apply twopowerQ_positive.
          setoid_replace
            (proj1_sig f * / twopowerQ next_down_exponent)
          with
          (inject_Z (ceiling (proj1_sig f / twopowerQ next_down_exponent))).
          setoid_replace
            (proj1_sig g * / twopowerQ next_down_exponent)
          with
          (inject_Z (ceiling (proj1_sig g / twopowerQ next_down_exponent))).
          rewrite <- Zle_Qle.
          easy.
          symmetry.
          apply ceiling_integer.
          apply (large_representable_is_integer p).
          apply scaled_representable_is_representable_div.
          destruct g.
          easy.
          unfold next_down_exponent.
          change (proj1_sig g * / twopowerQ (cobinade f_as_qpos - ' p))
          with (proj1_sig g / twopowerQ (cobinade f_as_qpos - ' p)).
          twopower_left.
          rewrite Qabs_pos.
          easy.
          apply Qle_trans with (y := twopowerQ (cobinade f_as_qpos - 1)).
          apply twopowerQ_nonnegative.
          easy.
          symmetry.
          apply ceiling_integer.
          apply (large_representable_is_integer p).
          apply scaled_representable_is_representable_div.
          now destruct f.
          unfold next_down_exponent.
          change (proj1_sig f * / twopowerQ (cobinade f_as_qpos - ' p))
          with (proj1_sig f / twopowerQ (cobinade f_as_qpos - ' p)).
          twopower_left.
          rewrite Qabs_pos.
          change (proj1_sig f) with (proj1_sig f_as_qpos).
          apply Qlt_le_weak.
          apply twopower_cobinade_lt.
          omega.
          apply Qlt_le_weak.
          easy.
    Qed.

  End NextDownPositive.

End NextUpNextDownPositive.

(* Now we're in a position to define the next_up and next_down functions.
   Note that they're defined only for nonzero floats, and that both
   functions *return* nonzero floats. *)

Section NextUpNextDown.

  Open Scope float.

  Lemma float_positive_implies_nonzero p (f : binary_float p) :
    0 < f  ->  ~(f == 0).
  Proof.
    intro; now apply Qnot_eq_sym, Qlt_not_eq.
  Qed.

  Lemma float_negative_implies_nonzero p (f : binary_float p) :
    f < 0  ->  ~(f == 0).
  Proof.
    intro; now apply Qlt_not_eq.
  Qed.

  Lemma float_negative_nonzero_is_nonzero p (f : binary_float p) :
    ~(f == 0) -> ~(-f == 0).
  Proof.
    unfold float_eq; destruct f; simpl; intro H; contradict H; rearrange.
  Qed.

  Variable p : positive.

  Let nonzero_float := { x : binary_float p | ~(x == 0) }.

  Definition float_is_positive (f : nonzero_float) :
    { 0 < proj1_sig f } + { proj1_sig f < 0 }.
  Proof.
    unfold float_lt; destruct f as [[q q_representable] x_nonzero];
    unfold float_eq in x_nonzero; destruct (Q_dec 0 q) as [[q1 | q2] | q3];
    [ left | right | contradict x_nonzero; symmetry]; easy.
  Defined.

  Definition next_up (f : nonzero_float) :
    nonzero_float.
  Proof.
    refine
      (
        if float_is_positive f
        then [_next_up_positive _ (proj1_sig f) _ ]
        else [- (_next_down_positive _ (-proj1_sig f) _)]
      ).
    - apply float_positive_implies_nonzero, next_up_positive_positive.
    - apply float_negative_nonzero_is_nonzero, float_positive_implies_nonzero,
      next_down_positive_positive.
    Grab Existential Variables.
    unfold float_lt in *. simpl in *. rearrange.
    easy.
  Defined.

  Lemma float_lt_neg_flip (f g : binary_float p) : f < -g  <->  g < -f.
  Proof.
    unfold float_lt; destruct f, g; simpl; split; intro; rearrange.
  Qed.

  Lemma float_neg_lt_flip (f g : binary_float p) : -f < g  <->  -g < f.
  Proof.
    unfold float_lt; destruct f, g; simpl; split; intro; rearrange.
  Qed.

  Lemma float_le_neg_flip (f g : binary_float p) : f <= -g  <->  g <= -f.
  Proof.
    unfold float_le; destruct f, g; simpl; split; intro; rearrange.
  Qed.

  Lemma float_neg_le_flip (f g : binary_float p) : -f <= g  <->  -g <= f.
  Proof.
    unfold float_le; destruct f, g; simpl; split; intro; rearrange.
  Qed.

  Lemma lt_next_up (f : nonzero_float) :
    proj1_sig f < proj1_sig (next_up f).
  Proof.
    unfold next_up.
    destruct (float_is_positive f).
    - apply lt_next_up_positive.
    - simpl.
      (* want to rearrange a < -b to b < -a *)
      apply float_lt_neg_flip.
      apply lt_next_down_positive.
  Qed.

  Theorem next_up_spec (f g : nonzero_float) :
    proj1_sig (next_up f) <= proj1_sig g  <->  proj1_sig f < proj1_sig g.
  Proof.
    split; intro.
    - apply float_lt_le_trans with (y := proj1_sig (next_up f)).
      + apply lt_next_up.
      + easy.
    - unfold next_up; destruct (float_is_positive f).
      + destruct (next_up_positive_is_next_up p (proj1_sig f) f0 (proj1_sig g)).
        assert (proj1_sig f < proj1_sig f).
        now apply float_lt_le_trans with (y := proj1_sig g).
        contradict H1.
        unfold float_lt.
        auto with qarith.
        easy.
      + simpl.
        assert (0 < -proj1_sig f) as H0.
        apply float_lt_neg_flip.
        easy.
        destruct (next_down_positive_is_next_down p (- proj1_sig f) H0 (- proj1_sig g)).
        * simpl.
          (* Case -g <= next_down (-f) *)
          apply float_neg_le_flip.
          match goal with
           | [ _ : ?lhs <= ?rhs1 |- ?lhs <= ?rhs2 ] => assert (rhs1 == rhs2)
          end.
          unfold float_eq. simpl.
          repeat f_equiv.
          setoid_rewrite <- H2.
          easy.
        * (* Case (-f) <= (-g) *)
          exfalso.
          assert (proj1_sig g <= proj1_sig f).
          setoid_replace (proj1_sig f) with (- - proj1_sig f).
          now apply float_le_neg_flip.
          unfold float_eq, float_opp.
          simpl.
          ring.
          assert (proj1_sig f < proj1_sig f).
          now apply float_lt_le_trans with (y := proj1_sig g).
          revert H3.
          unfold float_lt.
          generalize (proj1_sig (proj1_sig f)).
          intro q.
          change ((q < q)%Q -> False) with (~ (q < q)%Q).
          auto with qarith.
  Qed.

  (* Some basic properties. First, next_up is well-defined. *)

  Theorem next_up_morphism (f g : nonzero_float) :
    ' f == ' g  ->  ' next_up f == ' next_up g.
  Proof.
    intro; apply float_le_antisymm; apply next_up_spec;
    (rewrite H || rewrite <- H); apply next_up_spec;
    apply float_le_refl.
  Qed.

  (* And next_up preserves the sign of its input *)

  Theorem next_up_positive f : 0 < 'f -> 0 < ' next_up f.
  Proof.
    intro f_positive; apply float_lt_trans with (1 := f_positive).
    apply next_up_spec, float_le_refl.
  Qed.

  Theorem next_up_negative f : 'f < 0 -> ' next_up f < 0.
  Proof.
    unfold next_up; destruct (float_is_positive f); intro.
    - (* Case 0 < 'f < 0; contradiction *)
      assert (@float_lt p 0 0) by (now apply float_lt_trans with (y := ' f)).
      now contradict H0.
    - (* Case f' < 0. *)
      simpl.
      apply float_neg_lt_flip.
      apply next_down_positive_positive.
  Qed.

  (* Now we can also define next_down.  We could do this from first
     principles, but it's easier to define it in terms of next_up.

     We first define negation at the level of nonzero_float. *)

  Definition nonzero_float_neg (f : nonzero_float) : nonzero_float.
  Proof.
    refine [- 'f]; apply float_negative_nonzero_is_nonzero; now destruct f.
  Defined.

  Lemma nonzero_float_neg_neg (f : nonzero_float) :
    'nonzero_float_neg (nonzero_float_neg f) == 'f.
  Proof.
    unfold nonzero_float_neg, float_eq, float_opp; simpl; ring.
  Qed.

  Lemma nonzero_float_neg_lt_switch (f g : nonzero_float) :
    'nonzero_float_neg f < 'g  <->  'nonzero_float_neg g < 'f.
  Proof.
    unfold nonzero_float_neg, float_lt; simpl; split; intro; rearrange.
  Qed.

  Lemma nonzero_float_lt_neg_switch (f g : nonzero_float) :
    'f < 'nonzero_float_neg g  <->  'g < 'nonzero_float_neg f.
  Proof.
    unfold nonzero_float_neg, float_lt; simpl; split; intro; rearrange.
  Qed.

  Lemma nonzero_float_le_neg_switch (f g : nonzero_float) :
    'f <= 'nonzero_float_neg g  <->  'g <= 'nonzero_float_neg f.
  Proof.
    unfold nonzero_float_neg, float_le; simpl; split; intro; rearrange.
  Qed.

  Definition next_down (f : nonzero_float) : nonzero_float :=
    nonzero_float_neg (next_up (nonzero_float_neg f)).

  Lemma nonzero_float_neg_morphism (f g : nonzero_float) :
    'f == 'g ->  'nonzero_float_neg f == 'nonzero_float_neg g.
  Proof.
    intro H; unfold nonzero_float_neg; simpl; now rewrite H.
  Qed.

  Lemma nonzero_float_neg_positive_is_negative f :
    0 < 'f  -> 'nonzero_float_neg f < 0.
  Proof.
    unfold nonzero_float_neg, float_lt; simpl; intro; rearrange.
  Qed.

  Lemma nonzero_float_neg_negative_is_positive f :
    'f < 0  ->  0 < 'nonzero_float_neg f.
  Proof.
    unfold nonzero_float_neg, float_lt; simpl; intro; rearrange.
  Qed.

  Theorem next_down_morphism (f g : nonzero_float) :
    'f == 'g  ->  'next_down f == 'next_down g.
  Proof.
    unfold next_down; intro;
    now apply nonzero_float_neg_morphism, next_up_morphism,
        nonzero_float_neg_morphism.
  Qed.

  Theorem next_down_spec (f g : nonzero_float) :
    'f <= 'next_down g  <->   'f < 'g.
  Proof.
    unfold next_down.
    rewrite <- nonzero_float_neg_neg at 2.
    rewrite nonzero_float_neg_lt_switch.
    rewrite nonzero_float_le_neg_switch.
    apply next_up_spec.
  Qed.

  Theorem next_down_positive (f : nonzero_float) :
    0 < 'f  ->  0 < ' next_down f.
  Proof.
    unfold next_down; intro; now apply nonzero_float_neg_negative_is_positive,
                             next_up_negative, nonzero_float_neg_positive_is_negative.
  Qed.

  Theorem next_down_negative (f : nonzero_float) :
    'f < 0  ->  'next_down f < 0.
  Proof.
    unfold next_down; intro;
    now apply nonzero_float_neg_positive_is_negative,
    next_up_positive, nonzero_float_neg_negative_is_positive.
  Qed.

  (* Alternative versions of the specs of next_up and next_down. *)

  Lemma float_lt_nge (f g : binary_float p) : f < g  <->  ~(g <= f).
  Proof.
    apply Qlt_nge.
  Qed.

  Lemma float_le_ngt (f g : binary_float p) : f <= g  <->  ~(g < f).
  Proof.
    unfold float_le, float_lt.
    split; intro.
    now apply Qle_not_lt.
    now apply Qnot_lt_le.
  Qed.

  Theorem next_up_spec_alt (f g : nonzero_float) :
    'g < 'next_up f  <->  'g <= 'f.
  Proof.
    rewrite float_le_ngt, float_lt_nge; apply negate_iff, next_up_spec.
  Qed.

  Theorem next_down_spec_alt (f g : nonzero_float) :
    'next_down g < 'f  <->  'g <= 'f.
  Proof.
    rewrite float_le_ngt, float_lt_nge; apply negate_iff, next_down_spec.
  Qed.

  (* next_up and next_down are inverses of one another *)

  Theorem next_up_next_down f : ' next_up (next_down f) == ' f.
  Proof.
    apply float_le_antisymm.
    - apply next_up_spec, next_down_spec, float_le_refl.
    - apply next_down_spec_alt, next_up_spec_alt, float_le_refl.
  Qed.

  Theorem next_down_next_up f : ' next_down (next_up f) == 'f.
  Proof.
    apply float_le_antisymm.
    - apply next_up_spec_alt, next_down_spec_alt, float_le_refl.
    - apply next_down_spec, next_up_spec, float_le_refl.
  Qed.

  (* next_up and next_down are monotonic and injective. *)

  Theorem next_up_eq f g :
    'f == 'g  <->  'next_up f == 'next_up g.
  Proof.
    split; intro H.
    - apply float_le_antisymm; apply next_up_spec, next_up_spec_alt;
      rewrite H; apply float_le_refl.
    - apply float_le_antisymm; apply next_up_spec_alt, next_up_spec;
      rewrite H; apply float_le_refl.
  Qed.

  Theorem next_up_le f g :
    'f <= 'g  <->  'next_up f <= 'next_up g.
  Proof.
    split; intro.
    - now apply next_up_spec, next_up_spec_alt.
    - now apply next_up_spec_alt, next_up_spec.
  Qed.

  Theorem next_up_lt f g :
    'f < 'g  <->  'next_up f < 'next_up g.
  Proof.
    split; intro.
    - now apply next_up_spec_alt, next_up_spec.
    - now apply next_up_spec, next_up_spec_alt.
  Qed.

  Theorem next_down_eq f g :
    'f == 'g  <->  'next_down f == 'next_down g.
  Proof.
    split; intro H; apply float_le_antisymm;
    (apply next_down_spec, next_down_spec_alt
                             || apply next_down_spec_alt, next_down_spec);
    rewrite H; apply float_le_refl.
  Qed.

  Theorem next_down_le f g :
    'f <= 'g  <->  'next_down f <= 'next_down g.
  Proof.
    split; intro;
    (
      apply next_down_spec, next_down_spec_alt
      ||
      apply next_down_spec_alt, next_down_spec
    );
    easy.
  Qed.

  Theorem next_down_lt f g :
    'f < 'g  <->  'next_down f < 'next_down g.
  Proof.
    split; intro;
    (
      apply next_down_spec_alt, next_down_spec
      ||
      apply next_down_spec, next_down_spec_alt
    );
    easy.
  Qed.

End NextUpNextDown.
