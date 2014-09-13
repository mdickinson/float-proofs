(* Various rounding modes, expressed as functions from Q to Z. *)

Require Import ZArith.
Require Import QArith.

Require Import floor_and_ceiling.
Require Import twopower.
Require Import binade.


Section Representability.

(* We fix a floating-point precision p, which must be a positive integer. *)

Variable p : Z.
Hypothesis p_positive : (0 < p)%Z.

(* We say that an element of Q is representable with precision p if it
   can be expressed in the form m * 2**e for some integers m and e
   with abs(m) < 2**p. *)

Definition is_representable (x : Q) := exists (e m : Z),
  (Z.abs(m) < twopower_Z p)%Z  /\  x == (m # 1) * twopower_Q e. 

(* Clearly, 0 is representable. *)

Theorem zero_is_representable : is_representable 0.
Proof.
unfold is_representable. exists 0%Z. exists 0%Z.
split; simpl.
  apply twopower_positive. auto with zarith.
  ring.
Qed.

(* Now we can define the roundTowardNegative operation. *)

Section roundTowardNegative.

Variable x : Q.

(* First let's concentrate on the case where x is positive. *)

Hypothesis x_positive : x > 0.

(* Now 2^binade(x) <= x < 2^(binade(x) + 1).

   We want to scale so that 2^(p - 1) <= twopower (shift) * x < 2^p. *)

Let scale : Z := (p - 1 - binade_Q(x))%Z.
Let scaled_x := (twopower_Q scale) * x.

Lemma scaled_x_bound : twopower_Q (p - 1) <= scaled_x  /\  scaled_x < twopower_Q p.
Proof.
split.
unfold scaled_x.
(* multiply both sides by twopower_Q (-scale) *)
apply Qmult_le_l with (z := twopower_Q (-scale)%Z). apply twopower_positive_Q.
rewrite Qmult_assoc.
rewrite <- ?twopower_sum_Q.
replace (-scale + scale)%Z with 0%Z by ring.
unfold scale.
replace (- (p - 1 - binade_Q x) + (p - 1))%Z with (binade_Q x) by ring.
rewrite twopower_zero_Q.
rewrite Qmult_1_l.
apply twopower_binade_Q_counit. assumption.

unfold scaled_x.
apply Qmult_lt_l with (z := twopower_Q (-scale)%Z). apply twopower_positive_Q.
rewrite Qmult_assoc.
rewrite <- ?twopower_sum_Q.
replace (-scale + scale)%Z with 0%Z by ring.
unfold scale.
rewrite twopower_zero_Q.
rewrite Qmult_1_l.
replace (- (p - 1 - binade_Q x) + p)%Z with (binade_Q x + 1)%Z by ring.
apply twopower_binade_Q_counit2. assumption.
Qed.

(* pos subscript because we're only defining the operation for
   positive rationals at the moment. *)

Definition round_down_pos := twopower_Q scale * (floor (scaled_x) # 1).

Lemma round_down_result_is_representable : is_representable round_down_pos.
Proof.
  unfold is_representable.
  exists scale. exists (floor (scaled_x)).
  split.
    assert (0 <= floor scaled_x)%Z.
      apply floor_spec.
      replace (inject_Z 0) with 0 by reflexivity.
      unfold scaled_x.
      setoid_replace 0 with (0 * x) by ring.
      SearchAbout (_ * _ <= _ * _).
      apply Qmult_le_r. assumption.
      assert (0 < twopower_Q scale) by apply twopower_positive_Q.
      auto with qarith.

    rewrite Z.abs_eq.
    apply floor_spec_lt.
    unfold inject_Z.
    rewrite <- twopower_Z_Q.

    apply scaled_x_bound.
    auto with zarith. assumption.
    unfold round_down_pos. ring.
Qed.

End roundTowardNegative.
End Representability.
