Require Import ZArith.
Require Import QArith.

Require Import floor_and_ceiling.
Require Import twopower.
Require Import binade.


(* Auxiliary lemmas about Q. *)

Lemma Q_sign_flip : forall q r : Q, -q <= r  ->  -r <= q.
Proof.
  intros; apply Qplus_le_r with (z := r - q); now ring_simplify.
Qed.

Lemma Q_sign_flip_r : forall q r : Q, q <= -r  ->  r <= -q.
Proof.
  intros; apply Qplus_le_r with (z := q - r); now ring_simplify.
Qed.

Lemma Q_sign_flip_lt_r : forall q r : Q, q < -r  ->  r < -q.
Proof.
  intros; apply Qplus_lt_r with (z := q - r); now ring_simplify.
Qed.



Lemma div_mult_le_l : forall a b c, 0 < b -> a <= c * b -> a / b <= c.
Proof.
  intros.
  apply Qmult_le_r with (z := b). assumption.
  setoid_replace (a / b * b) with a.
  assumption.
  field.
  auto with qarith.
Qed.

Lemma div_mult_lt_l : forall a b c, 0 < b -> a < c * b -> a / b < c.
Proof.
  intros.
  apply Qmult_lt_r with (z := b). assumption.
  setoid_replace (a / b * b) with a.
  assumption.
  field.
  auto with qarith.
Qed.

Lemma div_mult_le_r : forall a b c, 0 < b -> a * b <= c -> a <= c / b.
Proof.
  intros.
  apply Qmult_le_r with (z := b). assumption.
  setoid_replace (c / b * b) with c by (field; auto with qarith).
  assumption.
Qed.
  
Lemma div_mult_lt_r : forall a b c, 0 < b ->  a * b < c ->  a < c / b.
Proof.
  intros.
  apply Qmult_lt_r with (z := b). assumption.
  setoid_replace (c / b * b) with c by (field; auto with qarith).
  assumption.
Qed.


Section DefinitionOfFloat.

Variable precision : Z.
Hypothesis precision_is_nonnegative : (0 <= precision)%Z.

(* Record describing finite floating-point numbers with precision p. *)

Record float : Set := mkFloat {
  negative : bool;
  significand : Z;
  exponent : Z;
  significand_bound : (0 <= significand < twopower_Z precision)%Z
}.

(* Value of a float, as a rational number. *)

Definition value (x : float) : Q :=
  match negative x with
  | true => -(inject_Z (significand x) * twopower_Q (exponent x))
  | false => inject_Z (significand x) * twopower_Q (exponent x)
  end.

Lemma zero_in_bounds : 0 <= 0 < twopower_Z precision.
Proof.
  split. auto with zarith. apply twopower_positive. auto with zarith.
Qed.

Definition positive_zero : float :=
  mkFloat false 0 0 zero_in_bounds.

Definition negative_zero : float :=
  mkFloat true 0 0 zero_in_bounds.

End DefinitionOfFloat.
Arguments value [precision] x.

Section RoundingFromQ.

(* In this section we define various functions Q -> float precision.  First
   let's set a precision. *)

Variable precision : Z.
Hypothesis precision_is_positive : (0 < precision)%Z.

(* Each of our rounding functions is based on a function from Q -> Z;
   for example, floor, ceiling, round. *)

Variable rounding_method : Q -> Z.

(* We assume that our rounding method always rounds to either
   the floor or the ceiling. *)

Hypothesis rounding_method_rounds : forall q : Q,
  (floor q <= rounding_method q <= ceiling q)%Z.

(* Define first a function that rounds to a particular exponent, returning
   the appropriate significand for that exponent *)

Definition round_to_exponent (exponent : Z) (q : Q) : Z :=
  rounding_method (q / twopower_Q exponent).

(* And another function to *choose* the exponent for a particular input. *)

Definition exponent_choice (q : Q) : Z :=
  match 0 ?= q with
  | Eq => 0%Z
  | Lt => (binade_Q q - precision + 1)%Z
  | Gt => (binade_Q (-q) - precision + 1)%Z
  end.

(* The exponent above is chosen so that the resulting significand is within
   the correct range. *)

Lemma significand_in_range : forall q,
  ((- twopower_Z precision) <= round_to_exponent (exponent_choice q) q
                           <= twopower_Z precision)%Z.
Proof.
  intro.
  split.
  (* Subgoal 1: proving that - 2**precision <= ... *)
  unfold round_to_exponent.
  apply Z.le_trans with (m := floor (q / twopower_Q (exponent_choice q))).
  apply floor_spec.
  rewrite inject_Z_opp.
  rewrite <- twopower_Z_Q_compat.
  apply div_mult_le_r. apply twopower_positive_Q.
  setoid_replace (- twopower_Q precision * twopower_Q (exponent_choice q))
     with (- (twopower_Q precision * twopower_Q (exponent_choice q)))
     by ring.
  apply Q_sign_flip.
  rewrite <- twopower_sum_Q.
  unfold exponent_choice.
  case_eq (0 ?= q); intro H; [apply Qeq_alt in H | apply Qlt_alt in H | apply Qgt_alt in H].
  rewrite <- H.
  ring_simplify.
  apply Qlt_le_weak.
  apply twopower_positive_Q.

  apply Qle_trans with (y := 0).
  apply Q_sign_flip. ring_simplify.
  now apply Qlt_le_weak.
  apply Qlt_le_weak. apply twopower_positive_Q.
  apply Qlt_le_weak.
  
  apply twopower_Q_binade_adjunction_lt.
  apply Q_sign_flip_lt_r.
  now ring_simplify.

  omega.
  omega.

  apply rounding_method_rounds.

  (* Subgoal 2: proving that ... <= 2**precision. *)
  unfold round_to_exponent.
  apply Z.le_trans with (m := ceiling (q / twopower_Q (exponent_choice q))).
  apply rounding_method_rounds.

  apply ceiling_spec.
  rewrite <- twopower_Z_Q_compat.
  apply div_mult_le_l.
  apply twopower_positive_Q.
  rewrite <- twopower_sum_Q.
  unfold exponent_choice.
  case_eq (0 ?= q); intro H; [apply Qeq_alt in H | apply Qlt_alt in H | apply Qgt_alt in H].
  rewrite <- H.
  apply Qlt_le_weak. apply twopower_positive_Q.

  apply Qlt_le_weak.
  apply twopower_Q_binade_adjunction_lt.  easy.
  omega.

  apply Qle_trans with (y := 0).  now apply Qlt_le_weak.
  apply Qlt_le_weak.  apply twopower_positive_Q.
  omega.
Qed.


End RoundingFromQ.  

Section FloatFromSignificandAndExponent.

Open Scope Z.

Variable precision : Z.
Hypothesis precision_is_positive : 0 < precision.

Variable significand : Z.
Variable exponent : Z.

Hypothesis significand_bound : Z.abs significand <= twopower_Z precision.

Locate "<=?".

Let sign := significand <? 0.
Let final_exponent := 
  if Z.abs significand <? twopower_Z precision
  then exponent
  else exponent + 1.
Let final_significand :=
  if Z.abs significand <? twopower_Z precision
  then Z.abs significand
  else Z.abs significand / 2.

Lemma final_significand_is_within_bounds : 0 <= final_significand < twopower_Z precision.
Proof.
  unfold final_significand; split; case_eq (Z.abs significand <? twopower_Z precision); intro.
    (* Showing 0 <= stuff. *)
    apply Z.abs_nonneg.
    apply floor_spec_Z; [ now compute | simpl; apply Z.abs_nonneg].
    (* Showing stuff < twopower_Z precision *)
    now rewrite Z.ltb_lt in H.
    rewrite Z.ltb_ge in H.
    SearchAbout (_ / _ < _).
    apply floor_spec_Z_lt; [now compute | ].
    eapply Z.le_lt_trans.
    apply significand_bound.
    SearchAbout (_ + _ < _ + _).
    apply Z.add_lt_mono_l with (p := - (twopower_Z precision)).
    ring_simplify.
    apply twopower_positive. omega.        
Qed.

Definition float_from_significand_and_exponent := 
  mkFloat precision sign final_significand final_exponent
          final_significand_is_within_bounds.


End FloatFromSignificandAndExponent.

Check float_from_significand_and_exponent.
