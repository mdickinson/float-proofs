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

Lemma mult_div_le_r : forall a b c, 0 < b -> a <= c / b -> a * b <= c.
Proof.
  intros.
  apply Qmult_le_r with (z := 1 / b).
  now apply div_mult_lt_r.
  field_simplify. field_simplify in H0. easy.
  revert H. rewrite H0. now compute.
  contradict H. rewrite H. now compute.
  contradict H. rewrite H. now compute.
Qed.

Section DefinitionOfFloat.

Open Scope Z.

(* 

We use a fairly simple definition of binary floats, with no exponent bounds,
and avoiding complications like signed zeros, infinities and NaNs.

Strictly speaking, for a given precision the significand should be *strictly*
smaller than "twopower precision", but for positive precision and unbounded
exponent it makes little difference if we allow the significand to equal
"twopower precision" in absolute value, and it'll be convenient when
defining rounding from Q to float.

*)

(* First we need a precision.  While we *could* define floats with
   a precision of zero (then 0 would be the only representable number),
   it's not terribly interesting to do so, and following results
   break down in that case.  So our precisions are all positive. *)

Variable precision : positive.

Definition within_bounds significand := Z.abs significand <= twopower_Z ('precision).

Record float : Set := mkFloat {
  exponent : Z;
  significand : Z;
  significand_bound : within_bounds significand
}.

(* Let's define zero as a float. *)

Lemma zero_within_bounds : within_bounds 0.
Proof.
  unfold within_bounds.
  simpl.
  apply Z.lt_le_incl.
  apply twopower_positive.
  auto with zarith.
Qed.

Definition zero_float := {|
  exponent := 0;
  significand := 0;
  significand_bound := zero_within_bounds
|}.

End DefinitionOfFloat.

Arguments exponent [precision] f.
Arguments significand [precision] f.
Arguments significand_bound [precision] _ _.


Section ValueOfAFloat.

Open Scope Q.

Definition value (precision : positive) (x : float precision) : Q :=
  inject_Z (significand x) * twopower_Q (exponent x).

End ValueOfAFloat.

Arguments value [precision] _.


Lemma value_zero : forall precision : positive, value (zero_float precision) == 0.
Proof.
  intros. unfold zero_float. unfold value. now compute.
Qed.

(* A tactic that destructs a Qcompare comparison, and puts the corresponding
   inequalities or equalities into the hypotheses for each branch of
   the comparison. *)

Ltac destruct_compare t :=
  match t with
  | Qcompare ?p ?q  => (let x := fresh in
    case_eq (Qcompare p q); intro x;
    [apply Qeq_alt in x | apply Qlt_alt in x | apply Qgt_alt in x])
  end.

Section RoundingFromQ.

(* In this section we define various functions Q -> float precision.  First
   let's set a precision. *)

Variable precision : positive.

(* Each of our rounding functions is based on a function from Q -> Z;
   for example, floor, ceiling, round. *)

Variable rounding_method : Q -> Z.

(* We'll need to assume that our rounding method is well-defined. *)

Hypothesis rounding_method_well_defined: forall q r : Q, q == r  -> rounding_method q = rounding_method r.

Print Instances Proper.

(* We assume that our rounding method always rounds to either
   the floor or the ceiling. *)

Hypothesis rounding_method_rounds : forall q : Q,
  (floor q <= rounding_method q <= ceiling q)%Z.

Definition exponent_choice (q : Q) : Z :=
  match 0 ?= q with
  | Eq => 0%Z
  | Lt => (binade_Q q - 'precision + 1)%Z
  | Gt => (binade_Q (-q) - 'precision + 1)%Z
  end.

Definition round_to_exponent (exponent : Z) (q : Q) : Z :=
  rounding_method (q / twopower_Q exponent).

Lemma significand_within_bounds (q : Q) :
  let exp := exponent_choice q in
  let sig := round_to_exponent exp q in
  (Z.abs sig <= twopower_Z ('precision))%Z.

Proof.
  intros.
  apply Z.abs_le.
  split.

  apply Z.opp_le_mono; rewrite Z.opp_involutive.
  unfold sig. unfold round_to_exponent.
  apply Z.le_trans with (m := (- floor (q / twopower_Q exp))%Z).
  apply Z.opp_le_mono.
  rewrite ?Z.opp_involutive.
  apply rounding_method_rounds.
  rewrite neg_floor_is_ceiling_neg.
  apply ceiling_spec.
  rewrite <- twopower_Z_Q_compat.
  setoid_replace (- (q / twopower_Q exp)) with ((-q) / twopower_Q exp) by field.
  apply div_mult_le_l.
  apply twopower_positive_Q.
  rewrite <- twopower_sum_Q.
  unfold exp. unfold exponent_choice.
  destruct_compare (0 ?= q).
  rewrite <- H. ring_simplify.
  apply Qlt_le_weak; apply twopower_positive_Q.

  apply Qle_trans with (y := 0).
  apply Q_sign_flip. ring_simplify. auto with qarith.
 
  apply Qlt_le_weak; apply twopower_positive_Q.
  apply Qlt_le_weak.
  apply twopower_Q_binade_adjunction_lt.
  apply Q_sign_flip_lt_r. easy.

  ring_simplify. omega.
  intro. symmetry in H. revert H.

  apply Qlt_not_eq. apply twopower_positive_Q.
  auto with zarith.

  (* Second half of the proof. *)
  unfold sig; unfold round_to_exponent.
  apply Z.le_trans with (m := ceiling (q / twopower_Q exp)).
  apply rounding_method_rounds.
  apply ceiling_spec.
  rewrite <- twopower_Z_Q_compat.
  SearchAbout (_ / _ <= _).
  apply div_mult_le_l. apply twopower_positive_Q.
  rewrite <- twopower_sum_Q.
  SearchAbout (_ <= twopower_Q _).
  apply Qlt_le_weak.
  SearchAbout (_ < twopower_Q _).
  unfold exp; unfold exponent_choice.
  destruct_compare (0 ?= q).
  rewrite <- H. apply twopower_positive_Q.
  apply twopower_Q_binade_adjunction_lt. easy.
  omega.
  apply Qlt_trans with (y := 0). easy. apply twopower_positive_Q.
  auto with zarith.
Qed.


Definition rounded (q : Q) : float precision
 :=
  let exp := exponent_choice q in
  {|
    exponent := exp;
    significand := round_to_exponent exp q;
    significand_bound := significand_within_bounds q
  |}.

End RoundingFromQ.

Check rounded.

Lemma floor_rounds : forall q : Q, (floor q <= floor q <= ceiling q)%Z.
Proof.
  intros. split. apply Z.le_refl. apply floor_le_ceiling.
Qed.

Lemma ceiling_rounds : forall q : Q, (floor q <= ceiling q <= ceiling q)%Z.
Proof.
  intros. split. apply floor_le_ceiling. apply Z.le_refl.
Qed.

Definition round_down (precision : positive) :=
  rounded precision floor floor_rounds.

Definition round_up precision :=
  rounded precision ceiling ceiling_rounds.

(* A few tests, to verify that these rounding operations are doing what we expect. *)

Example round_down_1 : value (round_down 3 (5#6)) == (6#8).
Proof.
  now compute.
Qed.

Example round_down_2 : value (round_down 3 (-5 # 6)) == -7 # 8.
Proof.
  now compute.
Qed.

Example round_down_3 : value (round_down 3 0) == 0.
Proof.
  now compute.
Qed.

Example round_up_1 : value (round_up 3 (5#6)) == (7#8).
Proof.
  now compute.
Qed.

Example round_up_2 : value (round_up 3 (-5 # 6)) == -6 # 8.
Proof.
  now compute.
Qed.

Example round_up_3 : value (round_up 3 0) == 0.
Proof.
  now compute.
Qed.

(* round_down should always round down! *)

Add Morphism (round_to_exponent floor) : round_to_exponent_floor.
  intros. unfold round_to_exponent. now rewrite H.
Qed.

Lemma round_down_le : forall precision q,
  value (round_down precision q) <= q.
Proof.
  intros.
  unfold round_down. unfold rounded. unfold value. simpl.
  unfold exponent_choice. destruct_compare (0 ?= q).
  (* Case 0 == q. *)
  rewrite <- H; now compute.
  (* Case 0 < q. *)
  apply mult_div_le_r.
  apply twopower_positive_Q.
  apply floor_spec.
  apply Z.le_refl.
  (* Case q < 0. *)
  apply mult_div_le_r.
  apply twopower_positive_Q.
  apply floor_spec.
  apply Z.le_refl.
Qed.


  

