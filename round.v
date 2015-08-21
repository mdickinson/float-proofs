(* Definition of round_to_nearest : Q -> Z, rounding ties to even. *)

Set Implicit Arguments.

Require Import Qabs.

Require Import remedial.
Require Import rearrange_tactic.
Require Import floor_and_ceiling.

(* We're going to be defining round by cases, according to whether the
   fractional part of its input is 0 or nonzero and less than, equal to, or
   greater than 1/2.  We'll define a type "ExcessClass" for the classification
   of the fractional part, and a function "excess_class" which classifies the
   fractional part of its input. *)

Definition excess (q : Q) := q - inject_Z (floor q).

Inductive ExcessClass : Set := Exact | Low | Tie | High.

Definition excess_class (q : Q) : ExcessClass :=
  let f := excess q in
  if (Qle_dec (1#2) f) then
    if (Qeq_dec (1#2) f) then Tie else High
  else
    if (Qeq_dec 0 f) then Exact else Low.

(* Some examples. *)

Example excess_class_example_exact : excess_class (3#1) = Exact := eq_refl.
Example excess_class_example_high : excess_class (-7#3) = High := eq_refl.
Example excess_class_example_tie : excess_class (7#2) = Tie := eq_refl.
Example excess_class_example_low : excess_class (30#7) = Low := eq_refl.

(* Some basic results about the excess function. *)

Add Morphism excess : excess_morphism.
Proof.
  intros x y x_eq_y; unfold excess; now rewrite x_eq_y.
Qed.

Lemma excess_nonnegative (q : Q) : 0 <= excess q.
Proof.
  unfold excess; rearrange_goal (inject_Z (floor q) <= q);
  apply floor_spec, Z.le_refl.
Qed.

Lemma ceiling_excess_nonpositive (q : Q) : q - inject_Z (ceiling q) <= 0.
Proof.
  rearrange_goal (q <= inject_Z (ceiling q)).
  apply ceiling_spec, Z.le_refl.
Qed.

(* The following tactic is helpful in proving statments involving
   excess_class: it divides into the 4 possible cases. *)

Ltac destruct_excess_class :=
  match goal with
  | [ |- context[excess_class ?x]] =>
    unfold excess_class at 1; cbv zeta;
    (destruct (Qle_dec (1#2) (excess x));
     [destruct (Qeq_dec (1#2) (excess x)) | destruct (Qeq_dec 0 (excess x))]);
    try congruence
  end.

(* Now we can define the round function. *)

Definition round (q : Q) : Z :=
  match excess_class q with
  | Exact => floor q
  | Low => floor q
  | Tie => if Zeven_dec (floor q) then floor q else ceiling q
  | High => ceiling q
  end.

(* Some examples. *)

Example round_down : round (10#7) = 1%Z := eq_refl.
Example round_up : round (37#8) = 5%Z := eq_refl.
Example round_tie_down : round (5#2) = 2%Z := eq_refl.
Example round_tie_up : round (7#2) = 4%Z := eq_refl.

(* A useful tactic for proving statements involving round:
   it unfolds the round definition and divides into the 5
   cases. *)

Ltac destruct_round :=
  match goal with
  | [ |- context[round ?x]] =>
    unfold round at 1; (case_eq (excess_class x); intro;
                   [ | | destruct (Zeven_dec (floor x)) | ])
  end.

(* excess_class and round are setoid morphisms *)

Add Morphism excess_class : excess_class_morphism.
Proof.
  intros x y x_eq_y; repeat destruct_excess_class; now rewrite x_eq_y in *.
Qed.

Add Morphism round : round_morphism.
Proof.
  intros x y x_eq_y; repeat destruct_round; rewrite x_eq_y in *; congruence.
Qed.


Lemma floor_diff_nonnegative q :
  Qabs (q - inject_Z (floor q)) == q - inject_Z (floor q).
Proof.
  apply Qabs_pos, excess_nonnegative.
Qed.

Lemma ceiling_diff_nonnegative q :
  Qabs (q - inject_Z (ceiling q)) == inject_Z (ceiling q) - q.
Proof.
  rewrite Qabs_neg; [ring | apply ceiling_excess_nonpositive ].
Qed.

Lemma floor_ceiling_gap q :
  0 < excess q -> inject_Z (ceiling q) == inject_Z (floor q) + 1.
Proof.
  unfold excess; intro excess_positive;
  setoid_replace (inject_Z (floor q) + 1) with (inject_Z (floor q + 1)%Z) by (
    now rewrite inject_Z_plus);
  apply inject_Z_injective; apply Z.le_antisymm.
  - apply ceiling_spec, Qlt_le_weak, floor_spec_lt; omega.
  - apply Z.le_succ_l, ceiling_spec_lt; rearrange.
Qed.

Lemma floor_ceiling_equal q :
  excess q == 0 -> inject_Z (ceiling q) == inject_Z (floor q).
Proof.
  unfold excess; intro; transitivity q.
  - apply ceilingQ_eq;
    setoid_replace q with (inject_Z (floor q)) by rearrange;
    apply is_integer_inject_Z.
  - rearrange.
Qed.    

Lemma exact_floor q : excess_class q = Exact -> q - inject_Z (floor q) == 0.
Proof.
  destruct_excess_class; intros _; unfold excess in *; rearrange.
Qed.

Lemma exact_ceiling q :
  excess_class q = Exact -> inject_Z (ceiling q) - q == 0.
Proof.
  destruct_excess_class; intros _;
  rewrite floor_ceiling_equal; [ unfold excess in * | ]; rearrange.
Qed.

Lemma low_floor q : excess_class q = Low -> q - inject_Z (floor q) < 1#2.
Proof.
  destruct_excess_class; try intros _; unfold excess in *;
  rewrite <- Qlt_nge in n; rearrange.
Qed.

Lemma low_ceiling q : excess_class q = Low -> 1#2 < inject_Z (ceiling q) - q.
Proof.
  destruct_excess_class; intros _; rewrite floor_ceiling_gap.
  - rewrite <- Qlt_nge in *; unfold excess in *; rearrange.
  - apply Qle_not_eq; [apply excess_nonnegative | easy].
Qed.

Lemma tie_floor q : excess_class q = Tie -> q - inject_Z (floor q) == 1#2.
Proof.
  destruct_excess_class; intros _; unfold excess in *; rearrange.
Qed.

Lemma tie_ceiling q : excess_class q = Tie -> inject_Z (ceiling q) - q == 1#2.
Proof.
  destruct_excess_class; intros _; rewrite floor_ceiling_gap.
  - unfold excess in *; rearrange.
  - now apply Qlt_le_trans with (y := 1#2).
Qed.

Lemma high_floor q : excess_class q = High -> 1#2 < q - inject_Z (floor q).
Proof.
  destruct_excess_class; intros _; unfold excess in *; now apply Qle_not_eq.
Qed.

Lemma high_ceiling q : excess_class q = High -> inject_Z (ceiling q) - q < 1#2.
Proof.
  destruct_excess_class; intros _; rewrite floor_ceiling_gap.
  - assert (1#2 < excess q) by (now apply Qle_not_eq);
    unfold excess in *; rearrange.
  - now apply Qlt_le_trans with (y := 1#2).
Qed.


Theorem round_as_close_as_ceiling (q : Q) :
  Qabs (q - inject_Z (round q)) <= Qabs (q - inject_Z (ceiling q)).
Proof.
  destruct_round; try apply Qle_refl; rewrite floor_diff_nonnegative;
  rewrite ceiling_diff_nonnegative.
  - (* Case Exact *)
    now rewrite exact_ceiling, exact_floor.
  - (* Case Low. *)
    apply Qle_trans with (y := 1#2); apply Qlt_le_weak;
    [ apply low_floor | apply low_ceiling ]; easy.
  - (* Case Tie. *)
    apply Qle_trans with (y := 1#2);
    [ rewrite tie_floor | rewrite tie_ceiling ]; easy.
Qed.

Theorem round_as_close_as_floor (q : Q) :
  Qabs (q - inject_Z (round q)) <= Qabs (q - inject_Z (floor q)).
Proof.
  destruct_round; try apply Qle_refl; rewrite floor_diff_nonnegative;
  rewrite ceiling_diff_nonnegative.
  - (* Case Tie. *)
    apply Qle_trans with (y := 1#2);
    [rewrite tie_ceiling | rewrite tie_floor ]; easy.
  - (* Case High. *)
    apply Qle_trans with (y := 1#2); apply Qlt_le_weak;
    [ apply high_ceiling | apply high_floor ]; easy.
Qed.

(* Results about round and absolute value. *)

Lemma Qabs_round_le x y :
  is_integer y  ->  Qabs x <= y  ->  Qabs (inject_Z (round x)) <= y.
Proof.
  destruct_round; (apply Qabs_floor_le || apply Qabs_ceiling_le).
Qed.

Theorem floor_le_round (q : Q) : (floor q <= round q)%Z.
Proof.
  rewrite Zle_Qle;
  rearrange_goal (q - inject_Z (round q) <= q - inject_Z (floor q));
  rewrite <- (Qabs_pos (q - inject_Z (floor q))).
  - apply Qle_trans with (1 := Qle_Qabs _), round_as_close_as_floor.
  - rearrange_goal (inject_Z (floor q) <= q);
    apply floor_spec, Zle_refl.
Qed.

Theorem round_le_ceiling (q : Q) : (round q <= ceiling q)%Z.
Proof.
  rewrite Zle_Qle;
  rearrange_goal (- (q - inject_Z (round q)) <= - (q - inject_Z (ceiling q)));
  rewrite <- (Qabs_neg (q - inject_Z (ceiling q))).
  - apply Qle_trans with (1 := Qle_Qabs_neg _), round_as_close_as_ceiling.
  - rearrange_goal (q <= inject_Z (ceiling q)); apply ceiling_spec, Z.le_refl.
Qed.
