(* Definitions of floor : Q -> Z and ceiling : Q -> Z, and key results.

   Also defines is_integer. *)

Require Import ZArith.
Require Import QArith.
Require Import Qabs.

Require Import remedial.
Require Import rearrange_tactic.

Local Open Scope Z.

(* The floor function can be defined in terms of the standard library
   / operator, which does Euclidean division with the appropriate
   semantics when the numerator is negative. *)

Definition floor q := (Qnum q / ' Qden q).

(* To prove the main specification theorem for floor, we first need
   to prove a corresponding theorem at integer level. *)

Lemma _floor_spec_Z a b n : 0 < b -> (n * b <= a  <->  n <= a / b).
Proof.
  intro; rewrite Z.mul_comm; split; intro.
  - now apply Z.div_le_lower_bound.
  - eapply Z.le_trans;
    ((apply Z.mul_le_mono_pos_l; eassumption) || now apply Z.mul_div_le).
Qed.

(* Now we can show that floor is an adjoint to the inclusion of Z into Q,
   a property which completely characterises the floor function. *)

Local Open Scope Q.

Theorem floor_spec q n : inject_Z n <= q  <->  (n <= floor q)%Z.
Proof.
  unfold Qle; rewrite Z.mul_1_r; apply _floor_spec_Z, Pos2Z.is_pos.
Qed.

(* It's easier to prove that "floor" is a setoid morphism
   using "floor_spec" than using the definition directly. *)

Add Parametric Morphism : floor
    with signature Qeq ==> eq as floor_morphism.
Proof.
  intros q r q_eq_r; apply Z.le_antisymm; apply floor_spec;
  [ rewrite <- q_eq_r | rewrite q_eq_r ]; apply floor_spec, Z.le_refl.
Qed.

(* Variant formulation of floor_spec in terms of < rather than <=. *)

Theorem floor_spec_lt q n : q < inject_Z n  <->  (floor q < n)%Z.
Proof.
  rewrite Z.lt_nge, Qlt_nge; apply negate_iff, floor_spec.
Qed.

(* It follows from the specification that floor is monotonic. *)

Theorem floor_monotonic q r : q <= r  ->  (floor q <= floor r)%Z.
Proof.
  intro q_le_r;
  apply floor_spec, Qle_trans with (2 := q_le_r), floor_spec, Z.le_refl.
Qed.

(* Define the ceiling function in terms of floor, and prove its characteristic
   properties. *)

Definition ceiling q := (- floor (- q))%Z.

Add Parametric Morphism : ceiling
    with signature Qeq ==> eq as ceiling_morphism.
Proof.
  intros q r q_eq_r; unfold ceiling; now rewrite q_eq_r.
Qed.

Theorem ceiling_spec q n : q <= inject_Z n  <->  (ceiling q <= n)%Z.
Proof.
  split; intro.
  - apply Zle_sign_flip_l, floor_spec;
    now rewrite inject_Z_opp, <- Qopp_le_mono.
  - rewrite Qopp_le_mono, <- inject_Z_opp;
    now apply floor_spec, Zle_sign_flip_l.
Qed.

Theorem ceiling_spec_lt q n : inject_Z n < q  <->  (n < ceiling q)%Z.
Proof.
  rewrite Z.lt_nge; rewrite Qlt_nge; apply negate_iff; apply ceiling_spec.
Qed.

Theorem ceiling_monotonic q r : q <= r  ->  (ceiling q <= ceiling r)%Z.
Proof.
  intro q_le_r;
  apply ceiling_spec, Qle_trans with (1 := q_le_r), ceiling_spec, Z.le_refl.
Qed.

(* Relationship between floor and ceiling. *)

Theorem neg_ceiling_is_floor_neg q : (- ceiling q)%Z = floor (-q).
Proof.
  apply Z.opp_involutive.
Qed.

Theorem neg_floor_is_ceiling_neg q : (- floor q)%Z = ceiling (-q).
Proof.
  unfold ceiling; now rewrite Qopp_opp.
Qed.

Theorem floor_ceiling_bound q : (ceiling q <= floor q + 1)%Z.
Proof.
  apply ceiling_spec, Qlt_le_weak, floor_spec_lt; omega.
Qed.

Theorem floor_le_ceiling q : (floor q <= ceiling q)%Z.
Proof.
  rewrite Zle_Qle; apply Qle_trans with (y := q).
  - apply floor_spec, Z.le_refl.
  - apply ceiling_spec, Z.le_refl.
Qed.


Definition is_integer (q : Q) : Prop :=
  exists n : Z, inject_Z n == q.

Add Morphism is_integer : is_integer_morphism.
Proof.
  unfold is_integer; split; intro H0; destruct H0 as [z H0]; exists z;
    now rewrite H0.
Qed.

Lemma is_integer_inject_Z (x : Z) : is_integer (inject_Z x).
Proof.
  now exists x.
Qed.

Lemma is_integer_neg (x : Q) : is_integer x -> is_integer (-x).
Proof.
  unfold is_integer; intro H; destruct H as [y H0]; exists (-y)%Z;
  rewrite inject_Z_opp; now rewrite H0.
Qed.

Lemma is_integer_add (x y : Q) :
  is_integer x -> is_integer y -> is_integer (x + y).
Proof.
  unfold is_integer; intros x_int y_int; destruct x_int as [x0 x_int];
  destruct y_int as [y0 y_int]; exists (x0 + y0)%Z; rewrite inject_Z_plus;
  rewrite x_int; now rewrite y_int.
Qed.

Lemma is_integer_sub (x y : Q) :
  is_integer x -> is_integer y -> is_integer (x - y).
Proof.
  intros; apply is_integer_add; [ | apply is_integer_neg]; easy.
Qed.

Lemma is_integer_mul (x y : Q) :
  is_integer x -> is_integer y -> is_integer (x * y).
Proof.
  unfold is_integer; intros x_int y_int; destruct x_int as [x0 x_int];
  destruct y_int as [y0 y_int]; exists (x0 * y0)%Z; rewrite inject_Z_mult;
  rewrite x_int; now rewrite y_int.
Qed.

Lemma small_integer_is_zero (x : Q) :
  is_integer x -> Qabs x < 1 -> x == 0.
Proof.
  destruct 1 as [n H]; rewrite <- H; clear H; rewrite Qabs_Zabs.
  setoid_replace 0 with (inject_Z 0) by easy;
  setoid_replace 1 with (inject_Z (Z.succ 0)) by easy;
  rewrite inject_Z_injective;
  rewrite <- Zlt_Qlt; intro;
  assert (-0 <= n <= 0)%Z by (now apply Z.abs_le, Z.lt_succ_r).
  apply Z.le_antisymm; easy.
Qed.

Lemma floor_integer (q : Q) : is_integer q <-> inject_Z (floor q) == q.
Proof.
  unfold is_integer; split.
  - destruct 1 as [n n_eq_q]; rewrite <- n_eq_q; apply Qle_antisym.
    + apply floor_spec, Z.le_refl.
    + rewrite <- Zle_Qle; apply floor_spec, Qle_refl.
  - intro; now exists (floor q).
Qed.

Lemma integer_le_floor (x y : Q) :
  is_integer x -> x <= y -> x <= inject_Z (floor y).
Proof.
  destruct 1 as [m H]; rewrite <- H; intro; rewrite <- Zle_Qle;
  now apply floor_spec.
Qed.

Lemma integer_le_ceiling (x y : Q) :
  is_integer y -> x <= y -> inject_Z (ceiling x) <= y.
Proof.
  destruct 1 as [m H]; rewrite <- H; intro; rewrite <- Zle_Qle;
  now apply ceiling_spec.
Qed.


Lemma ceiling_integer (q : Q) : is_integer q <-> inject_Z (ceiling q) == q.
Proof.
  unfold is_integer; split.
  - destruct 1 as [n n_eq_q]; rewrite <- n_eq_q; apply Qle_antisym.
    + rewrite <- Zle_Qle; apply ceiling_spec, Z.le_refl.
    + apply ceiling_spec, Z.le_refl.
  - intro; now exists (ceiling q).
Qed.

(* As a corollary of the above characterization of is_integer in terms of an
   equality, is_integer is decidable. *)

Lemma is_integer_is_decidable (q : Q) : is_integer q  \/  ~is_integer q.
Proof.
  destruct (Qeq_dec (inject_Z (floor q)) q) as [equal | notequal];
  [left | right; contradict notequal]; now apply floor_integer.
Qed.


Lemma floor_eq_ceiling (q : Q) :
  is_integer q <-> (floor q = ceiling q)%Z.
Proof.
  split.
  - intro; apply inject_Z_injective; transitivity q;
    [ apply floor_integer | symmetry; apply ceiling_integer ]; easy.
  - intro; apply floor_integer; apply Qle_antisym;
    [apply floor_spec | rewrite H ; apply ceiling_spec]; apply Zle_refl.
Qed.


Lemma floor_ceiling_gap (q : Q) :
  ~(is_integer q) -> (ceiling q = floor q + 1)%Z.
Proof.
  intro q_is_integer; apply Z.le_antisymm; [
  apply floor_ceiling_bound |
  apply Z.le_succ_l; apply Zle_not_eq; [ apply floor_le_ceiling |
  contradict q_is_integer; now apply floor_eq_ceiling]].
Qed.


Lemma floor_ceiling_gap_Q (q : Q) :
  ~is_integer q -> inject_Z (ceiling q) == inject_Z (floor q) + 1.
Proof.
  intro; replace 1 with (inject_Z 1) by reflexivity;
  rewrite <- inject_Z_plus; apply inject_Z_injective;
  now apply floor_ceiling_gap.
Qed.

(* Results about floor, ceiling and absolute value. *)

Lemma abs_floor_le (x : Q) (m : Z) :
  Qabs x <= inject_Z m  ->  (Z.abs (floor x) <= m)%Z.
Proof.
  intro abs_x_le_m; apply Z.abs_case; [
    solve_proper |
    (* Proving floor x <= m. *)
    rewrite Zle_Qle; apply Qle_trans with (y := x); [
      apply floor_spec, Zle_refl |
      now apply Qabs_Qle_condition ]
    |
    (* Proving - floor x <= m. *)
    rewrite neg_floor_is_ceiling_neg; apply ceiling_spec, Qabs_Qle_condition;
    now rewrite Qabs_opp
  ].
Qed.

Lemma abs_ceiling_le (x : Q) (m : Z) :
  Qabs x <= inject_Z m  ->  (Z.abs (ceiling x) <= m)%Z.
Proof.
  setoid_replace x with (- - x) by ring;
  rewrite Qabs_opp; rewrite <- neg_floor_is_ceiling_neg;
  rewrite Z.abs_opp; apply abs_floor_le.
Qed.

Lemma Qabs_floor_le x y :
  is_integer y  ->  Qabs x <= y  ->  Qabs (inject_Z (floor x)) <= y.
Proof.
  destruct 1 as [m m_eq_y]; rewrite <- m_eq_y;
  rewrite Qabs_Zabs; rewrite <- Zle_Qle; apply abs_floor_le.
Qed.

Lemma Qabs_ceiling_le x y :
  is_integer y  ->  Qabs x <= y  ->  Qabs (inject_Z (ceiling x)) <= y.
Proof.
  destruct 1 as [m m_eq_y]; rewrite <- m_eq_y;
  rewrite Qabs_Zabs; rewrite <- Zle_Qle; apply abs_ceiling_le.
Qed.
