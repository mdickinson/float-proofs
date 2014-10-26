(**

* Powers of two

In this section we introduce definitions and basic properties
for powers of two.

*)

Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import QOrderedType.
Require Import qpos.

(**

First we want to define powers of two as a function
from nonnegative integers to integers.  There's already
a [Z.pow] operation in the standard library, but it's
defined for negative exponents as well as positive.
We'd like something that can only be used for positive
exponents.  Rather than reinventing the wheel, let's
see if we can make use of the existing positive and N types.

*)

Open Scope N.

Definition N_to_pos (n : N) := Z.to_pos (Z.of_N n).

Lemma N_to_pos_to_N : forall n : N,
  0 < n  ->  Npos (N_to_pos n) = n.
Proof.
  intros; unfold N_to_pos; apply N2Z.inj; rewrite N2Z.inj_pos;
  rewrite Z2Pos.id; [ | rewrite <- N2Z.inj_0; apply N2Z.inj_lt ]; easy.
Qed.

Definition exptwo (n : N) : positive := N_to_pos (2^n)%N.

Lemma exptwo_spec : forall n, Npos (exptwo n) = 2^n.
Proof.
  intros; unfold exptwo; apply N_to_pos_to_N; apply N.neq_0_lt_0;
  apply N.pow_nonzero; now compute.
Qed.

Open Scope Q.

Lemma nonzero_and_nonneg_implies_positive: forall q : Q,
   ~ q == 0  ->  q >= 0  ->  q > 0.
Proof.
  auto with qarith.
Qed.

Lemma Q_div_pos_pos : forall p q : Q, (0 < p -> 0 < q -> 0 < p / q)%Q.
Proof.
  intros p q p_positive q_positive; apply Q_mul_pos_pos;
  try apply Qinv_lt_0_compat; easy.
Qed.


Lemma two_to_the_power_n_is_nonzero : forall n: Z, (~ (inject_Z 2)^n == 0)%Q.
Proof.
  intro n; destruct n; simpl; try (rewrite <- Qinv_power_positive);
  try (apply Qpower_not_0_positive); discriminate.
Qed.

Lemma two_to_the_power_n_is_positive : forall n : Z, (0 < inject_Z 2 ^ n)%Q.
Proof.
  intros.
  apply nonzero_and_nonneg_implies_positive.
  apply two_to_the_power_n_is_nonzero.
  apply Qpower_pos.
  discriminate.
Qed.

Open Scope QPos.

Definition twopower (n : Z) : QPos.
  refine (exist _ (inject_Z 2 ^ n)%Q _).
  apply two_to_the_power_n_is_positive.
Defined.

(* Now let's define the binade of a positive rational. *)

Definition QPos_num (q : QPos) := Z.to_pos (Qnum (proj1_sig q)).
Definition QPos_den (q : QPos) := Qden (proj1_sig q).

(* Creation of a positive rational from a positive integer. *)

Definition QPos_from_pos (p : positive) : QPos.
  refine (exist _ (inject_Z (' p)) _); apply Pos2Z.is_pos.
Defined.

(* Multiplication and division for positive rationals. *)

Lemma QPos_num_positive (q : Q) : (0 < q)%Q -> ('Z.to_pos (Qnum q) = Qnum q)%Z.
Proof.
  intros q_positive; apply Z2Pos.id; revert q_positive;
  unfold Qlt; now rewrite Z.mul_1_r.
Qed.

Lemma Q_as_fraction (q : Q) : (inject_Z (Qnum q) / inject_Z (' Qden q) == q)%Q.
Proof.
  unfold Qeq; simpl; ring.
Qed.

Lemma num_over_den : forall q : QPos,
  QPos_from_pos (QPos_num q) / QPos_from_pos (QPos_den q) == q.
Proof.
  intro q. destruct q.
  unfold QPos.eq, QPos.div, QPos_num, QPos_den. simpl.
  rewrite QPos_num_positive; [ | easy].
  apply Q_as_fraction.
Qed.

Lemma twopower_compat : forall p, twopower (' p) == QPos_from_pos (2^p).
Proof.
  intro p. unfold QPos.eq. simpl.
  rewrite Pos2Z.inj_pow.
  rewrite Zpower_Qpower. reflexivity.
  auto with zarith.
Qed.


Instance QPos_Setoid : Equivalence QPos.eq.
Proof.
  split; unfold QPos.eq; intro; [reflexivity | now symmetry |
    intros y z; now transitivity (proj1_sig y)].
Qed.

Add Morphism QPos.lt : QPos_lt_morphism.
Proof.
  unfold QPos.lt, QPos.eq.
  destruct x, y. simpl. intro.
  destruct x1, y0. simpl. intro.
  rewrite H. rewrite H0. reflexivity.
Qed.

Add Morphism QPos.le : QPos_le_morphism.
Proof.
  unfold QPos.le, QPos.eq.
  destruct x, y. simpl. intro.
  destruct x1, y0. simpl. intro.
  rewrite H. rewrite H0. reflexivity.
Qed.

Add Morphism QPos.mul : QPos_mul_morphism.
  unfold QPos.eq; simpl; intros; rewrite H; now rewrite H0.
Qed.

Add Morphism QPos.div : QPos_div_morphism.
  unfold QPos.eq; simpl; intros; rewrite H; now rewrite H0.
Qed.


Lemma QPos_from_pos_lt : forall p q, (p < q)%positive  -> QPos_from_pos p < QPos_from_pos q.
Proof.
  intros; unfold QPos.lt; simpl; rewrite <- Zlt_Qlt; unfold Zlt;
  now apply Pos.compare_lt_iff.
Qed.

Lemma QPos_from_pos_le : forall p q, (p <= q)%positive ->
  QPos_from_pos p <= QPos_from_pos q.
Proof.
  intros. unfold QPos.le. simpl. rewrite <- Zle_Qle. unfold Zle.
  now apply Pos.compare_le_iff.
Qed.

Lemma twopower_mul : forall p q : Z, twopower (p + q) == (twopower p) * (twopower q).
Proof.
  unfold QPos.eq, twopower; intros; now apply Qpower_plus.
Qed.

Lemma QPos_mul_inv_l p : /p * p == 1.
Proof.
  rewrite QPos.mul_comm. apply QPos.mul_inv_r.
Qed.

Lemma QPos_div_mul b c : b / c * c == b.
Proof.
  unfold QPos.div.
  rewrite <- QPos.mul_assoc. rewrite QPos_mul_inv_l.
  apply QPos.mul_1_r.
Qed.

Lemma QPos_mul_div b c : b * c / c == b.
Proof.
  unfold QPos.div.
  rewrite <- QPos.mul_assoc.
  rewrite QPos.mul_inv_r.
  apply QPos.mul_1_r.
Qed.

Lemma QPos_div_mul_r a b c : a == b / c  <->  a * c == b.
  split; intro; [rewrite H | rewrite <- H].
  apply QPos_div_mul. symmetry.  apply QPos_mul_div.
Qed.

Lemma QPos_div_mul_le_r a b c : b / c <= a  <->  b <= a * c.
Proof.
  rewrite QPos.mul_le_mono_r with (p := c).
  setoid_replace (b / c * c) with b. easy.
  apply QPos_div_mul.
Qed.

Lemma QPos_div_mul_le_l a b c : a <= b / c  <->  a * c <= b.
Proof.
  rewrite QPos.mul_le_mono_r with (p := c).
  setoid_replace (b / c * c) with b. easy.
  apply QPos_div_mul.
Qed.

Lemma QPos_div_mul_lt_l a b c : a < b / c  <->  a * c < b.
Proof.
  rewrite QPos.mul_lt_mono_r with (p := c).
  setoid_replace (b / c * c) with b. easy.
  apply QPos_div_mul.
Qed.

Lemma twopower_div : forall p q : Z, twopower (p - q) == (twopower p) / (twopower q).
Proof.
  intros p q; remember (p - q)%Z as r; replace p with (r + q)%Z by (rewrite Heqr; ring).
  apply QPos_div_mul_r; symmetry; apply twopower_mul.
Qed.

Lemma twopower_zero : twopower 0 == 1.
Proof.
  easy.
Qed.


Lemma twopower_one : twopower 1 == 2.
Proof.
  easy.
Qed.

Lemma QPos_from_pos_one : QPos_from_pos 1 == 1.
Proof.
  easy.
Qed.

Lemma QPos_from_pos_two : QPos_from_pos 2 == 2.
Proof.
  easy.
Qed.

Lemma QPos_from_pos_mul: forall p q, QPos_from_pos (p * q) == QPos_from_pos p * QPos_from_pos q.
Proof.
  unfold QPos.eq. intros. simpl. easy.
Qed.


Lemma positive_times_two : forall p, (p~0 = p * 2)%positive.
Proof.
  intro; rewrite Pos.mul_xO_r; now rewrite Pos.mul_1_r.
Qed.

Lemma pos_size_lt : forall p, QPos_from_pos p < twopower (' Pos.size p).
Proof.
  intro p. rewrite twopower_compat. apply QPos_from_pos_lt.
  apply Pos.size_gt.
Qed.

Lemma pos_size_le' : forall p, twopower (' Pos.size p) <= QPos_from_pos (p~0).
Proof.
  intro p. rewrite twopower_compat. apply QPos_from_pos_le.
  apply Pos.size_le.
Qed.

Lemma pos_size_le : forall p, twopower (' Pos.size p - 1) <= QPos_from_pos p.
Proof.
  intro p. rewrite twopower_div. rewrite twopower_one.
  apply QPos_div_mul_le_r. rewrite <- QPos_from_pos_two.
  rewrite <- QPos_from_pos_mul.
  rewrite <- positive_times_two.
  apply pos_size_le'.
Qed.

Notation "x <= y < z" := ((x <= y) /\ (y < z)) : QPos_scope.


Lemma QPos_lt_le_weak : forall p q, p < q  -> p <= q.
Proof.
  unfold QPos.le, QPos.lt; intros p q; destruct p, q; auto with qarith.
Qed.


Open Scope Q.

Lemma Q_over_one : forall a, a / 1 == a.
Proof.
  intro; unfold Qdiv, Qinv; destruct a;
  apply f_equal2; simpl; [rewrite (Z.mul_1_r) | rewrite (Pos.mul_1_r)]; easy.
Qed.


Lemma Q_div_le_lt a b c d : 0 < c -> 0 < d -> a <= c -> d < b  -> a / b < c / d.
Proof.
  intros.
  assert (0 < b) by (eapply Qlt_trans; eauto).
  apply Qmult_lt_r with (z := b * d); [ now apply Q_mul_pos_pos | ].
  setoid_replace (a / b * (b * d)) with (a * d) by field; [ | auto with qarith].
  setoid_replace (c / d * (b * d)) with (c * b) by field; [ | auto with qarith].
  eapply Qle_lt_trans; [ apply Qmult_le_r | apply Qmult_lt_l]; easy.
Qed.

Lemma Q_div_lt_le a b c d : 0 < c -> 0 < d -> a < c -> d <= b -> a / b < c / d.
Proof.
  intros.
  assert (0 < b) by (eapply Qlt_le_trans; eauto).
  apply Qmult_lt_r with (z := b * d); [now apply Q_mul_pos_pos |].
  setoid_replace (a / b * (b * d)) with (a * d) by field; [ | auto with qarith].
  setoid_replace (c / d * (b * d)) with (c * b) by field; [ | auto with qarith].
  eapply Qlt_le_trans; [ apply Qmult_lt_r | apply Qmult_le_l]; easy.
Qed.




Open Scope QPos.

Lemma QPos_div_le_lt a b c d : a <= c -> d < b  ->  a / b < c / d.
Proof.
  destruct a, b, c, d; unfold QPos.lt, QPos.le; now apply Q_div_le_lt.
Qed.

Lemma QPos_div_lt_le a b c d : a < c -> d <= b -> a / b < c / d.
  destruct a, b, c, d; unfold QPos.lt, QPos.le; now apply Q_div_lt_le.
Qed.

Hint Resolve QPos_lt_le_weak.
Hint Resolve QPos_div_le_lt.
Hint Resolve QPos_div_lt_le.

Hint Immediate pos_size_le.
Hint Immediate pos_size_lt.

Lemma trial_binade_bound : forall q : QPos, 
  let trial_binade := ('Pos.size (QPos_num q) - 'Pos.size (QPos_den q))%Z in
  twopower (trial_binade - 1) <= q < twopower (trial_binade + 1).
Proof.
  intros; split;
  setoid_replace q with (QPos_from_pos (QPos_num q) / QPos_from_pos (QPos_den q)) by (symmetry; apply num_over_den);
  unfold trial_binade.

  replace (' Pos.size (QPos_num q) - ' Pos.size (QPos_den q) - 1)%Z
     with (' Pos.size (QPos_num q) - 1 - ' Pos.size (QPos_den q))%Z by ring.
  rewrite twopower_div. auto.

  replace (' Pos.size (QPos_num q) - ' Pos.size (QPos_den q) + 1)%Z
     with (' Pos.size (QPos_num q) - (' Pos.size (QPos_den q) - 1))%Z by ring.
  rewrite twopower_div. auto.
Qed.

Definition binade (q : QPos) : Z :=
  let trial_binade := ('Pos.size (QPos_num q) - 'Pos.size (QPos_den q))%Z in
  if q <? twopower trial_binade then (trial_binade - 1)%Z else trial_binade.


Lemma QPos_ltb_le : forall q r, (q <? r) = false  <->  r <= q.
Proof.
  unfold QPos.le, QPos.ltb, QPos.compare. intros q r. destruct q, r. simpl.
  case_eq (x ?= x0)%Q.
  rewrite <- Qeq_alt. intuition.
  rewrite H. auto with qarith.
  rewrite <- Qlt_alt. intuition. exfalso. assert (x < x)%Q.
  eapply Qlt_le_trans; eauto. revert H1. unfold Qlt. auto with zarith.
  rewrite <- Qgt_alt. intuition.
Qed.


Lemma binade_bound : forall q : QPos,
  twopower (binade q) <= q < twopower (binade q + 1).
Proof.
  intro q.
  unfold binade.
  remember ('Pos.size (QPos_num q) - 'Pos.size (QPos_den q))%Z as trial_binade.
  case_eq (q <? twopower trial_binade).

  split.
  rewrite Heqtrial_binade. apply trial_binade_bound.
  replace (trial_binade - 1 + 1)%Z with trial_binade by ring.
  now apply QPos.ltb_lt.

  split.
  now apply QPos_ltb_le.
  rewrite Heqtrial_binade. apply trial_binade_bound.
Qed.

Lemma inject_Z_one : (inject_Z 1 == 1)%Q.
Proof.
  easy.
Qed.

Open Scope Q.

Lemma Qmul_gt1_gt1 : forall (q r : Q), 1 < q -> 1 < r -> 1 < q * r.
Proof.
  intros q r one_lt_q one_lt_r.
  setoid_replace 1 with (1 * 1) by ring.
  apply Qlt_trans with (y := q * 1).
  apply Qmult_lt_r. easy. easy.
  apply Qmult_lt_l.
  apply Qlt_trans with (y := 1); auto.
  easy. easy.
Qed.

Lemma Qmul_ge1_ge1 : forall (q r : Q), 1 <= q  ->  1 <= r  ->  1 <= q * r.
Proof.
  intros q r one_le_q one_le_r; setoid_replace 1 with (1 * 1) by ring;
  apply Qle_trans with (y := q * 1); [ apply Qmult_le_r |
  apply Qmult_le_l; [apply Qlt_le_trans with (y := 1) | ]]; easy.
Qed.

Hint Resolve Qmul_gt1_gt1.
Hint Resolve Qmul_ge1_ge1.

Lemma Qpower_one_lt : forall (n : Z) (q : Q),
  (0 < n)%Z  ->  1 < q  ->  1 < q^n.
Proof.
  intros; unfold Qpower; destruct n; try (now contradict H);
  induction p; simpl; auto.
Qed.


Lemma Qpower_one_le : forall (n : Z) (q : Q),
  (0 <= n)%Z  ->  1 <= q  -> 1 <= q^n.
Proof.
  intros; unfold Qpower; destruct n;
  [ | unfold Qpower_positive; induction p; simpl | contradiction H];
  auto.
Qed.



Open Scope QPos.

Lemma twopower_of_positive : forall p, (0 < p)%Z -> 1 < twopower p.
Proof.
  intros p p_pos; unfold twopower, QPos.lt; simpl;
  rewrite inject_Z_one; apply Qpower_one_lt; easy.
Qed.


Lemma twopower_of_nonnegative : forall p, (0 <= p)%Z -> 1 <= twopower p.
Proof.
  intros p p_nonneg; unfold twopower, QPos.le; simpl;
  rewrite inject_Z_one; apply Qpower_one_le; easy.
Qed.


Lemma twopower_monotonic : forall p q, (p <= q)%Z -> twopower p <= twopower q.
Proof.
  intros p q p_le_q;
  (* rewrite as 1 * twopower p <= twopower q *)
  rewrite <- QPos.mul_1_l at 1;
  apply QPos_div_mul_le_l;
  rewrite <- twopower_div;
  apply twopower_of_nonnegative;
  auto with zarith.
Qed.


Lemma twopower_monotonic_lt : forall m n, (m < n)%Z -> twopower m < twopower n.
Proof.
  intros m n m_lt_n;
  rewrite <- QPos.mul_1_l at 1;
  apply QPos_div_mul_lt_l;
  rewrite <- twopower_div;
  apply twopower_of_positive;
  omega.
Qed.


Lemma QPos_lt_le_trans a b c : a < b -> b <= c -> a < c.
Proof.
  destruct a, b, c; unfold QPos.le, QPos.lt; apply Qlt_le_trans.
Qed.


Lemma twopower_binade_contrapos n q : (binade q < n)%Z  ->  q < twopower n.
Proof.
  intros.
  apply Zlt_le_succ in H; unfold Z.succ in H.
  apply QPos_lt_le_trans with (b := twopower (binade q + 1)).
    apply binade_bound.
    now apply twopower_monotonic.
Qed.

Lemma QPos_le_ngt : forall q r, q <= r  <->  ~ (r < q).
Proof.
  intros q r; destruct q, r; unfold QPos.le, QPos.lt; split; QOrder.order.
Qed.

Lemma QPos_lt_nge : forall q r, q < r  <->  ~ (r <= q).
Proof.
  intros q r; destruct q, r; unfold QPos.le, QPos.lt; split; QOrder.order.
Qed.

Lemma QPos_le_trans : forall p q r, p <= q -> q <= r -> p <= r.
Proof.
  intros p q r; destruct p, q, r; unfold QPos.le; QOrder.order.
Qed.

(* Now the main theorem that effectively acts as a specification for binade. *)

Theorem twopower_binade_le n q : twopower n <= q  <->  (n <= binade q)%Z.
Proof.
  split; intro.

  (* First direction: showing that twopower n <= q  ->  n <= binade q. *)
  apply Z.le_ngt.
  contradict H.
  apply QPos_lt_nge.
  now apply twopower_binade_contrapos.

  (* Second direction: showing that n <= binade q  implies twopower n <= q. *)
  apply QPos_le_trans with (q := twopower (binade q)).
  now apply twopower_monotonic.
  apply binade_bound.
Qed.

(* With this in hand, we can finally prove that binade is well-defined. *)

Add Morphism binade : binade_morphism.
Proof.
  intros x y x_eq_y; apply Z.le_antisymm; apply twopower_binade_le;
  [rewrite <- x_eq_y | rewrite x_eq_y ]; apply twopower_binade_le; apply Z.le_refl.
Qed.

(* We can also use the injectivity of twopower to show that
   binade (twopower n) = n. *)

Lemma twopower_injective_le m n : twopower m <= twopower n  ->  (m <= n)%Z.
Proof.
  intro.
  apply Z.nlt_ge.
  contradict H.
  apply QPos_lt_nge.
  now apply twopower_monotonic_lt.
Qed.


Lemma QPos_le_eq p q : p == q  ->  p <= q.
Proof.
  intro p_eq_q. rewrite p_eq_q. unfold QPos.le. destruct q. simpl. auto with qarith.
Qed.


Lemma twopower_injective m n : twopower m == twopower n -> m = n.
Proof.
  intro H.
  apply Z.le_antisymm.
  apply twopower_injective_le.
  now apply QPos_le_eq.

  apply twopower_injective_le.
  now apply QPos_le_eq.
Qed.


Lemma QPos_le_antisymm q r : q <= r -> r <= q -> q == r.
Proof.
  unfold QPos.le, QPos.eq; destruct q, r; simpl.
  auto with qarith.
Qed.


Lemma QPos_le_refl q : q <= q.
Proof.
  unfold QPos.le; destruct q; simpl; auto with qarith.
Qed.



Theorem binade_twopower_eq n : (binade (twopower n) = n)%Z.
Proof.
  apply twopower_injective.
  apply QPos_le_antisymm.
  apply twopower_binade_le. auto with zarith.
  apply twopower_monotonic.
  apply twopower_binade_le.
  apply QPos_le_refl.
Qed.


Theorem binade_monotonic q r : q <= r  -> (binade q <= binade r)%Z.
Proof.
  intro q_le_r. apply twopower_binade_le.
  apply QPos_le_trans with (q := q).
  apply binade_bound. easy.
Qed.

(* Alternative form of the specification. *)

Theorem twopower_binade_lt n q : q < twopower n  <->  (binade q < n)%Z.
Proof.
  rewrite Z.lt_nge.
  rewrite QPos_lt_nge.
  split; intro H; contradict H; now apply twopower_binade_le.
Qed.
