(**

* Powers of two

In this section we introduce definitions and basic properties
for powers of two.

*)

Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import QOrderedType.
Require Import Qabs.

Require Import qpos.
Require Import is_integer.
Require Import rearrange_tactic.
Require Import remedial.

(**

First we want to define powers of two as a function
from nonnegative integers to integers.  There's already
a [Z.pow] operation in the standard library, but it's
defined for negative exponents as well as positive.
We'd like something that can only be used for positive
exponents.  Rather than reinventing the wheel, let's
see if we can make use of the existing positive and N types.

*)

Local Open Scope N.

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

Local Open Scope Q.

Lemma two_to_the_power_n_is_nonzero : forall n: Z, (~ (inject_Z 2)^n == 0)%Q.
Proof.
  intro n; destruct n; simpl; try (rewrite <- Qinv_power_positive);
  try (apply Qpower_not_0_positive); discriminate.
Qed.

Lemma two_to_the_power_n_is_positive : forall n : Z, (0 < inject_Z 2 ^ n)%Q.
Proof.
  intros; apply Qle_not_eq;
  [ now apply Qpower_pos | apply Qnot_eq_sym, two_to_the_power_n_is_nonzero].
Qed.

Lemma Qmul_gt1_gt1 : forall (q r : Q), 1 < q -> 1 < r -> 1 < q * r.
Proof.
  intros q r one_lt_q one_lt_r; apply Qlt_trans with (1 := one_lt_q);
  setoid_replace q with (q * 1) at 1 by ring;
  apply Qmult_lt_l with (2 := one_lt_r);
  apply Qlt_trans with (2 := one_lt_q); easy.
Qed.

Lemma Qmul_ge1_ge1 : forall (q r : Q), 1 <= q  ->  1 <= r  ->  1 <= q * r.
Proof.
  intros q r one_le_q one_le_r; apply Qle_trans with (1 := one_le_q);
  setoid_replace q with (q * 1) at 1 by ring;
  apply Qmult_le_l with (2 := one_le_r);
  apply Qlt_le_trans with (2 := one_le_q); easy.
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

Local Open Scope QPos.

Definition twopower (n : Z) : QPos :=
  exist _ (inject_Z 2 ^ n)%Q (two_to_the_power_n_is_positive n).

Lemma twopower_compat : forall p, twopower (' p) == QPos_from_pos (2^p).
Proof.
  intro p; unfold QPos.eq; simpl; rewrite Pos2Z.inj_pow, Zpower_Qpower; easy.
Qed.


Lemma twopower_mul :
  forall p q : Z, twopower (p + q) == (twopower p) * (twopower q).
Proof.
  unfold QPos.eq, twopower; intros; now apply Qpower_plus.
Qed.

Lemma twopower_div :
  forall p q : Z, twopower (p - q) == (twopower p) / (twopower q).
Proof.
  intros p q; remember (p - q)%Z as r;
  replace p with (r + q)%Z by (rewrite Heqr; ring);
  apply QPos_div_mul_r; symmetry; apply twopower_mul.
Qed.

Lemma twopower_inv p : twopower (-p) == / twopower p.
Proof.
  change (-p)%Z with (0 - p)%Z; rewrite twopower_div; apply QPos.mul_1_l.
Qed.

Lemma twopower_zero : twopower 0 == 1.
Proof.
  easy.
Qed.


Lemma twopower_one : twopower 1 == 2.
Proof.
  easy.
Qed.

Lemma twopower_of_positive : forall p, (0 < p)%Z -> 1 < twopower p.
Proof.
  intros p p_pos; unfold twopower, QPos.lt; simpl;
  change (inject_Z 1) with 1%Q; apply Qpower_one_lt; easy.
Qed.


Lemma twopower_of_nonnegative : forall p, (0 <= p)%Z -> 1 <= twopower p.
Proof.
  intros p p_nonneg; unfold twopower, QPos.le; simpl;
  change (inject_Z 1) with 1%Q; apply Qpower_one_le; easy.
Qed.


Lemma twopower_monotonic_le :
  forall p q, (p <= q)%Z -> twopower p <= twopower q.
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


Lemma twopower_injective_lt m n : twopower m < twopower n  ->  (m < n)%Z.
Proof.
  intro; apply Z.lt_nge; contradict H; apply QPos_le_ngt;
  now apply twopower_monotonic_le.
Qed.


Lemma twopower_injective_le m n : twopower m <= twopower n  ->  (m <= n)%Z.
Proof.
  intro; apply Z.nlt_ge; contradict H; apply QPos_lt_nge;
  now apply twopower_monotonic_lt.
Qed.


Lemma twopower_injective m n : twopower m == twopower n -> m = n.
Proof.
  intro H; apply Z.le_antisymm; now apply twopower_injective_le, QPos_le_eq.
Qed.


Lemma positive_times_two : forall p, (p~0 = p * 2)%positive.
Proof.
  intro; rewrite Pos.mul_xO_r; now rewrite Pos.mul_1_r.
Qed.

Lemma pos_size_lt : forall p, QPos_from_pos p < twopower (' Pos.size p).
Proof.
  intro; rewrite twopower_compat; apply QPos_from_pos_lt, Pos.size_gt.
Qed.

Lemma pos_size_le' : forall p, twopower (' Pos.size p) <= QPos_from_pos (p~0).
Proof.
  intro p; rewrite twopower_compat; apply QPos_from_pos_le, Pos.size_le.
Qed.

Lemma pos_size_le : forall p, twopower (' Pos.size p - 1) <= QPos_from_pos p.
Proof.
  intro p; rewrite twopower_div, twopower_one;
  apply QPos_div_mul_le_r; rewrite <- QPos_from_pos_two,
  <- QPos_from_pos_mul, <- positive_times_two; apply pos_size_le'.
Qed.

Lemma mul_le p q r s : p <= q -> r <= s -> p*r <= q * s.
Proof.
  intros; apply QPos_le_trans with (b := q * r);
  [apply QPos.mul_le_mono_r | apply QPos.mul_le_mono_l ]; easy.
Qed.

Lemma mul_lt p q r s : p < q -> r < s -> p*r < q*s.
Proof.
  intros; apply QPos_lt_trans with (b := q * r);
  [apply QPos.mul_lt_mono_r | apply QPos.mul_lt_mono_l ]; easy.
Qed.

(* Versions of twopower for the rationals. *)

Local Open Scope Q.

Definition twopowerQ n := proj1_sig (twopower n).

Lemma twopowerQ_positive n : 0 < twopowerQ n.
Proof.
  unfold twopowerQ; now destruct (twopower n).
Qed.

Lemma twopowerQ_nonzero n : ~(twopowerQ n == 0).
Proof.
  apply Qnot_eq_sym, Qlt_not_eq, twopowerQ_positive.
Qed.

Lemma twopowerQ_nonnegative n : 0 <= twopowerQ n.
Proof.
  apply Qlt_le_weak, twopowerQ_positive.
Qed.

Lemma Qabs_twopower (x : Z) : Qabs (twopowerQ x) == twopowerQ x.
Proof.
  apply Qabs_pos, Qlt_le_weak, twopowerQ_positive.
Qed.

Lemma twopowerQ_monotonic_lt m n :
  (m < n)%Z -> twopowerQ m < twopowerQ n.
Proof.
  apply twopower_monotonic_lt.
Qed.

Lemma twopowerQ_monotonic_le m n :
  (m <= n)%Z -> twopowerQ m <= twopowerQ n.
Proof.
  apply twopower_monotonic_le.
Qed.

Lemma twopowerQ_injective_lt (p q : Z) :
  twopowerQ p < twopowerQ q  ->  (p < q)%Z.
Proof.
  apply twopower_injective_lt.
Qed.

Lemma twopowerQ_injective_le (p q : Z) :
  twopowerQ p <= twopowerQ q  ->  (p <= q)%Z.
Proof.
  apply twopower_injective_le.
Qed.

Lemma twopowerQ_mul m n : twopowerQ (m + n) == twopowerQ m * twopowerQ n.
Proof.
  apply twopower_mul.
Qed.

Lemma twopowerQ_inv m : twopowerQ (- m) == / twopowerQ m.
Proof.
  apply twopower_inv.
Qed.

Lemma twopowerQ_div m n : twopowerQ (m - n) == twopowerQ m / twopowerQ n.
Proof.
  apply twopower_div.
Qed.


Lemma is_integer_twopowerQ (n : Z) :
  (0 <= n)%Z -> is_integer (twopowerQ n).
Proof.
  unfold twopowerQ; intro; simpl;
  rewrite <- Qpower.Zpower_Qpower; [ apply is_integer_inject_Z | easy ].
Qed.


Lemma Qabs_twopowerQ n :
  Qabs (twopowerQ n) == twopowerQ n.
Proof.
  apply Qabs_pos, Qlt_le_weak, twopowerQ_positive.
Qed.