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
  now apply Qpower_pos.
Qed.

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

Lemma inject_Z_one : (inject_Z 1 == 1).
Proof.
  easy.
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

Definition twopower (n : Z) : QPos.
  refine (exist _ (inject_Z 2 ^ n)%Q _).
  apply two_to_the_power_n_is_positive.
Defined.

Lemma twopower_compat : forall p, twopower (' p) == QPos_from_pos (2^p).
Proof.
  intro p. unfold QPos.eq. simpl.
  rewrite Pos2Z.inj_pow.
  rewrite Zpower_Qpower. reflexivity.
  auto with zarith.
Qed.


Lemma twopower_mul : forall p q : Z, twopower (p + q) == (twopower p) * (twopower q).
Proof.
  unfold QPos.eq, twopower; intros; now apply Qpower_plus.
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


Lemma twopower_monotonic_le : forall p q, (p <= q)%Z -> twopower p <= twopower q.
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
  intro.
  apply Z.lt_nge.
  contradict H.
  apply QPos_le_ngt.
  now apply twopower_monotonic_le.
Qed.


Lemma twopower_injective_le m n : twopower m <= twopower n  ->  (m <= n)%Z.
Proof.
  intro.
  apply Z.nlt_ge.
  contradict H.
  apply QPos_lt_nge.
  now apply twopower_monotonic_lt.
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

Lemma twopower_binade_contrapos n q : (binade q < n)%Z  ->  q < twopower n.
Proof.
  intros.
  apply Zlt_le_succ in H; unfold Z.succ in H.
  apply QPos_lt_le_trans with (b := twopower (binade q + 1)).
    apply binade_bound.
    now apply twopower_monotonic_le.
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
  apply QPos_le_trans with (b := twopower (binade q)).
  now apply twopower_monotonic_le.
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

Theorem binade_twopower_eq n : (binade (twopower n) = n)%Z.
Proof.
  apply twopower_injective.
  apply QPos_le_antisymm.
  apply twopower_binade_le. auto with zarith.
  apply twopower_monotonic_le.
  apply twopower_binade_le.
  apply QPos_le_refl.
Qed.


Theorem binade_monotonic q r : q <= r  -> (binade q <= binade r)%Z.
Proof.
  intro q_le_r. apply twopower_binade_le.
  apply QPos_le_trans with (b := q).
  apply binade_bound. easy.
Qed.

(* Alternative form of the specification. *)

Theorem twopower_binade_lt n q : q < twopower n  <->  (binade q < n)%Z.
Proof.
  rewrite Z.lt_nge.
  rewrite QPos_lt_nge.
  split; intro H; contradict H; now apply twopower_binade_le.
Qed.

(* Relationship with multiplication. *)

Theorem binade_one : (binade (1%QPos) = 0)%Z.
Proof.
  easy.
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

Theorem binade_mul x y :
  (binade x + binade y <= binade (x * y)%QPos <= binade x + binade y + 1)%Z.
Proof.
  split;
  [
  apply twopower_binade_le; rewrite twopower_mul; apply mul_le
  |
  apply Zlt_succ_le; apply twopower_binade_lt;
  replace (Z.succ (binade x + binade y + 1)) with
  ((binade x + 1) + (binade y + 1))%Z by omega; rewrite twopower_mul;
    apply mul_lt
  ]; apply binade_bound.
Qed.

Theorem binade_div x y :
  (binade x - binade y - 1 <= binade (x / y)%QPos <= binade x - binade y)%Z.
Proof.
  remember (x / y) as z; setoid_replace x with (x / y * y) by (symmetry;
  apply QPos_div_mul); rewrite <- Heqz; pose proof (binade_mul z y); omega.
Qed.
