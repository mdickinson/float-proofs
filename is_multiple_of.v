Require Import QArith.
Require Import Qabs.

Require Import rearrange_tactic.
Require Import floor_and_ceiling.


Local Open Scope Q.


Definition is_multiple_of (y x : Q) :=
  exists (m : Q), is_integer m  /\  x == m * y.

Add Morphism is_multiple_of : is_multiple_of_morphism.
Proof.
  intros m n m_eq_n x y x_eq_y; unfold is_multiple_of; split;
  destruct 1 as [z H]; exists z; rewrite m_eq_n in *; rewrite x_eq_y in *;
  trivial.
Qed.

Lemma is_multiple_of_additive (m a b : Q) :
  is_multiple_of m a -> is_multiple_of m b -> is_multiple_of m (a + b).
Proof.
  destruct 1 as [x [is_integer_x m_divides_a]];
  destruct 1 as [y [is_integer_y m_divides_b]]; exists (x + y); split.
  - now apply is_integer_add.
  - rewrite m_divides_a,  m_divides_b; ring.
Qed.

Lemma is_multiple_of_neg (m a : Q) :
  is_multiple_of m a -> is_multiple_of m (-a).
Proof.
  destruct 1 as [x [is_integer_x m_divides_a]]; exists (-x); split.
  - now apply is_integer_neg.
  - rewrite m_divides_a; ring.
Qed.

Lemma is_multiple_of_sub (m a b : Q) :
  is_multiple_of m a -> is_multiple_of m b -> is_multiple_of m (a - b).
Proof.
  intros; apply is_multiple_of_additive; [ | apply is_multiple_of_neg]; easy.
Qed.

Lemma is_multiple_of_abs (m a : Q) :
  is_multiple_of m a -> is_multiple_of m (Qabs a).
Proof.
  apply Qabs_case; intros; [ easy | now apply is_multiple_of_neg].
Qed.

Lemma is_multiple_of_transitive (a b c : Q):
  is_multiple_of a b -> is_multiple_of b c -> is_multiple_of a c.
Proof.
  destruct 1 as [m [is_integer_m b_is_ma]];
  destruct 1 as [n [is_integer_n c_is_nb]]; exists (n*m); split.
  - now apply is_integer_mul.
  - rewrite c_is_nb, b_is_ma; ring.
Qed.

Lemma is_multiple_of_product (a b c d : Q):
  is_multiple_of a b -> is_multiple_of c d -> is_multiple_of (a*c) (b*d).
Proof.
  destruct 1 as [m [is_integer_m b_is_ma]];
  destruct 1 as [n [is_integer_n d_is_nc]]; exists (m * n); split.
  - now apply is_integer_mul.
  - rewrite b_is_ma, d_is_nc; ring.
Qed.

Lemma small_multiple_is_zero (m a : Q) :
  is_multiple_of m a  ->  Qabs a < m  ->  a == 0.
Proof.
  destruct 1 as [b [is_integer_b a_is_bm]];
  rewrite a_is_bm; intro a_bounded; cut (b == 0).
  - intro H; rewrite H; ring.
  - apply small_integer_is_zero with (1 := is_integer_b).
    assert (0 < m)
      by (apply Qle_lt_trans with (2 := a_bounded); apply Qabs_nonneg);
    scale_by m;
    setoid_replace m with (Qabs m) at 1
      by (rewrite Qabs_pos; try apply Qlt_le_weak; easy);
    rewrite <- Qabs_Qmult; rearrange.
Qed.