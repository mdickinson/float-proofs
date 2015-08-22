(* Definition of the is_integer relation, and basic properties. *)

Set Implicit Arguments.

Require Import QArith.
Require Import Qabs.

Require Import remedial.

Definition is_integer q := exists n : Z, inject_Z n == q.

Add Parametric Morphism : is_integer
    with signature Qeq ==> iff as is_integer_morphism.
Proof.
  split; destruct 1 as [n n_eq]; exists n; now rewrite n_eq.
Qed.

Theorem is_integer_inject_Z n : is_integer (inject_Z n).
Proof.
  now exists n.
Qed.

Theorem is_integer_neg q : is_integer q -> is_integer (-q).
Proof.
  destruct 1 as [n n_eq_q]; exists (-n)%Z; now rewrite inject_Z_opp, n_eq_q.
Qed.

Theorem is_integer_add q r :
  is_integer q -> is_integer r -> is_integer (q + r).
Proof.
  destruct 1 as [m m_eq_q], 1 as [n n_eq_r]; exists (m + n)%Z;
  now rewrite inject_Z_plus, m_eq_q, n_eq_r.
Qed.

Theorem is_integer_mul q r :
  is_integer q -> is_integer r -> is_integer (q * r).
Proof.
  destruct 1 as [m m_eq_q], 1 as [n n_eq_r]; exists (m * n)%Z;
  now rewrite inject_Z_mult, m_eq_q, n_eq_r.
Qed.

Theorem is_integer_sub q r :
  is_integer q -> is_integer r -> is_integer (q - r).
Proof.
  intros; apply is_integer_add; now try apply is_integer_neg.
Qed.

Theorem small_integer_is_zero q :
  is_integer q -> Qabs q < 1 -> q == 0.
Proof.
  destruct 1 as [n H]; rewrite <- H; clear H; rewrite Qabs_Zabs;
  change 0 with (inject_Z 0); change 1 with (inject_Z 1);
  rewrite inject_Z_injective, <- Zlt_Qlt; intro;
  assert (-0 <= n <= 0)%Z by (now apply Z.abs_le, Z.lt_succ_r);
  now apply Z.le_antisymm.
Qed.