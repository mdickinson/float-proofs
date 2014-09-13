Require Import ZArith.
Require Import QArith.

Open Scope Z.

Lemma div2_monotonic : forall (m n : Z), m <= n -> Z.div2 m <= Z.div2 n.
Proof.
intros. rewrite ?Zdiv2_div. apply Z_div_le. omega. trivial.
Qed.

Lemma shiftl_monotonic : forall (p m n : Z),
  m <= n -> Z.shiftl m p <= Z.shiftl n p.
Proof.
intro p. destruct p as [ | q | q].
(* case p = 0 *)
trivial.

(* case p > 0 *)
unfold Z.shiftl.
induction q; intros; try apply Z.mul_le_mono_nonneg_l; try omega.
apply IHq. apply IHq. trivial. apply IHq. apply IHq. trivial.

(* case p < 0 *)
unfold Z.shiftl.
induction q; intros.
apply div2_monotonic. apply IHq. apply IHq. trivial.
apply IHq. apply IHq. trivial.
apply div2_monotonic. trivial.
Qed.

Lemma shiftl_lt_monotonic : forall (p m n : Z),
  0 <= p -> m < n -> Z.shiftl m p < Z.shiftl n p.
Proof.
unfold Z.shiftl.
intro p. destruct p as [ | q | q].
(* case p = 0 *)
trivial.
(* case p > 0 *)
intros m n redundant. clear redundant. revert m n.
induction q as [ r | r | ]; intros.
apply Zmult_lt_compat_l. omega. apply IHr. apply IHr. trivial.
apply IHr. apply IHr. trivial.
apply Zmult_lt_compat_l. omega. trivial.
(* case p < 0 *)
intros. absurd (0 <= Z.neg q). auto with zarith. trivial.
Qed.

Lemma shiftl_positive :
  forall (m : Z), 0 <= m ->
  forall (n : Z), 0 < n -> 0 < Z.shiftl n m.
Proof.
intros m m_positive n.
assert (0 = Z.shiftl 0 m).
symmetry. apply Z.shiftl_0_l. rewrite H at 2.
apply shiftl_lt_monotonic. trivial.
Qed.

Definition twopower_Z := Z.shiftl 1.

Lemma twopower_zero : twopower_Z 0 = 1.
Proof.
reflexivity.
Qed.

Lemma twopower_positive : forall (m : Z), 0 <= m -> 0 < twopower_Z m.
Proof.
intros. unfold twopower_Z. apply shiftl_positive. trivial. omega.
Qed.

Lemma twopower_sum : forall (m n : Z), 0 <= m -> 0 <= n ->
  twopower_Z (m + n) = twopower_Z m * twopower_Z n.
Proof.
intros m n m_nonnegative n_nonnegative.
unfold twopower_Z.
rewrite ?Z.shiftl_mul_pow2.
rewrite Z.pow_add_r. ring. trivial. trivial. trivial. trivial. omega.
Qed.

Lemma twopower_monotonic : forall (m n : Z), m <= n -> twopower_Z m <= twopower_Z n.
Proof.
unfold twopower_Z.
intros m n m_le_n.
assert (Z.shiftl 1 n = Z.shiftl (Z.shiftl 1 (n - m)) m).
replace n with (n - m + m ) at 1 by ring.
symmetry. apply Z.shiftl_shiftl. auto with zarith.
rewrite H.
apply shiftl_monotonic.
assert (0 < Z.shiftl 1 (n - m)).
apply shiftl_positive. omega. omega. omega.
Qed.

Open Scope Q.

Definition twopower_Q (n : Z) : Q :=
  match n with
  | 0%Z => 1
  | Z.pos p => twopower_Z n # 1
  | Z.neg p => 1 # Z.to_pos (twopower_Z (-n))
  end.

Lemma twopower_zero_Q : twopower_Q 0 == 1.
Proof.
reflexivity.
Qed.

Lemma twopower_Z_Q_compat : forall (n : Z), (0 <= n)%Z -> twopower_Q n == (twopower_Z n) # 1.
Proof.
intros.
destruct n. reflexivity. reflexivity.
absurd (0 <= Z.neg p)%Z. auto with zarith. trivial.
Qed.

Arguments twopower_Z _ : simpl never.

Lemma twopower_positive_Q : forall m : Z, 0 < twopower_Q m.
Proof.
unfold Qlt. unfold twopower_Q. intro m. destruct m.
simpl. auto with zarith.
simpl. rewrite Z.mul_1_r. apply twopower_positive. auto with zarith.
simpl. auto with zarith.
Qed.

Lemma twopower_nonzero_Q : forall m : Z, ~ twopower_Q m == 0.
Proof.
intro.
assert (twopower_Q m > 0) by apply twopower_positive_Q.
auto with qarith.
Qed.

Lemma twopower_inverse_Q : forall m : Z,
   twopower_Q m * twopower_Q (-m) == 1.
Proof.
unfold Qeq. unfold Qmult. simpl.
destruct m. 
(* case m = 0 *)
trivial.
(* case m > 0 *)
simpl.
assert (' Z.to_pos (twopower_Z (' p)) = twopower_Z ('p )).
apply Z2Pos.id. apply twopower_positive. auto with zarith.
rewrite H. ring.
(* case m < 0 *)
simpl.
rewrite Pos2Z.inj_mul.
rewrite Z2Pos.id.
generalize (twopower_Z (' p)). intro. destruct z; trivial.
apply twopower_positive. auto with zarith.
Qed.

Lemma twopower_sum_Q_restricted : forall (m n : Z),
  (0 <= m)%Z -> (0 <= n)%Z -> twopower_Q (m + n) == twopower_Q m * twopower_Q n.
Proof.
intros m n m_nonnegative n_nonnegative.
assert (0 <= m + n)%Z. omega.
rewrite ?twopower_Z_Q_compat; try trivial.
unfold Qmult. unfold Qeq. rewrite twopower_sum; trivial.
Qed.

(* Now address case where m < 0 and n >= 0.  Let p = m + n.
   2^p = 2^m * 2^n <-> 2^(-m) * 2^p = 2^n  (because 2^(-m) * 2^m = 1)
   if p >= 0, we're done.  If p < 0, do a further transformation:
   <-> 2^(-m) = 2^n * 2^(-p). *)

(* By symmetry, this also addresses the case where n < 0 and m >= 0. *)

Lemma twopower_sum_Q_semi_restricted : forall (m n : Z),
  (0 <= n)%Z -> twopower_Q (m + n) == twopower_Q m * twopower_Q n.
Proof.
intros m n n_nonnegative.
destruct (Z_lt_le_dec m 0).
apply Qmult_inj_l with (z := twopower_Q (- m)).
apply twopower_nonzero_Q.
rewrite Qmult_assoc.
apply Qeq_trans with (y := twopower_Q m * twopower_Q (-m) * twopower_Q n).
rewrite twopower_inverse_Q.
rewrite Qmult_1_l.
remember (-m)%Z as p.
assert (p >= 0)%Z by auto with zarith.
replace (m + n)%Z with (n - p)%Z by auto with zarith.

(* Now split into cases again: either n - p >= 0, or n - p < 0. *)
assert ({(n < p)%Z} + {(p <= n)%Z}) by apply Z_lt_le_dec.
destruct H0.
(* First, we're in the case where n < p. *)
remember (n - p)%Z as q.
apply Qmult_inj_r with (z := twopower_Q (- q)).
assert (twopower_Q (-q) > 0) by apply twopower_positive_Q.
auto with qarith.
rewrite <- Qmult_assoc.
rewrite twopower_inverse_Q.
rewrite Qmult_1_r.
remember (-q)%Z as r.
assert (p = r + n)%Z by auto with zarith. rewrite H0.
rewrite Qmult_comm.
apply twopower_sum_Q_restricted. auto with zarith. trivial.
(* Now, the case where n >= p, so n - p is nonnegative. *)
remember (n - p)%Z as r.
replace n with (p + r)%Z by auto with zarith.
symmetry.
apply twopower_sum_Q_restricted. auto with zarith. auto with zarith.
ring.

apply twopower_sum_Q_restricted. trivial. trivial.
Qed.


Lemma twopower_sum_Q : forall (m n : Z),
  twopower_Q (m + n) == twopower_Q m * twopower_Q n.
Proof.
intros.
(* Destruct on the sign of n. *)
destruct (Z_lt_le_dec n 0).
(* Case n < 0. *)
apply Qmult_inj_r with (z := twopower_Q (- n)).
apply twopower_nonzero_Q.
rewrite <- Qmult_assoc.
rewrite twopower_inverse_Q.
rewrite Qmult_1_r.
remember (-n)%Z as p.
remember (m + n)%Z as q.
assert (m = q + p)%Z by auto with zarith.
rewrite H.
symmetry. apply twopower_sum_Q_semi_restricted. auto with zarith.
apply twopower_sum_Q_semi_restricted. auto with zarith.
Qed.

Lemma twopower_div_Q : forall (m n : Z),
  twopower_Q m / twopower_Q n == twopower_Q (m - n)%Z.
Proof.
intros.
apply Qmult_inj_r with (z := twopower_Q n).
apply twopower_nonzero_Q.
assert (twopower_Q m / twopower_Q n * twopower_Q n == twopower_Q m).
field. apply twopower_nonzero_Q. rewrite H.

replace m with (m - n + n)%Z at 1 by auto with zarith.
remember (m - n)%Z as p.
apply twopower_sum_Q.
Qed.
