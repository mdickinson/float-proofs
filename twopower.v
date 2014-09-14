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

Lemma twopower_nonzero : forall (m : Z), 0 <= m -> twopower_Z m <> 0.
Proof.
intros. assert (0 < twopower_Z m) by (apply twopower_positive; assumption).
auto with zarith.
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

Arguments twopower_Z _ : simpl never.

Open Scope Q.

Definition twopower_Q (m : Z) : Q :=
  if Z_lt_le_dec m 0
  then / inject_Z (twopower_Z (-m))
  else inject_Z (twopower_Z m).

Lemma twopower_zero_Q : twopower_Q 0 == 1.
Proof.
reflexivity.
Qed.

Lemma twopower_Z_Q_compat : forall (m : Z),
  (0 <= m)%Z -> twopower_Q m == inject_Z (twopower_Z m).
Proof.
intros. unfold twopower_Q.
destruct (Z_lt_le_dec m 0). absurd (m < 0)%Z. auto with zarith. trivial.
reflexivity.
Qed.

Lemma twopower_positive_Q : forall m : Z, 0 < twopower_Q m.
Proof.
  intros; unfold twopower_Q; destruct (Z_lt_le_dec m 0);
  [ apply Qinv_lt_0_compat | ];
  setoid_replace 0 with (inject_Z 0) by reflexivity;
  rewrite <- Zlt_Qlt; apply twopower_positive; auto with zarith.
Qed.

Lemma twopower_nonzero_Q : forall m : Z, ~ twopower_Q m == 0.
Proof.
intro.
assert (0 < twopower_Q m) by apply twopower_positive_Q.
auto with qarith.
Qed.

Lemma inject_Z_nonzero : forall x,
   ~ (inject_Z x == 0)  <->  (x <> 0)%Z.
Proof.
  intros; split; intro; intro; apply H; apply inject_Z_injective; trivial.
Qed.

Lemma inject_twopower_nonzero : forall x,
   (0 <= x)%Z -> ~ (inject_Z (twopower_Z x)) == 0.
Proof.
  intros x x_nonnegative. apply inject_Z_nonzero. apply twopower_nonzero.
  assumption.
Qed.

Lemma twopower_inverse_Q : forall m : Z,
   twopower_Q m * twopower_Q (-m) == 1.
Proof.
intro m. unfold twopower_Q.
destruct (Z_lt_le_dec m 0); destruct (Z_lt_le_dec (-m) 0).
  (* m < 0 and -m < 0 *)
  absurd (m < 0)%Z; auto with zarith.
  (* m < 0 and 0 <= -m *)
  field. apply inject_twopower_nonzero. assumption.
  (* 0 <= m and -m < 0 *)
  replace (--m)%Z with m by auto with zarith.
  field. apply inject_twopower_nonzero. assumption.
  (* 0 <= m and 0 <= -m *)
  replace m with 0%Z by omega. reflexivity.
Qed.

Lemma twopower_as_quotient : forall m : Z,
  twopower_Q m == inject_Z (twopower_Z (Zmax 0 m)) /
                  inject_Z (twopower_Z (Zmax 0 (-m))).
Proof.
  intro m. unfold twopower_Q.
  destruct (Z_lt_le_dec m 0).
    replace (Z.max 0 (-m)) with (-m)%Z by (
      symmetry; apply Z.max_r; auto with zarith).
    replace (Z.max 0 m) with 0%Z by (
      symmetry; apply Z.max_l; auto with zarith).
    rewrite twopower_zero.
    field. apply inject_twopower_nonzero. auto with zarith.

    replace (Z.max 0 m) with m by (
      symmetry; apply Z.max_r; auto with zarith).
    replace (Z.max 0 (-m)) with 0%Z by (
      symmetry; apply Z.max_l; auto with zarith).
    rewrite twopower_zero.
    field.
Qed.

Lemma twopower_sum_Q : forall (m n : Z),
  twopower_Q (m + n) == twopower_Q m * twopower_Q n.
Proof.
  intros m n; unfold twopower_Q;
  destruct (Z_lt_le_dec m 0); destruct (Z_lt_le_dec n 0);
  destruct (Z_lt_le_dec (m + n) 0).
    (* m, n and m + n all negative. -(m + n) = -m + -n. *)
    replace (-(m + n))%Z with ((-m) + (-n))%Z by ring;
    rewrite twopower_sum; [ | auto with zarith | auto with zarith];
    rewrite inject_Z_mult; field;
    try split; apply inject_twopower_nonzero; auto with zarith.

    (* m, n negative; m + n nonnegative. Not possible. *) 
    absurd (0 <= m + n)%Z; auto with zarith.

    (* m and m + n negative and n nonnegative. (-m) = -(m + n) + n. *)
    replace (-m)%Z with (-(m + n) + n)%Z by ring;
    rewrite twopower_sum; [ | auto with zarith | auto with zarith];
    rewrite inject_Z_mult; field;
    try split; apply inject_twopower_nonzero; auto with zarith.

    (* m negative, n and m + n nonnegative. n = (m + n) + (-m). *)
    replace n with ((-m) + (m + n))%Z at 2 by ring;
    rewrite (twopower_sum (-m) (m + n)); [ | auto with zarith | auto with zarith];
    rewrite inject_Z_mult; field;
    try split; apply inject_twopower_nonzero; auto with zarith.

    (* n and m + n negative, m nonnegative.  -n = -(m + n) + m. *)
    replace (-n)%Z with ((-(m + n)) + m)%Z by ring;
    rewrite (twopower_sum (-(m + n)) m); [ | auto with zarith | auto with zarith];
    rewrite inject_Z_mult; field;
    try split; apply inject_twopower_nonzero; auto with zarith.

    (* n negative, m and m + n nonnegative;  m = (m + n) + (-n) *)
    replace m with ((m + n) + (-n))%Z at 2 by ring;
    rewrite (twopower_sum (m + n) (-n)); [ | auto with zarith | auto with zarith];
    rewrite inject_Z_mult; field;
    try split; apply inject_twopower_nonzero; auto with zarith.

    (* m + n negative, m and n nonnegative.  Not possible. *)
    absurd (m + n < 0)%Z; auto with zarith.

    (* m, n and m + n all nonnegative.  m + n = m + n. *)
    rewrite twopower_sum; [ | auto with zarith | auto with zarith];
    rewrite inject_Z_mult; field;
    try split; apply inject_twopower_nonzero; auto with zarith.
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

Lemma twopower_Q_monotonic :
  forall m n : Z, (m <= n)%Z -> twopower_Q m <= twopower_Q n.
Proof.
  intros m n m_le_n.
  assert (exists k:Z, 0 <= m + k  /\  0 <= n + k)%Z.
  destruct (Z_lt_le_dec m n); [exists (-m)%Z | exists (-n)%Z]; split;
  auto with zarith.
  destruct H.
  apply Qmult_le_r with (z := twopower_Q x). apply twopower_positive_Q.
  rewrite <- ?twopower_sum_Q.
  rewrite ?twopower_Z_Q_compat; [ | auto with zarith | auto with zarith].
  rewrite <- Zle_Qle.
  apply twopower_monotonic.
  auto with zarith.
Qed.


