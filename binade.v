Require Import ZArith.
Require Import QArith.

Require Import twopower.

Section binade_and_twopower.

Open Scope Z.

Definition binade_Z := Z.log2.

Lemma binade_monotonic : forall (m n : Z), m <= n -> binade_Z m <= binade_Z n.
Proof.
unfold binade_Z. apply Z.log2_le_mono.
Qed.

Lemma binade_nonnegative : forall (m : Z), 0 <= binade_Z m.
Proof.
unfold binade_Z. apply Z.log2_nonneg.
Qed.

Lemma twopower_binade_unit : forall (m : Z),
  0 <= m -> m = binade_Z (twopower_Z m).
Proof.
unfold binade_Z. unfold twopower_Z.
intros.
rewrite Z.log2_shiftl. trivial. omega. trivial.
Qed.

Lemma twopower_binade_counit : forall (n : Z),
  0 < n -> twopower_Z (binade_Z n) <= n.
Proof.
unfold binade_Z. unfold twopower_Z.
intros n n_is_positive.
assert (n = ' Z.to_pos n). symmetry. apply Z2Pos.id. trivial.
rewrite H. clear H. generalize (Z.to_pos n). clear n n_is_positive.
intro.
(* Target is now: Z.shiftl 1 (Z.log2 (' p)) <= ' p, where p : positive. *)
induction p as [q | q |].

destruct q; simpl in *; try (rewrite Pos.iter_succ).
apply Z.le_trans with (m := 2 * ' q~1). omega.
replace (' q~1~1) with (2 * 'q~1 + 1) by apply Pos2Z.inj_xI. omega.
apply Z.le_trans with (m := 2 * ' q~0). omega.
replace (' q~0~1) with (2 * 'q~0 + 1) by apply Pos2Z.inj_xI. omega.
omega.

destruct q; simpl in *; try (rewrite Pos.iter_succ).
apply Z.le_trans with (m := 2 * ' q~1). omega.
replace (' q~1~0) with (2 * 'q~1) by apply Pos2Z.inj_xO. omega.
apply Z.le_trans with (m := 2 * ' q~0). omega.
replace (' q~0~0) with (2 * 'q~0) by apply Pos2Z.inj_xO. omega.
omega.

simpl. omega.
Qed.

Lemma twopower_binade_adjunction : forall (n m : Z),
  0 < m -> 0 <= n ->
  (twopower_Z n <= m  <->  n <= binade_Z m).
Proof.
intros. split; intro.
apply Z.le_trans with (m := binade_Z (twopower_Z n)).
replace (binade_Z (twopower_Z n)) with n. omega. apply twopower_binade_unit. trivial.
apply binade_monotonic. trivial.
apply Z.le_trans with (m := twopower_Z (binade_Z m)).
apply twopower_monotonic. trivial.
apply twopower_binade_counit. trivial.
Qed.


Lemma twopower_binade_counit2 : forall (n : Z),
  0 < n -> n < twopower_Z (binade_Z n + 1).
Proof.
intros.
assert (not (binade_Z n + 1 <= binade_Z n)) by omega.
assert (not (twopower_Z (binade_Z n + 1) <= n)).
pose proof (twopower_binade_adjunction (binade_Z n + 1) n).
assert (0 <= binade_Z n + 1).
assert (0 <= binade_Z n) by apply binade_nonnegative. omega.
intuition. omega.
Qed.



Open Scope Q.

(* Definition of binade for rationals.

   Suppose x = m / n; we have

     2^binade(m) <= m < 2^(binade(m) + 1)
     2^binade(n) <= n < 2^(binade(n) + 1)

   so

     2^(binade(m) - binade(n) - 1) < m / n < 2^(binade(m) - binade(n) + 1).

   and we can define the binade of x to be:

     binade(m) - binade(n) if m / n >= 2^(binade(m) - binade(n))

   and

     binade(m) - binade(n) - 1 otherwise.

*)

Section binade_for_rationals.

Variable x : Q.

Let shift := (binade_Z (Qnum x) - binade_Z (' Qden x))%Z.

Definition binade_Q : Z :=
  if Qlt_le_dec x (twopower_Q shift)
  then (shift - 1)%Z
  else shift%Z.

End binade_for_rationals.

Lemma Qden_inverse : forall p : Z,
  (0 < p)%Z -> (' Qden (/ inject_Z p) = p).
Proof.
  unfold inject_Z. unfold Qinv. simpl.
  intros.
  case_eq p; intro.
    absurd (p = 0)%Z; auto with zarith.
    reflexivity.    
    intro.
    assert (p < 0)%Z.
    rewrite H0.
    apply Zlt_neg_0.
    absurd (0 < p)%Z; auto with zarith.
Qed.


Lemma Qnum_inverse : forall p : Z,
  (0 < p)%Z -> ((Qnum (/ inject_Z p)) = 1)%Z.
Proof.
  unfold inject_Z. unfold Qinv. simpl.
  intros.
  case_eq p; intro.
    absurd (p = 0)%Z; auto with zarith.
    reflexivity.
    intro.
    assert (p < 0)%Z.
    rewrite H0.
    apply Zlt_neg_0.
    absurd (0 < p)%Z; auto with zarith.
Qed.
    

Lemma twopower_binade_Q_unit : forall m : Z,
  m = binade_Q (twopower_Q m).
Proof.
  intro m. unfold binade_Q.
  remember ((binade_Z (Qnum (twopower_Q m)) -
             binade_Z (' Qden (twopower_Q m))))%Z as shift.
  cut (shift = m).
    (* completion of proof assuming shift = m *)
    intro; rewrite H; clear H.
    destruct (Qlt_le_dec (twopower_Q m) (twopower_Q m)).
    absurd (twopower_Q m < twopower_Q m); auto with qarith.
    reflexivity.

  rewrite Heqshift; clear Heqshift shift.
  unfold twopower_Q.
  destruct (Z_lt_le_dec m 0).
    (* m < 0 *)
    rewrite Qnum_inverse; [ | apply twopower_positive; auto with zarith].
    rewrite Qden_inverse; [ | apply twopower_positive; auto with zarith].
    simpl; rewrite <- twopower_binade_unit; auto with zarith.
    (* 0 <= m *)
    simpl; rewrite <- twopower_binade_unit; auto with zarith.
Qed.


Lemma Q_le_quotient : forall a b c d : Q,
  0 < a -> 0 < c -> a <= b -> c <= d -> a / d <= b / c.
Proof.
  intros a b c d a_positive c_positive a_le_b c_le_d.
  assert (0 < d) by (apply Qlt_le_trans with (y := c); assumption).
  apply Qmult_le_r with (z := c * d).
  setoid_replace 0 with (0 * d) by ring; apply Qmult_lt_r; assumption.
  setoid_replace (a / d * (c * d)) with (a * c) by field;
    [ | auto with qarith].
  setoid_replace (b / c * (c * d)) with (b * d) by field;
    [ | auto with qarith].
  apply Qle_trans with (y := a * d).
  apply Qmult_le_l; assumption.
  apply Qmult_le_r; assumption.
Qed.


Lemma Q_lt_quotient : forall a b c d : Q,
  0 < a -> 0 < c -> a < b -> c <= d -> a / d < b / c.
Proof.
  intros a b c d a_positive c_positive a_lt_b c_le_d.
  assert (0 < d) by (apply Qlt_le_trans with (y := c); assumption).
  apply Qmult_lt_r with (z := c * d).
  setoid_replace 0 with (0 * d) by ring; apply Qmult_lt_r; assumption.
  setoid_replace (a / d * (c * d)) with (a * c) by field;
    [ | auto with qarith].
  setoid_replace (b / c * (c * d)) with (b * d) by field;
    [ | auto with qarith].
  apply Qle_lt_trans with (y := a * d).
  apply Qmult_le_l; assumption.
  apply Qmult_lt_r; assumption.
Qed.


Lemma twopower_binade_Q_counit : forall x : Q, 0 < x ->
  twopower_Q (binade_Q x) <= x.
Proof.
  unfold binade_Q.
  intros x x_positive.
  remember (binade_Z (Qnum x) - binade_Z ('Qden x))%Z as shift.
  destruct (Qlt_le_dec _ _).
    (* case x < twopower_Q shift *)
    setoid_replace x with (inject_Z (Qnum x) / inject_Z (' Qden x))
      by (apply Qmake_Qdiv).
    setoid_replace (twopower_Q (shift - 1)) with
      (twopower_Q (binade_Z (Qnum x)) / twopower_Q (binade_Z (' Qden x) + 1)).
    apply Q_le_quotient. apply twopower_positive_Q. replace 0 with (inject_Z 0) by reflexivity. rewrite <- Zlt_Qlt. auto with zarith.
      (* proof that twopower_Q (binade_Z (Qnum x)) <= inject_Z (Qnum x) *)
      rewrite twopower_Z_Q_compat.
      rewrite <- Zle_Qle. apply twopower_binade_counit.
      revert x_positive; unfold Qlt; auto with zarith.
      simpl. auto with zarith.
      apply binade_nonnegative.
      (* proof that inject_Z (' Qden x) <= twopower_Q (binade_Z (' Qden x) + 1) *)
      rewrite twopower_Z_Q_compat.
      rewrite <- Zle_Qle.
      apply Z.lt_le_incl.
      apply twopower_binade_counit2.
      auto with zarith.
      apply Zle_trans with (m := binade_Z (' Qden x)).
      apply binade_nonnegative. auto with zarith.
   (* Now make good on the second setoid_replace above. *)
   rewrite twopower_div_Q.
   rewrite Heqshift.
   replace (binade_Z (Qnum x) - binade_Z (' Qden x) - 1)%Z with
           (binade_Z (Qnum x) - (binade_Z (' Qden x) + 1))%Z by ring.
   reflexivity. assumption.
Qed.

Arguments twopower_Q _ : simpl never.

Lemma twopower_binade_Q_counit2 : forall x : Q, 0 < x ->
  x < twopower_Q (binade_Q x + 1).
Proof.
  unfold binade_Q.
  intros x x_positive.
  remember (binade_Z (Qnum x) - binade_Z ('Qden x))%Z as shift.
  destruct (Qlt_le_dec _ _).
  (* case x < twopower_Q shift is disposed of easily. *)
  replace (shift - 1 + 1)%Z with shift by ring. assumption.
  (* case twopower_Q shift <= x *)
  setoid_replace x with (inject_Z (Qnum x) / inject_Z (' Qden x))
    by (apply Qmake_Qdiv).
  setoid_replace (twopower_Q (shift + 1)) with
    (twopower_Q (binade_Z (Qnum x) + 1) / twopower_Q (binade_Z (' Qden x))).
  apply Q_lt_quotient.
  replace 0 with (inject_Z 0) by reflexivity; rewrite <- Zlt_Qlt.
  revert x_positive; unfold Qlt; auto with zarith.
  simpl. auto with zarith.
  rewrite twopower_Z_Q_compat.
  replace 0 with (inject_Z 0) by reflexivity; rewrite <- Zlt_Qlt.
  apply twopower_positive.
  apply binade_nonnegative.
  apply binade_nonnegative.
  rewrite twopower_Z_Q_compat.
  rewrite <- Zlt_Qlt.
  apply twopower_binade_counit2.
  revert x_positive; unfold Qlt; auto with zarith.
  simpl. auto with zarith.
  apply Zle_trans with (m := binade_Z (Qnum x)).
  apply binade_nonnegative.
  auto with zarith.
  rewrite twopower_Z_Q_compat.
  rewrite <- Zle_Qle.
  apply twopower_binade_counit.
  revert x_positive; auto with zarith.
  apply binade_nonnegative.
  rewrite Heqshift.
  rewrite twopower_div_Q.
  replace (binade_Z (Qnum x) - binade_Z (' Qden x) + 1)%Z with
          (binade_Z (Qnum x) + 1 - binade_Z (' Qden x))%Z by ring.
  reflexivity.
Qed.

(* The above two lemmas serve to specify binade fully. *)

Lemma binade_Q_monotonic :
  forall x y : Q, 0 < x -> (x <= y -> (binade_Q x <= binade_Q y)%Z).
Proof.
intros.

(* we have:
   twopower (binade_Q x) <= x <= y < twopower(binade_Q y + 1),

   from which it follows that binade_Q < binade_Q y + 1
   (because otherwise we'd hvae binade_Q y + 1 <= binade_Q x,
    and twopower (binade_Q y + 1) <= twopower (binade_Q x),
    a contradiction).

*)

assert (twopower_Q (binade_Q x) < twopower_Q (binade_Q y + 1)).
apply Qle_lt_trans with (y := x).
apply twopower_binade_Q_counit. assumption.
apply Qle_lt_trans with (y := y).
assumption.
apply twopower_binade_Q_counit2.
apply Qlt_le_trans with (y := x). assumption. assumption.

(* Now divide into cases: either binade_Q x < binade_Q y + 1, or not. *)
destruct (Z_lt_le_dec (binade_Q x) (binade_Q y + 1)).
(* Case 1: binade_Q x < binade_Q y + 1.  Then the conclusion follows immediately. *)
auto with zarith.
(* Case 2: binade_Q y + 1 <= binade_Q x.  Then we should be able to reach a
   contradiction. *)
assert (twopower_Q (binade_Q y + 1) <= twopower_Q (binade_Q x)).
apply twopower_Q_monotonic. assumption.
assert (twopower_Q (binade_Q x) < twopower_Q (binade_Q x)).
apply Qlt_le_trans with (y := twopower_Q (binade_Q y + 1)).
assumption. assumption.
revert H3.
generalize (twopower_Q (binade_Q x)).
intros.
absurd (q < q). auto with qarith. assumption.
Qed.


Lemma twopower_Q_binade_adjunction :
  forall (x : Q) (n : Z), 0 < x ->
  (twopower_Q n <= x  <->  (n <= binade_Q x)%Z).
Proof.
intros x n x_positive.
split.
  intro.
  apply Z.le_trans with (m := binade_Q (twopower_Q n)).
    rewrite <- twopower_binade_Q_unit. auto with zarith.
    apply binade_Q_monotonic. apply twopower_positive_Q. assumption.

  intro.
  apply Qle_trans with (y := twopower_Q (binade_Q x)).
    apply twopower_Q_monotonic. assumption.
    apply twopower_binade_Q_counit. assumption.
Qed.

Lemma binade_well_defined :
  forall x y : Q, 0 < x ->
  (x == y) -> (binade_Q x = binade_Q y).
Proof.
  intros x y x_positive x_eq_y.
  assert (0 < y) as y_positive by (rewrite <- x_eq_y; assumption).

  assert (binade_Q x <= binade_Q y)%Z.
  apply twopower_Q_binade_adjunction. assumption.
  rewrite <- x_eq_y.
  apply twopower_Q_binade_adjunction. assumption.
  auto with zarith.

  assert (binade_Q y <= binade_Q x)%Z.
  apply twopower_Q_binade_adjunction.  assumption.
  rewrite x_eq_y.
  apply twopower_Q_binade_adjunction.  assumption.
  auto with zarith.

  auto with zarith.
Qed.


End binade_and_twopower.
