Require Import QArith.
Require Import Qabs.
Require Import QOrderedType.

Require Import rearrange_tactic.
Require Import remedial.
Require Import qpos.
Require Import twopower.

Local Open Scope QPos.

(* The *binade* of a positive rational q is the greatest n such that
   2^n <= q.  In other words, it's the floor of log_2(q). *)

Definition QPos_lt_le_dec x y : { x < y } + { y <= x }
  := Qlt_le_dec (proj1_sig x) (proj1_sig y).

(* Write q = n / d, and suppose that 2^(a-1) <= n < 2^a, 2^(b-1) <= d < 2^b.
   Then 2^(a-b-1) < q < 2^(a-b+1).  So the binade is either a-b-1 or
   a-b, depending on whether q < 2^(a-b) or 2^(a-b) <= q. *)

Definition binade q :=
  (let trial_binade := 'Pos.size (QPos_num q) - 'Pos.size (QPos_den q) in
   if QPos_lt_le_dec q (twopower trial_binade)
   then trial_binade - 1 else trial_binade)%Z.


Lemma binade_bound q :
  twopower (binade q) <= q < twopower (binade q + 1).
Proof.
  unfold binade; set (n := QPos_num q); set (d := QPos_den q);
  destruct QPos_lt_le_dec as [ H | H ]; setoid_rewrite <- (num_over_den q);
  setoid_rewrite <- (num_over_den q) in H; split;
  subst n; subst d; revert H; generalize (QPos_num q), (QPos_den q);
  intros n d H.
  - apply QPos_lt_le_weak, QPos_div_mul_lt_l;
    apply QPos_lt_le_trans with (2 := pos_size_le _);
    rewrite QPos.mul_comm; apply QPos_div_mul_lt_l; rewrite <- twopower_div;
    match goal with | [ |- _ < twopower ?n ] => ring_simplify n end;
    apply pos_size_lt.
  - now match goal with | [ |- _ < twopower ?n ] => ring_simplify n end.
  - now match goal with | [ |- twopower ?n <= _ ] => ring_simplify n end.
  - apply QPos_div_mul_lt_r;
    apply QPos_lt_le_trans with (1 := pos_size_lt _);
    rewrite QPos.mul_comm; apply QPos_div_mul_le_r; rewrite <- twopower_div;
    match goal with | [ |- twopower ?n <= _ ] => ring_simplify n end;
    apply pos_size_le.
Qed.


Theorem twopower_binade_le n q : twopower n <= q  <->  (n <= binade q)%Z.
Proof.
  split; intro H.
  - apply Z.le_ngt; contradict H; apply QPos_lt_nge;
    apply QPos_lt_le_trans with (b := twopower (binade q + 1)).
    + apply binade_bound.
    + apply twopower_monotonic_le; omega.
  - apply QPos_le_trans with (b := twopower (binade q)).
    + apply twopower_monotonic_le; omega.
    + apply binade_bound.
Qed.

Add Parametric Morphism : binade
    with signature QPos.eq ==> eq as binade_morphism.
Proof.
  intros x y x_eq_y; apply Z.le_antisymm; apply twopower_binade_le;
  [rewrite <- x_eq_y | rewrite x_eq_y ]; apply twopower_binade_le;
  apply Z.le_refl.
Qed.

Theorem twopower_binade_lt n q : q < twopower n  <->  (binade q < n)%Z.
Proof.
  rewrite Z.lt_nge, QPos_lt_nge;
  split; intro H; contradict H; now apply twopower_binade_le.
Qed.

Theorem binade_monotonic q r : q <= r  -> (binade q <= binade r)%Z.
Proof.
  intro q_le_r. apply twopower_binade_le.
  apply QPos_le_trans with (b := q).
  apply binade_bound. easy.
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



Local Open Scope Q.

(* We define binadeQ for all nonzero numbers. *)

Definition binadeQ x (x_nonzero : ~(x == 0)) : Z :=
  binade (exist _ (Qabs x) (Qabs_nonzero x x_nonzero)).

(* Relationships between twopower and binade. *)

Lemma twopowerQ_binadeQ_lt n q (q_nonzero : ~(q == 0)) :
  Qabs q < twopowerQ n  <->  (binadeQ q q_nonzero < n)%Z.
Proof.
  unfold twopowerQ, binadeQ; now rewrite <- twopower_binade_lt.
Qed.

Lemma twopowerQ_binadeQ_le n q (q_nonzero : ~(q == 0)) :
  twopowerQ n <= Qabs q  <->  (n <= binadeQ q q_nonzero)%Z.
Proof.
  unfold twopowerQ, binadeQ; now rewrite <- twopower_binade_le.
Qed.

Lemma binadeQ_monotonic x (x_nonzero : ~(x == 0)) y (y_nonzero : ~(y == 0)) :
  Qabs x <= Qabs y  ->  (binadeQ x x_nonzero <= binadeQ y y_nonzero)%Z.
Proof.
  intro; unfold binadeQ; now apply binade_monotonic.
Qed.

Lemma binadeQ_equiv x (x_nonzero : ~(x == 0)) y (y_nonzero : ~(y == 0)) :
  x == y  ->  binadeQ x x_nonzero = binadeQ y y_nonzero.
Proof.
  intro H; unfold binadeQ; apply binade_morphism.
  unfold QPos.eq. simpl. now rewrite H.
Qed.

Lemma binadeQ_opp x (x_nonzero : ~(x == 0)) (neg_x_nonzero : ~(-x == 0)) :
  binadeQ x x_nonzero = binadeQ (-x) neg_x_nonzero.
Proof.
  unfold binadeQ; apply binade_morphism.
  unfold QPos.eq. setoid_replace (Qabs (-x)) with (Qabs x).
  reflexivity.
  apply Qabs_opp.
Qed.