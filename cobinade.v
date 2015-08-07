Require Import QArith.

Require Import qpos.
Require Import twopower.

Local Open Scope QPos.

(* The *cobinade* of a positive rational q is the least n such that
   q <= 2^n.  In other words, it's the ceiling of log_2(q). *)

(* Computing: suppose that q = n / d, 2^e <= n < 2^(e+1)
   and 2^f <= d < 2^(f+1).  Then

     2^(e-f-1) < n/d < 2^(e-f+1)

   So if n / d <= 2^(e-f) then the cobinade is e - f.  Otherwise it's e - f +
   1. *)

Definition QPos_le_dec x y : { x <= y } + {~ (x <= y) }.
Proof.
  case_eq (QPos.leb x y); intro.
  - left; now apply QPos.leb_le.
  - right; intro;
    assert (x <=? y = true) by (now apply QPos.leb_le); congruence.
Defined.

Definition cobinade q :=
  let trial_cobinade := ('Pos.size (QPos_num q) - 'Pos.size (QPos_den q))%Z in
  if QPos_le_dec q (twopower trial_cobinade)
  then trial_cobinade else (trial_cobinade + 1)%Z.

Lemma trial_cobinade_bound q :
  let trial_cobinade := ('Pos.size (QPos_num q) - 'Pos.size (QPos_den q))%Z in
  twopower (trial_cobinade - 1) < q < twopower (trial_cobinade + 1).
Proof.
  intros; split;
  setoid_replace q
  with (QPos_from_pos (QPos_num q) / QPos_from_pos (QPos_den q))
    by (symmetry; apply num_over_den); subst trial_cobinade;
  generalize (QPos_num q) as n; generalize (QPos_den q) as d; intros.

  - setoid_replace (twopower (' Pos.size n - ' Pos.size d - 1))
    with (twopower (' Pos.size n - 1 ) / twopower (' Pos.size d )).
    + apply QPos_div_le_lt.
      * apply pos_size_le.
      * apply pos_size_lt.
    + rewrite <- twopower_div; f_equiv; ring.
  - setoid_replace (twopower (' Pos.size n - ' Pos.size d + 1))
    with (twopower (' Pos.size n) / twopower (' Pos.size d - 1)).
    + apply QPos_div_lt_le.
      * apply pos_size_lt.
      * apply pos_size_le.
    + rewrite <- twopower_div; f_equiv; ring.
Qed.

Lemma cobinade_bound q :
  twopower (cobinade q - 1) < q <= twopower (cobinade q).
Proof.
  unfold cobinade; destruct (QPos_le_dec q).
  - split.
    + apply trial_cobinade_bound.
    + assumption.
  - split.
    + apply QPos_lt_nge; now ring_simplify
        (' Pos.size (QPos_num q) - ' Pos.size (QPos_den q) + 1 - 1)%Z.
    + apply QPos_lt_le_weak; apply trial_cobinade_bound.
Qed.


Theorem twopower_cobinade_le n q :
  q <= twopower n  <->  (cobinade q <= n)%Z.
Proof.
  split; intro H.
  - apply Z.lt_pred_le, twopower_injective_lt,
      QPos_lt_le_trans with (2 := H), cobinade_bound.
  - apply QPos_le_trans with (b := twopower (cobinade q)).
    + apply cobinade_bound.
    + now apply twopower_monotonic_le.
Qed.


Theorem twopower_cobinade_lt n q :
  twopower n < q  <->  (n < cobinade q)%Z.
Proof.
  split; intro H.
  - apply twopower_injective_lt, QPos_lt_le_trans with (1 := H),
                                                       cobinade_bound.
  - apply QPos_le_lt_trans with (b := twopower (cobinade q - 1)).
    + apply twopower_monotonic_le; omega.
    + apply cobinade_bound.
Qed.


Add Parametric Morphism : cobinade
    with signature QPos.eq ==> eq as cobinade_morphism.
Proof.
  intros x y x_eq_y; apply Z.le_antisymm; apply twopower_cobinade_le;
  (rewrite x_eq_y || rewrite <- x_eq_y); apply twopower_cobinade_le; omega.
Qed.


Theorem cobinade_monotonic q r : q <= r  ->  (cobinade q <= cobinade r)%Z.
Proof.
  intro q_le_r; apply twopower_cobinade_le;
  apply QPos_le_trans with (1 := q_le_r);
  apply twopower_cobinade_le; omega.
Qed.
