Require Import QArith.
Require Import Qabs.

Require Import remedial.
Require Import twopower.

Local Open Scope Q.

(* Some tactics for dealing with powers of 2. *)

Ltac twopower_l_to_r :=
  match goal with
  | [ |- _ * twopowerQ _ == _ ] => apply Qmult_eq_div
                                   with (1 := twopowerQ_nonzero _)
  | [ |- _ / twopowerQ _ == _ ] => apply Qdiv_eq_mult
                                   with (1 := twopowerQ_nonzero _)
  | [ |- _ * twopowerQ _ <= _ ] => apply Qmult_le_div
                                   with (1 := twopowerQ_positive _)
  | [ |- _ / twopowerQ _ <= _ ] => apply Qdiv_le_mult
                                   with (1 := twopowerQ_positive _)
  | [ |- _ * twopowerQ _ < _ ] => apply Qmult_lt_div
                                   with (1 := twopowerQ_positive _)
  | [ |- _ / twopowerQ _ < _ ] => apply Qdiv_lt_mult
                                   with (1 := twopowerQ_positive _)
  end.

Ltac twopower_r_to_l :=
  match goal with
  | [ |- _ == _ / twopowerQ _ ] => apply Qmult_eq_div
                                   with (1 := twopowerQ_nonzero _)
  | [ |- _ == _ * twopowerQ _ ] => apply Qdiv_eq_mult
                                   with (1 := twopowerQ_nonzero _)
  | [ |- _ <= _ / twopowerQ _ ] => apply Qmult_le_div
                                   with (1 := twopowerQ_positive _)
  | [ |- _ <= _ * twopowerQ _ ] => apply Qdiv_le_mult
                                   with (1 := twopowerQ_positive _)
  | [ |- _ < _ / twopowerQ _ ] => apply Qmult_lt_div
                                   with (1 := twopowerQ_positive _)
  | [ |- _ < _ * twopowerQ _ ] => apply Qdiv_lt_mult
                                   with (1 := twopowerQ_positive _)
  end.

Ltac twopower_prepare :=
  try match goal with
      | [ |- - (?n / twopowerQ ?e) <= _ ] =>
        setoid_replace (- (n / twopowerQ e)) with ((-n) / twopowerQ e)
          by (field; apply twopowerQ_nonzero)
      | [ |- _ <= - (?n / twopowerQ ?e)] =>
        setoid_replace (- (n / twopowerQ e)) with ((-n) / twopowerQ e)
          by (field; apply twopowerQ_nonzero)
      | [ |- - (?n * twopowerQ ?e) <= _ ] =>
        setoid_replace (- (n * twopowerQ e)) with ((-n) * twopowerQ e) by ring

      | [ |- Qabs (_ / twopowerQ _) <= _ ] =>
        rewrite Qabs_div, Qabs_twopowerQ; [ | apply twopowerQ_nonzero ]
      | [ |- Qabs (_ / twopowerQ _) < _ ] =>
        rewrite Qabs_div, Qabs_twopowerQ; [ | apply twopowerQ_nonzero ]
      | [ |- _ <= Qabs(_ / twopowerQ _) ] =>
        rewrite Qabs_div, Qabs_twopowerQ; [ | apply twopowerQ_nonzero ]
      | [ |- Qabs (_ * twopowerQ _) < _ ] =>
        rewrite Qabs_Qmult, Qabs_twopowerQ
      end.

(* Tactics to be applied post moving powers of two around. *)

Ltac twopower_collect :=
  try match goal with
      | [ |- _ <= twopowerQ _ * twopowerQ _ ] => rewrite <- twopowerQ_mul
      | [ |- _ < twopowerQ _ * twopowerQ _ ] => rewrite <- twopowerQ_mul
      | [ |- _ <= twopowerQ _ / twopowerQ _ ] => rewrite <- twopowerQ_div
      | [ |- _ < twopowerQ _ / twopowerQ _ ] => rewrite <- twopowerQ_div
      | [ |- twopowerQ _ / twopowerQ _ == _ ] => rewrite <- twopowerQ_div
      | [ |- twopowerQ _ / twopowerQ _ <= _ ] => rewrite <- twopowerQ_div
      | [ |- twopowerQ _ * twopowerQ _ <= _ ] => rewrite <- twopowerQ_mul
      | [ |- twopowerQ _ * twopowerQ _ < _ ] => rewrite <- twopowerQ_mul
      | [ |- _ / twopowerQ _ * twopowerQ _ <= _ ] =>
        unfold Qdiv; rewrite <- twopowerQ_inv;
        rewrite <- Qmult_assoc; rewrite <- twopowerQ_mul
      | [ |- _ <= _ * twopowerQ _ / twopowerQ _] =>
        unfold Qdiv; rewrite <- twopowerQ_inv;
        rewrite <- Qmult_assoc; rewrite <- twopowerQ_mul
      | [ |- _ == _ * twopowerQ _ / twopowerQ _] =>
        unfold Qdiv; rewrite <- twopowerQ_inv;
        rewrite <- Qmult_assoc; rewrite <- twopowerQ_mul
      end.

Ltac twopower_exponent_simplify :=
  try match goal with
      | [ |- _ == _ * twopowerQ ?e ] => ring_simplify e
      | [ |- _ <= twopowerQ ?e ] => ring_simplify e
      | [ |- _ <= _ * twopowerQ ?e ] => ring_simplify e
      | [ |- twopowerQ ?e <= _ ] => ring_simplify e
      | [ |- _ * twopowerQ ?e <= _ ] => ring_simplify e
      | [ |- _ < twopowerQ ?e ] => ring_simplify e
      | [ |- twopowerQ ?e < _ ] => ring_simplify e
      | [ |- _ < _ * twopowerQ ?e ] => ring_simplify e
      | [ |- _ * twopowerQ ?e < _ ] => ring_simplify e
      end.

Ltac twopower_cleanup :=
  try match goal with
      | [ |- _ * twopowerQ 0 <= _ ] => replace (twopowerQ 0) with 1 by easy;
          rewrite Qmult_1_r
      | [ |- _ == _ * twopowerQ 0 ] => replace (twopowerQ 0) with 1 by easy;
          rewrite Qmult_1_r
      | [ |- _ <= _ * twopowerQ 0 ] => replace (twopowerQ 0) with 1 by easy;
          rewrite Qmult_1_r
      | [ |- 0 * twopowerQ _ <= _ ] => rewrite Qmult_0_l
      | [ |- _ <= 0 * twopowerQ _ ] => rewrite Qmult_0_l
      end.


Ltac twopower_left := twopower_prepare; twopower_r_to_l; twopower_collect;
                      twopower_exponent_simplify; twopower_cleanup.
Ltac twopower_right := twopower_prepare; twopower_l_to_r; twopower_collect;
                       twopower_exponent_simplify; twopower_cleanup.
