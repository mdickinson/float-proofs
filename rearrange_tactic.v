Require Import QArith.

Local Open Scope Q.


SearchAbout (/_).

Lemma Qinv_nonzero q : ~(q == 0) -> ~(/q == 0).
Proof.
  intro H; contradict H; rewrite <- Qinv_involutive; now rewrite H.
Qed.

Ltac discharge_positivity_constraints :=
  match goal with
  | [ _ : 0 < ?z |- ~(?z == 0) ] => apply Qnot_eq_sym, Qlt_not_eq; assumption
  | [ _ : 0 < ?z |- 0 < / ?z ] => apply Qinv_lt_0_compat; assumption
  | [ _ : 0 < ?z |- 0 < ?z ] => assumption
  | [ _ : ~(?z == 0) |- ~(?z == 0) ] => assumption
  | [ _ : ~(?z == 0) |- ~(/?z == 0) ] => apply Qinv_nonzero; assumption
  | [ _ : 0 < ?z |- ~(/?z == 0) ] =>
    apply Qinv_nonzero, Qnot_eq_sym, Qlt_not_eq; assumption
  end.

Ltac field_pos := field; discharge_positivity_constraints.

Ltac scale_by multiplier :=
  match goal with
  | [ |- _ == _ ] => apply Qmult_inj_r with (z := multiplier);
      [discharge_positivity_constraints | ]
  | [ |- _ <= _ ] => apply Qmult_le_r with (z := multiplier);
      [discharge_positivity_constraints | ]
  | [ |- _ < _ ] => apply Qmult_lt_r with (z := multiplier);
      [discharge_positivity_constraints | ]
  end.


Lemma _rearrange_eq_l a b c d :
  a == b  ->  b + c == a + d  ->  c == d.
Proof.
  intro a_eq_b; rewrite a_eq_b; apply Qplus_inj_l.
Qed.

Lemma _rearrange_eq_r a b c d :
  a == b  ->  b + d == a + c  ->  c == d.
Proof.
  intros a_eq_b H; symmetry; now apply _rearrange_eq_l with (1 := a_eq_b).
Qed.

Ltac rearrange_eq :=
  match goal with
  | [ H : _ == _ |- _ == _ ] =>
      (apply _rearrange_eq_r with (1 := H); (ring || field_pos))
      ||
      (apply _rearrange_eq_l with (1 := H); (ring || field_pos))
  | [ |- _ == _ ] => (ring || field_pos)
  end.

Lemma _rearrange_le a b c d :
  a <= b  ->  b + c == a + d  ->  c <= d.
Proof.
  intros; apply Qplus_le_r with (z := a - c).
  setoid_replace (a - c + c) with a by (idtac; rearrange_eq).
  setoid_replace (a - c + d) with b by (idtac; rearrange_eq).
  assumption.
Qed.

Lemma _rearrange_lt a b c d :
  a < b  ->  b + c == a + d  ->  c < d.
Proof.
  intros; apply Qplus_lt_r with (z := a - c).
  setoid_replace (a - c + d) with b by (idtac; rearrange_eq).
  setoid_replace (a - c + c) with a by (idtac; rearrange_eq).
  assumption.
Qed.


Ltac rearrange_le :=
  match goal with
  | [ H : _ <= _ |- _ <= _ ] => apply _rearrange_le with (1 := H);
      (ring || field_pos)
  end.

Ltac rearrange_lt :=
  match goal with
  | [ H : _ < _ |- _ < _ ] => apply _rearrange_lt with (1 := H);
      (ring || field_pos)
  end.

Ltac rearrange := intros; (rearrange_eq || rearrange_lt || rearrange_le).

(* Tactic to replace the goal with an equivalent one by rearrangement. *)

Ltac rearrange_goal new_goal :=
  let H := fresh "H" in
    assert new_goal as H; [ | rearrange ].

(* Testing the tactic. *)

Lemma test_rearrange1 a b : a + 1 == b + 1  ->  a == b.
Proof.
  rearrange.
Qed.

Lemma test_rearrange2 a b c : a == b - c  ->  c + a == b.
Proof.
  rearrange.
Qed.

Lemma test_rearrange3 a b c : a == b + c  ->  b == a - c.
Proof.
  rearrange.
Qed.

Lemma test_rearrange4 a b c : a == b + c ->  c == b  ->  b == a - c.
Proof.
  rearrange.
Qed.

Lemma test_rearrange5 a b c : c == b  ->  a - 1 == b + c  ->  1 + b == a - c.
Proof.
  rearrange.
Qed.

Lemma test_rearrange_assoc a b c :
  a + (b - c) == 1  ->  (a + b) - c == 1.
Proof.
  rearrange.
Qed.

Lemma test_rearrange_lt_1 a b c : a < b + c  ->  a - c < b.
Proof.
  rearrange.
Qed.

Lemma test_rearrange_lt_2 a b c d : a + b < c + d  ->  b - d < c - a.
Proof.
  rearrange.
Qed.

Lemma test_rearrange_le_1 a b c d : a + b <= c + d  ->  b - d <= c - a.
Proof.
  rearrange.
Qed.
