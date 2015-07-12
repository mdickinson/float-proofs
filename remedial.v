(* Remedial lemmas: basic facts, mostly about Z and Q, that aren't
   in the standard library. *)

Require Import Qabs.

Open Scope Q.

Notation "x <> y" := (~ (x == y)) : Q_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Q_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Q_scope.
Notation "x < y < z" := (x < y /\ y < z) : Q_scope.

Lemma lt_neg_switch x y : x < -y -> y < -x.
Proof.
  intro; apply Qplus_lt_l with (z := x - y); now ring_simplify.
Qed.

Lemma le_neg_switch x y : -x <= y  ->  -y <= x.
Proof.
  intro; apply Qplus_le_l with (z := y - x); now ring_simplify.
Qed.

Lemma le_neg_switch_r x y : x <= -y  ->  y <= -x.
Proof.
  intro; apply Qplus_le_l with (z := x - y); now ring_simplify.
Qed.

Lemma abs_nonzero (x : Q) : ~(x == 0)  -> 0 < Qabs x.
Proof.
  destruct (Q_dec x 0) as [[Hlt | Hgt] | Heq].
  - intros _. (* case x < 0 *)
    setoid_replace (Qabs x) with (-x) by (now apply Qabs_neg, Qlt_le_weak);
    now apply lt_neg_switch.
  - intros _. (* case 0 < x *)
    setoid_replace (Qabs x) with x by (now apply Qabs_pos, Qlt_le_weak);
    easy.
  - intuition. (* case x == 0 *)
Qed.

Lemma Qle_Qabs_neg x : -x <= Qabs x.
Proof.
  rewrite <- Qabs_opp; apply Qle_Qabs.
Qed.

Lemma Qdiv_le_mult x y z : 0 < z -> (x / z <= y  <->  x <= y * z).
Proof.
  intro; split; intro H0.
  - (* show x / z <= y  ->  x <= y * z *)
    apply Qmult_le_r with (z := / z); [ | setoid_replace (y * z * /z) with y by field];
    try (apply Qinv_lt_0_compat); auto with qarith.
  - (* x <= y * z -> x / z <= y *)
    apply Qmult_le_r with (z := z); [ | setoid_replace (x / z * z) with x by field];
    auto with qarith.
Qed.

Lemma Qmult_le_div x y z : 0 < z -> (x * z <= y  <->  x <= y / z).
Proof.
  intro; split; intro H0.
  - (* x * z <= y  ->  x <= y / z *)
    apply Qmult_le_r with (z := z); [ | field_simplify; field_simplify in H0];
    auto with qarith.
  - apply Qmult_le_r with (z := /z).
    apply Qinv_lt_0_compat.
    easy.
    field_simplify.
    field_simplify in H0.
    easy.
    revert H0.
    fold (~ (z == 0)).
    auto with qarith.
    auto with qarith.
    auto with qarith.
Qed.

Lemma Qle_ge_cases (x y : Q) : x <= y  \/  y <= x.
Proof.
  destruct (Qlt_le_dec x y); intuition.
Qed.

Lemma Qabs_zero (x : Q) : Qabs x == 0  ->  x == 0.
Proof.
  apply Qabs_case; intros _ H; [ | rewrite <- Qopp_opp]; rewrite H; easy.
Qed.

Lemma Qabs_div (a b : Q) :
  (~ b == 0) -> Qabs (a / b) == Qabs a / Qabs b.
Proof.
  intro; setoid_replace (Qabs a) with (Qabs (a / b) * Qabs b).
  - rewrite Qdiv_mult_l.
    + easy.
    + contradict H; now apply Qabs_zero.
  - rewrite <- Qabs_Qmult; setoid_replace (a / b * b) with a by field; easy.
Qed.
