(* Remedial lemmas: basic facts, mostly about Z and Q, that aren't
   in the standard library. *)

Require Import Qabs.
Require Import rearrange_tactic.

Local Open Scope Q.

Notation "x <> y" := (~ (x == y)) : Q_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Q_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Q_scope.
Notation "x < y < z" := (x < y /\ y < z) : Q_scope.

Lemma lt_neg_switch x y : x < -y -> y < -x.
Proof.
  rearrange.
Qed.

Lemma le_neg_switch x y : -x <= y  ->  -y <= x.
Proof.
  rearrange.
Qed.

Lemma le_neg_switch_r x y : x <= -y  ->  y <= -x.
Proof.
  rearrange.
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
  intro; split; intro; [scale_by (/z) | scale_by z]; rearrange.
Qed.

Lemma Qmult_le_div x y z : 0 < z -> (x * z <= y  <->  x <= y / z).
Proof.
  intro; split; intro; [scale_by z | scale_by (/z)]; rearrange.
Qed.

Lemma Qdiv_lt_mult x y z : 0 < z -> (x / z < y  <->  x < y * z).
Proof.
  intro; split; intro; [scale_by (/z) | scale_by z]; rearrange.
Qed.

Lemma Qmult_lt_div x y z : 0 < z -> (x * z < y  <->  x < y / z).
Proof.
  intro; split; intro; [scale_by z | scale_by (/z)]; rearrange.
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

Definition Qle_dec x y : { x <= y } + {~ (x <= y) }.
Proof.
  destruct (Qlt_le_dec y x).
  - right; now apply Qlt_not_le.
  - now left.
Defined.
