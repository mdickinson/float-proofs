(* Remedial lemmas: basic facts, mostly about Z and Q, that aren't
   in the standard library. *)

Require Import Qabs.
Require Import rearrange_tactic.

Lemma negate_iff : forall P Q, (P <-> Q)  ->  (~P <-> ~Q).
Proof.
  tauto.
Qed.

Local Open Scope Z.

Lemma Zle_sign_flip_l (a b : Z) : -a <= b -> -b <= a.
Proof.
  intro; apply Zplus_le_reg_r with (p := b - a); now ring_simplify.
Qed.

Lemma Zle_not_eq (a b : Z) : a <= b -> ~(a = b) -> a < b.
Proof.
  auto with zarith.
Qed.

Local Open Scope Q.

Notation "x <> y" := (~ (x == y)) : Q_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Q_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Q_scope.
Notation "x < y < z" := (x < y /\ y < z) : Q_scope.
Notation "2" := (2#1) : Q_scope.

Lemma Qopp_le_mono (x y : Q) : x <= y  <->  -y <= -x.
Proof.
  split; intro; rearrange.
Qed.

Lemma Qopp_lt_mono (x y : Q) : x < y  <->  -y < -x.
Proof.
  split; intro; rearrange.
Qed.

Lemma Qlt_nge (x y : Q) : x < y <-> ~(y <= x).
  split; auto with qarith.
Qed.

Lemma Qle_not_eq (a b : Q) : a <= b -> ~(a == b) -> a < b.
Proof.
  auto with qarith.
Qed.

Lemma Qeq_le_incl (a b : Q) : a == b -> a <= b.
Proof.
  intro H; rewrite H; apply Qle_refl.
Qed.

Lemma Qabs_Zabs (x : Z) : Qabs (inject_Z x) == inject_Z (Z.abs x).
Proof.
  now unfold Qabs.
Qed.

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

Lemma Qdiv_eq_mult x y z : ~(z == 0) -> (x / z == y  <->  x == y * z).
Proof.
  intro; split; intro; [scale_by (/z) | scale_by z]; rearrange.
Qed.

Lemma Qmult_eq_div x y z : ~(z == 0) -> (x * z == y  <->  x == y / z).
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

Lemma Qabs_nonzero (x : Q) : ~(x == 0)  -> 0 < Qabs x.
Proof.
  intro H; apply Qle_not_eq.
  - apply Qabs_nonneg.
  - contradict H. apply Qabs_zero. now symmetry.
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

Lemma Qle_lt_eq x y :
  x <= y -> x < y \/ x == y.
Proof.
  case (Qeq_dec x y).
  - intros; now right.
  - intros; left; now apply Qle_not_eq.
Qed.

Lemma Qabs_nonzero_inv (x : Q) : 0 < Qabs x -> ~(x == 0).
Proof.
  apply Qabs_case; intros _ H1; intro H; now rewrite H in H1.
Qed.
