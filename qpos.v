Require Import OrdersFacts.
Require Import OrdersTac.
Require Import QArith.
Require Import QOrderedType.

(* Auxiliary facts about Q that don't seem to be readily to
   hand in the standard library. *)

Open Scope Q.

Lemma Q_mul_pos_pos : forall p q : Q, 0 < p -> 0 < q -> 0 < p * q.
Proof.
  intros p q; unfold Qlt; simpl; rewrite ?Z.mul_1_r; apply Z.mul_pos_pos.
Qed.


Definition QPos := { x : Q | 0 < x }.

Delimit Scope QPos_scope with QPos.

Open Scope QPos.

Module Type OrderedTypeFullWithOrderFunctions :=
  OrderedTypeFull <+ HasBoolOrdFuns <+ BoolOrdSpecs.

Module QPos
 <: BooleanDecidableType
 <: OrderedTypeFullWithOrderFunctions
 <: LtBool
 <: TotalOrder.

Definition t := QPos.

Local Notation "!" := proj1_sig.

Definition eq (p q : t) := (!p == !q)%Q.
Definition lt (p q : t) := (!p < !q)%Q.
Definition le (p q : t) := (!p <= !q)%Q.
Definition compare (p q : t) := (!p ?= !q)%Q.

Infix "==" := eq : QPos_scope.
Infix "<" := lt : QPos_scope.
Infix "<=" := le : QPos_scope.
Infix "?=" := compare (at level 70, no associativity) : QPos_scope.

Instance eq_equiv : Equivalence eq.
Proof.
  split; unfold eq; [intros p | intros p q | intros p q r]; apply Q_Setoid.
Qed.

Instance lt_strorder : StrictOrder lt.
Proof.
  split; unfold lt; [ intros q ; unfold complement | intros p q r];
  apply QOrder.TO.lt_strorder.
Qed.

Instance lt_compat : Proper (eq==>eq==>iff) lt.
Proof.
  split; unfold lt; unfold eq in H, H0; rewrite H; rewrite H0; trivial.
Qed.

Lemma le_lteq p q : p <= q <-> p < q \/ p == q.
Proof. split; unfold eq, le, lt; apply Qle_lteq. Qed.

Lemma lt_total p q : p < q \/ p == q \/ q < p.
Proof. unfold eq, lt; apply QOrder.TO.lt_total. Qed.

Lemma eq_dec p q : { p == q } + { ~ p == q }.
Proof. unfold eq; apply QOrder.TO.eq_dec. Qed.

Definition eqb p q := if eq_dec p q then true else false.
Definition leb p q := match p ?= q with | Gt => false | _ => true end.
Definition ltb p q := match p ?= q with | Lt => true | _ => false end.

Infix "=?" := eqb (at level 70, no associativity) : QPos_scope.
Infix "<=?" := leb (at level 70, no associativity) : QPos_scope.
Infix "<?" := ltb (at level 70, no associativity) : QPos_scope.

Lemma eqb_eq p q : (p =? q) = true <-> p == q.
Proof. unfold eq, eqb; destruct (eq_dec p q); intuition. Qed.

Lemma ltb_lt p q : (p <? q) = true <-> p < q.
Proof.
  unfold ltb, lt, compare; rewrite Qlt_alt; case (!p ?= !q)%Q; split; easy.
Qed.

Lemma leb_le p q : (p <=? q) = true <-> p <= q.
Proof.
  unfold leb, le, compare; rewrite Qle_alt; case (!p ?= !q)%Q; split; easy'.
Qed.

Lemma compare_spec p q : CompareSpec (p == q) (p < q) (q < p) (p ?= q).
Proof.
  unfold eq, lt, compare; case Qcompare_spec; now constructor.
Qed.

Include OrderedTypeFullFacts.

(* Arithmetic *)

Definition one : t.
  refine (exist _ (inject_Z 1) _); easy.
Defined.

Definition two : t.
  refine (exist _ (inject_Z 2) _); easy.
Defined.

Notation "1" := one : QPos_scope.
Notation "2" := two : QPos_scope.

(* Multiplication: definition and order. *)

Definition mul (p q : t) : t.
  refine (exist _ (!p * !q) _); destruct p, q; now apply Q_mul_pos_pos.
Defined.

Infix "*" := mul : QPos_scope.

(* Basic facts about multiplication. *)

Lemma mul_assoc p q r : p * (q * r) == (p * q) * r.
Proof.
  apply Qmult_assoc.
Qed.

Lemma mul_comm p q : p * q == q * p.
Proof.
  apply Qmult_comm.
Qed.

Lemma mul_1_l p : 1 * p == p.
Proof.
  apply Qmult_1_l.
Qed.

Lemma mul_1_r p : p * 1 == p.
Proof.
  apply Qmult_1_r.
Qed. 

(* Multiplication and order. *)

Lemma mul_le_mono_l p q r : q <= r  <->  p * q <= p * r.
Proof.
  split; apply Qmult_le_l; now destruct p.
Qed.

Lemma mul_le_mono_r p q r : q <= r  <->  q * p <= r * p.
Proof.
  split; apply Qmult_le_r; now destruct p.
Qed.

Lemma mul_lt_mono_l p q r :  q < r  <->  p * q < p * r.
Proof.
  split; apply Qmult_lt_l; now destruct p.
Qed.

Lemma mul_lt_mono_r p q r :  q < r  <->  q * p < r * p.
Proof.
  split; apply Qmult_lt_r; now destruct p.
Qed.

(* Reciprocal. *)

Definition inv (p : t) : t.
  refine (exist _ (/ !p)%Q _); apply Qinv_lt_0_compat; now destruct p.
Defined.

Notation "/ x" := (inv x).

Lemma mul_inv_r p : p * /p == 1.
Proof.
  apply Qmult_inv_r; destruct p; simpl; QOrder.order.
Qed.

(* Division. *)

Definition div (p q : t) : t := p * /q.

Infix "/" := div : QPos_scope.

(* QPos and the positive type. *)

Definition from_pos (m : positive) : t.
  refine (exist _ (inject_Z (' m)) _); apply Pos2Z.is_pos.
Defined.

Lemma as_fraction (p : t) :
  exists (m n : positive), p == (from_pos m) / (from_pos n).
Proof.
  destruct p; exists (Z.to_pos (Qnum x)), (Qden x); unfold eq; simpl; rewrite Z2Pos.id.
  unfold Qeq; simpl; ring.
  unfold Qlt in q; simpl in q; ring_simplify in q; easy.
Qed.

End QPos.

(* Re-export notations. *)

Infix "==" := QPos.eq : QPos_scope.
Infix "<" := QPos.lt : QPos_scope.
Infix "<=" := QPos.le : QPos_scope.
Notation "p > q" := (q < p) (only parsing) : QPos_scope.
Notation "p >= q" := (q <= p) (only parsing) : QPos_scope.
Notation "p <> q" := (~p==q) (at level 70, no associativity) : QPos_scope.

Infix "?=" := QPos.compare (at level 70, no associativity) : QPos_scope.
Infix "=?" := QPos.eqb (at level 70, no associativity) : QPos_scope.
Infix "<=?" := QPos.leb (at level 70, no associativity) : QPos_scope.
Infix "<?" := QPos.ltb (at level 70, no associativity) : QPos_scope.

Infix "*" := QPos.mul : QPos_scope.
Infix "/" := QPos.div : QPos_scope.
Notation "/ p" := (QPos.inv p) : QPos_scope.

Notation "1" := QPos.one : QPos_scope.
Notation "2" := QPos.two : QPos_scope.

Notation "x <= y < z" := ((x <= y) /\ (y < z)) : QPos_scope.

(* Additional results about QPos. *)

Lemma QPos_le_eq p q : p == q  ->  p <= q.
Proof.
  intro p_eq_q. rewrite p_eq_q. unfold QPos.le. destruct q. simpl. auto with qarith.
Qed.


Lemma QPos_le_antisymm q r : q <= r -> r <= q -> q == r.
Proof.
  unfold QPos.le, QPos.eq; destruct q, r; simpl.
  auto with qarith.
Qed.


Lemma QPos_le_refl q : q <= q.
Proof.
  unfold QPos.le; destruct q; simpl; auto with qarith.
Qed.


(* Positive rationals to and from positive integers. *)

Definition QPos_num (q : QPos) : positive := Z.to_pos (Qnum (proj1_sig q)).
Definition QPos_den (q : QPos) : positive := Qden (proj1_sig q).

Definition QPos_from_pos (p : positive) : QPos.
  refine (exist _ (inject_Z (' p)) _); apply Pos2Z.is_pos.
Defined.


Lemma QPos_num_positive (q : Q) : (0 < q)%Q -> ('Z.to_pos (Qnum q) = Qnum q)%Z.
Proof.
  intros q_positive; apply Z2Pos.id; revert q_positive;
  unfold Qlt; now rewrite Z.mul_1_r.
Qed.

Lemma Q_as_fraction (q : Q) : (inject_Z (Qnum q) / inject_Z (' Qden q) == q)%Q.
Proof.
  unfold Qeq; simpl; ring.
Qed.

Lemma num_over_den : forall q : QPos,
  QPos_from_pos (QPos_num q) / QPos_from_pos (QPos_den q) == q.
Proof.
  intro q. destruct q.
  unfold QPos.eq, QPos.div, QPos_num, QPos_den. simpl.
  rewrite QPos_num_positive; [ | easy].
  apply Q_as_fraction.
Qed.


Instance QPos_Setoid : Equivalence QPos.eq.
Proof.
  split; unfold QPos.eq; intro; [reflexivity | now symmetry |
    intros y z; now transitivity (proj1_sig y)].
Qed.

Add Morphism QPos.lt : QPos_lt_morphism.
Proof.
  unfold QPos.lt, QPos.eq.
  destruct x, y. simpl. intro.
  destruct x1, y0. simpl. intro.
  rewrite H. rewrite H0. reflexivity.
Qed.

Add Morphism QPos.le : QPos_le_morphism.
Proof.
  unfold QPos.le, QPos.eq.
  destruct x, y. simpl. intro.
  destruct x1, y0. simpl. intro.
  rewrite H. rewrite H0. reflexivity.
Qed.

Add Morphism QPos.mul : QPos_mul_morphism.
  unfold QPos.eq; simpl; intros; rewrite H; now rewrite H0.
Qed.

Add Morphism QPos.div : QPos_div_morphism.
  unfold QPos.eq; simpl; intros; rewrite H; now rewrite H0.
Qed.


Lemma QPos_from_pos_lt : forall p q, (p < q)%positive  -> QPos_from_pos p < QPos_from_pos q.
Proof.
  intros; unfold QPos.lt; simpl; rewrite <- Zlt_Qlt; unfold Zlt;
  now apply Pos.compare_lt_iff.
Qed.

Lemma QPos_from_pos_le : forall p q, (p <= q)%positive ->
  QPos_from_pos p <= QPos_from_pos q.
Proof.
  intros. unfold QPos.le. simpl. rewrite <- Zle_Qle. unfold Zle.
  now apply Pos.compare_le_iff.
Qed.

Lemma QPos_mul_inv_l p : /p * p == 1.
Proof.
  rewrite QPos.mul_comm. apply QPos.mul_inv_r.
Qed.

Lemma QPos_div_mul b c : b / c * c == b.
Proof.
  unfold QPos.div.
  rewrite <- QPos.mul_assoc. rewrite QPos_mul_inv_l.
  apply QPos.mul_1_r.
Qed.

Lemma QPos_mul_div b c : b * c / c == b.
Proof.
  unfold QPos.div.
  rewrite <- QPos.mul_assoc.
  rewrite QPos.mul_inv_r.
  apply QPos.mul_1_r.
Qed.

Lemma QPos_div_mul_r a b c : a == b / c  <->  a * c == b.
  split; intro; [rewrite H | rewrite <- H].
  apply QPos_div_mul. symmetry.  apply QPos_mul_div.
Qed.

Lemma QPos_div_mul_le_r a b c : b / c <= a  <->  b <= a * c.
Proof.
  rewrite QPos.mul_le_mono_r with (p := c).
  setoid_replace (b / c * c) with b. easy.
  apply QPos_div_mul.
Qed.

Lemma QPos_div_mul_le_l a b c : a <= b / c  <->  a * c <= b.
Proof.
  rewrite QPos.mul_le_mono_r with (p := c).
  setoid_replace (b / c * c) with b. easy.
  apply QPos_div_mul.
Qed.

Lemma QPos_div_mul_lt_l a b c : a < b / c  <->  a * c < b.
Proof.
  rewrite QPos.mul_lt_mono_r with (p := c).
  setoid_replace (b / c * c) with b. easy.
  apply QPos_div_mul.
Qed.

Lemma QPos_div_mul_lt_r a b c : b / c < a  <->  b < a * c.
Proof.
  rewrite QPos.mul_lt_mono_r with (p := c).
  setoid_replace (b / c * c) with b. easy.
  apply QPos_div_mul.
Qed.

Lemma QPos_from_pos_one : QPos_from_pos 1 == 1.
Proof.
  easy.
Qed.

Lemma QPos_from_pos_two : QPos_from_pos 2 == 2.
Proof.
  easy.
Qed.

Lemma QPos_from_pos_mul: forall p q, QPos_from_pos (p * q) == QPos_from_pos p * QPos_from_pos q.
Proof.
  unfold QPos.eq. intros. simpl. easy.
Qed.


Lemma QPos_lt_le_weak : forall p q, p < q  -> p <= q.
Proof.
  unfold QPos.le, QPos.lt; intros p q; destruct p, q; auto with qarith.
Qed.



Lemma QPos_le_lt_trans a b c : a <= b -> b < c -> a < c.
Proof.
  unfold QPos.le, QPos.lt. destruct a, b, c. simpl.
  apply Qle_lt_trans.
Qed.

Lemma QPos_mul_le_lt a b c d : a <= c -> d < b  ->  a * d < c * b.
Proof.
  intros; apply QPos_le_lt_trans with (b := c * d);
  [now apply QPos.mul_le_mono_r | now apply QPos.mul_lt_mono_l].
Qed.

Lemma QPos_div_le_lt a b c d : a <= c -> d < b  ->  a / b < c / d.
Proof.
  intros.
  apply QPos.mul_lt_mono_r with (p := b * d).
  setoid_replace (a / b * (b * d)) with (a * d).
  setoid_replace (c / d * (b * d)) with (c * b).
  now apply QPos_mul_le_lt.

  (* Left with two equality goals. Cheat by mapping to Q and using the big
  guns. *)
  unfold QPos.eq; destruct a, b, c, d; simpl; field; apply Qnot_eq_sym;
  now apply Qlt_not_eq.

  unfold QPos.eq; destruct a, b, c, d; simpl; field. apply Qnot_eq_sym;
  now apply Qlt_not_eq.
Qed.

Lemma QPos_div_lt_le a b c d : a < c -> d <= b -> a / b < c / d.
Proof.
  intros.
  apply QPos.mul_lt_mono_r with (p := b * d).
  setoid_replace (a / b * (b * d)) with (d * a).
  setoid_replace (c / d * (b * d)) with (b * c).
  now apply QPos_mul_le_lt.

  unfold QPos.eq; destruct a, b, c, d; simpl; field; apply Qnot_eq_sym;
  now apply Qlt_not_eq.

  unfold QPos.eq; destruct a, b, c, d; simpl; field; apply Qnot_eq_sym;
  now apply Qlt_not_eq.
Qed.

Lemma QPos_le_trans a b c : a <= b -> b <= c -> a <= c.
Proof.
  destruct a, b, c; unfold QPos.le; QOrder.order.
Qed.

Lemma QPos_lt_le_trans a b c : a < b -> b <= c -> a < c.
Proof.
  destruct a, b, c; unfold QPos.le, QPos.lt; apply Qlt_le_trans.
Qed.

Lemma QPos_lt_trans a b c : a < b -> b < c -> a < c.
Proof.
  destruct a, b, c; unfold QPos.lt; apply Qlt_trans.
Qed.


Lemma QPos_le_ngt : forall q r, q <= r  <->  ~ (r < q).
Proof.
  intros q r; destruct q, r; unfold QPos.le, QPos.lt; split; QOrder.order.
Qed.

Lemma QPos_lt_nge : forall q r, q < r  <->  ~ (r <= q).
Proof.
  intros q r; destruct q, r; unfold QPos.le, QPos.lt; split; QOrder.order.
Qed.


Lemma QPos_ltb_le : forall q r, (q <? r) = false  <->  r <= q.
Proof.
  unfold QPos.le, QPos.ltb, QPos.compare. intros q r. destruct q, r. simpl.
  case_eq (x ?= x0)%Q.
  rewrite <- Qeq_alt. intuition.
  rewrite H. auto with qarith.
  rewrite <- Qlt_alt. intuition. exfalso. assert (x < x)%Q.
  eapply Qlt_le_trans; eauto. revert H1. unfold Qlt. auto with zarith.
  rewrite <- Qgt_alt. intuition.
Qed.
