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


Definition QPos := { x : Q | (0 < x) }.

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

(*
  p : t
  q : t
  ============================
   Gt <> Gt -> false = true
*)

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

End QPos.

(* Re-export notations. *)

Infix "==" := QPos.eq : QPos_scope.
Infix "<" := QPos.lt : QPos_scope.
Infix "<=" := QPos.le : QPos_scope.
Notation "p > q" := (q < p) (only parsing) : QPos_scope.
Notation "p >= q" := (q <= p) (only parsing) : QPos_scope.
Notation "p != q" := (~p==q) (at level 70, no associativity) : QPos_scope.

Infix "?=" := QPos.compare (at level 70, no associativity) : QPos_scope.
Infix "=?" := QPos.eqb (at level 70, no associativity) : QPos_scope.
Infix "<=?" := QPos.leb (at level 70, no associativity) : QPos_scope.
Infix "<?" := QPos.ltb (at level 70, no associativity) : QPos_scope.

Infix "*" := QPos.mul : QPos_scope.

Notation "1" := QPos.one : QPos_scope.
Notation "2" := QPos.two : QPos_scope.

