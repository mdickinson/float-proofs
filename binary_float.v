(* Define the concept of representability for binary floating-point formats,
   and use that to define "binary_float" types at various precisions. *)

Require Import QArith.
Require Import Qabs.

Require Import remedial.
Require Import floor_and_ceiling.
Require Import qpos.
Require Import twopower.


Local Open Scope Q.

(* A rational number is representable in precision p if it can be expressed in
   the form m * 2^e for some integers m and e with |m| < 2^p. *)

Definition representable (p : positive) (x : Q) :=
  exists (m : Z) (e : Z),
    Qabs (inject_Z m) < twopowerQ ('p)  /\  x == (inject_Z m) * twopowerQ e.

(* Some basic results about representability. *)

Add Morphism representable : representable_morphism.
Proof.
  intros p x y x_eq_y; unfold representable; now setoid_rewrite x_eq_y.
Qed.

Lemma zero_is_representable (p : positive) : representable p 0.
Proof.
  exists 0%Z, 0%Z; intuition; apply twopowerQ_positive.
Qed.

Lemma one_is_representable (p : positive) : representable p 1.
Proof.
  exists 1%Z, 0%Z; intuition; change (Qabs (inject_Z 1)) with (twopowerQ 0);
  now apply twopowerQ_monotonic_lt.
Qed.

Lemma neg_representable_is_representable p x:
  representable p x -> representable p (-x).
Proof.
  destruct 1 as [m [e [H0 H1]]]; exists (-m)%Z, e;
  rewrite inject_Z_opp, Qabs_opp; intuition; rewrite H1; ring.
Qed.

Lemma scaled_representable_is_representable p e x :
  representable p x -> representable p (x * twopowerQ e).
Proof.
  destruct 1 as [m [f [H0 H1]]]; exists m, (f + e)%Z; intuition;
  rewrite H1; rewrite twopowerQ_mul; ring.
Qed.

Lemma scaled_representable_is_representable_div p e x :
  representable p x -> representable p (x / twopowerQ e).
Proof.
  unfold Qdiv; rewrite <- twopowerQ_inv;
  apply scaled_representable_is_representable.
Qed.


Lemma small_integers_are_representable p m :
  Qabs (inject_Z m) < twopowerQ ('p) -> representable p (inject_Z m).
Proof.
  exists m, 0%Z; intuition; change (twopowerQ 0) with 1; ring.
Qed.

Lemma powers_of_two_are_representable p e :
  representable p (twopowerQ e).
Proof.
  setoid_replace (twopowerQ e) with (1 * twopowerQ e) by ring;
  apply scaled_representable_is_representable;
  apply one_is_representable.
Qed.

(* For proving that something is representable, it's helpful to
   have a slightly weaker bound than that used in the definition. *)

Lemma small_integers_are_representable_le p m :
  Qabs (inject_Z m) <= twopowerQ ('p) -> representable p (inject_Z m).
Proof.
  intro H;
  destruct (Qle_lt_eq (Qabs (inject_Z m)) (twopowerQ (' p)) H) as [H0 | H0];
  clear H.
  - now apply small_integers_are_representable.
  - revert H0; apply Qabs_case; intros _ H0;
    [ | setoid_replace (inject_Z m) with (- - inject_Z m) by ring ];
    rewrite H0; try apply neg_representable_is_representable;
    apply powers_of_two_are_representable.
Qed.

Lemma representable_le_bound p m e :
  Qabs (inject_Z m) <= twopowerQ ('p) ->
  representable p (inject_Z m * twopowerQ e).
Proof.
  intros; apply scaled_representable_is_representable;
  now apply small_integers_are_representable_le.
Qed.

(* A key lemma: large representable numbers must be integers. *)

Lemma large_representable_is_integer p x :
  representable p x ->  twopowerQ ('p - 1) <= Qabs x -> is_integer x.
Proof.
  destruct 1 as [m [e [H0 H1]]]; rewrite H1; intro H2; apply is_integer_mul.
  - apply is_integer_inject_Z.
  - apply is_integer_twopowerQ;
    assert ('p - 1 < 'p + e)%Z.
    + apply twopowerQ_injective_lt;
      apply Qle_lt_trans with (1 := H2);
      rewrite Qabs_Qmult, twopowerQ_mul, Qabs_twopower;
      now apply Qmult_lt_r with (1 := twopowerQ_positive _).
    + omega.
Qed.

(* Definition of binary_float p as a subset of Q. *)

Definition binary_float (p : positive) := { x : Q | representable p x}.

(* The zero float. *)

Definition zero_float p : binary_float p :=
  exist _ _ (zero_is_representable p).

(* Construction of a float from a (suitably bounded) significand and
   an exponent. *)

Definition float_from_significand_and_exponent p m e
  (m_bounded : Qabs (inject_Z m) <= twopowerQ ('p)) : binary_float p :=
  exist _ _ (representable_le_bound p m e m_bounded).

(* An obvious fact: a rational number x is representable iff its
   the image of a binary float. *)

Lemma float_from_significand_and_exponent_Q p m e m_bounded :
  proj1_sig (float_from_significand_and_exponent p m e m_bounded) ==
  inject_Z m * twopowerQ e.
Proof.
  easy.
Qed.

Lemma binary_floats_are_representable p x :
  representable p x  <->  exists (y : binary_float p), proj1_sig y == x.
Proof.
  split.
  - intro H. exists (exist _ x H). easy.
  - destruct 1 as [y H]. destruct y. simpl in H.
    now rewrite <- H.
Qed.

(* Some basic notation in the domain of floats. *)

Delimit Scope float_scope with float.

Set Implicit Arguments.

Definition float_le p (x y : binary_float p) : Prop :=
  proj1_sig x <= proj1_sig y.

Definition float_eq p (x y : binary_float p) : Prop :=
  proj1_sig x == proj1_sig y.

Definition float_lt p (x y : binary_float p) : Prop :=
  proj1_sig x < proj1_sig y.

Definition float_opp p (x : binary_float p) : binary_float p.
Proof.
  refine (exist _ (- (proj1_sig x)) _); destruct x;
  now apply neg_representable_is_representable.
Defined.

Infix "<" := float_lt : float_scope.
Infix "<=" := float_le : float_scope.
Infix "==" := float_eq : float_scope.
Notation "0" := (zero_float _) : float_scope.
Notation "- x" := (float_opp x) : float_scope.
Notation "x <> y" := (~ (float_eq x y)) : float_scope.

Local Open Scope float.

Lemma float_eq_reflexivity p (x : binary_float p) : x == x.
Proof.
  now unfold float_eq.
Qed.

Lemma float_eq_symmetry p (x y : binary_float p) : x == y -> y == x.
Proof.
  now unfold float_eq.
Qed.

Lemma float_eq_transitivity p (x y z : binary_float p) :
  x == y -> y == z -> x == z.
Proof.
  apply Qeq_trans.
Qed.


Add Parametric Relation (p : positive) : (binary_float p) (@float_eq p)
    reflexivity proved by (@float_eq_reflexivity p)
    symmetry proved by (@float_eq_symmetry p)
    transitivity proved by (@float_eq_transitivity p)
      as EqualFloat.


Add Parametric Morphism (p : positive) : (@float_opp p) with
    signature (@float_eq p) ==> (@float_eq p) as float_opp_morphism.
Proof.
  unfold float_opp, float_eq; intros x y H; simpl; now rewrite H.
Qed.


Lemma float_le_antisymm p (x y : binary_float p) :
  x <= y  ->  y <= x  ->  x == y.
Proof.
  apply Qle_antisym.
Qed.


Lemma float_le_refl p (x : binary_float p) : x <= x.
Proof.
  apply Qle_refl.
Qed.


Lemma float_le_trans p (x y z : binary_float p) :
  x <= y -> y <= z -> x <= z.
Proof.
  apply Qle_trans with (y := proj1_sig y).
Qed.


Lemma float_incl_opp p (x : binary_float p) :
  (proj1_sig (- x)%float == - proj1_sig x)%Q.
Proof.
  easy.
Qed.


Lemma le_neg_switch p (x y : binary_float p) : -x <= y <-> -y <= x.
Proof.
  unfold float_le; repeat rewrite float_incl_opp;
  split; intro; now apply remedial.le_neg_switch.
Qed.

Lemma float_lt_nge p (x y : binary_float p) :
  x < y  <->  ~ (y <= x).
Proof.
  apply Qlt_nge.
Qed.

Lemma float_le_not_eq p (x y : binary_float p) :
  x <= y -> ~(x == y) -> x < y.
Proof.
  apply Qle_not_eq.
Qed.