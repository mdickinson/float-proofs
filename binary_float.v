(* Define the concept of representability for binary floating-point formats,
   and use that to define "binary_float" types at various precisions. *)

Require Import QArith.
Require Import Qabs.

Require Import floor_and_ceiling.
Require Import qpos.
Require Import twopower.


Open Scope Q.

(* Remedial lemmas.  Move these to another module. *)

Lemma Qle_lt_eq x y :
  x <= y -> x < y \/ x == y.
Proof.
  case (Qeq_dec x y).
  - intros; now right.
  - intros; left; now apply Qle_not_eq.
Qed.

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
