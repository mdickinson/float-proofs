(* Definitions of floor : Q -> Z and ceiling : Q -> Z, and key results.

   Also defines is_integer. *)

Set Implicit Arguments.

Require Import ZArith.
Require Import QArith.
Require Import Qabs.

Require Import remedial.
Require Import is_integer.

Local Open Scope Z.

(* The floor function can be defined in terms of the standard library
   / operator, which does Euclidean division with the appropriate
   semantics when the numerator is negative. *)

Definition floor q := (Qnum q / ' Qden q).

(* To prove the main specification theorem for floor, we first need
   to prove a corresponding theorem at integer level. *)

Lemma _floor_spec_Z a b n : 0 < b -> (n * b <= a  <->  n <= a / b).
Proof.
  intro; rewrite Z.mul_comm; split; intro.
  - now apply Z.div_le_lower_bound.
  - eapply Z.le_trans;
    ((apply Z.mul_le_mono_pos_l; eassumption) || now apply Z.mul_div_le).
Qed.

(* Now we can show that floor is an adjoint to the inclusion of Z into Q,
   a property which completely characterises the floor function. *)

Local Open Scope Q.

Theorem floor_spec q n : inject_Z n <= q  <->  (n <= floor q)%Z.
Proof.
  unfold Qle; rewrite Z.mul_1_r; apply _floor_spec_Z, Pos2Z.is_pos.
Qed.

(* It's easier to prove that "floor" is a setoid morphism
   using "floor_spec" than using the definition directly. *)

Add Parametric Morphism : floor
    with signature Qeq ==> eq as floor_morphism.
Proof.
  intros q r q_eq_r; apply Z.le_antisymm; apply floor_spec;
  [ rewrite <- q_eq_r | rewrite q_eq_r ]; apply floor_spec, Z.le_refl.
Qed.

(* Variant formulation of floor_spec in terms of < rather than <=. *)

Theorem floor_spec_lt q n : q < inject_Z n  <->  (floor q < n)%Z.
Proof.
  rewrite Z.lt_nge, Qlt_nge; apply negate_iff, floor_spec.
Qed.

(* It follows from the specification that floor is monotonic. *)

Theorem floor_monotonic q r : q <= r  ->  (floor q <= floor r)%Z.
Proof.
  intro q_le_r;
  apply floor_spec, Qle_trans with (2 := q_le_r), floor_spec, Z.le_refl.
Qed.

(* Define the ceiling function in terms of floor, and prove its characteristic
   properties. *)

Definition ceiling q := (- floor (- q))%Z.

Add Parametric Morphism : ceiling
    with signature Qeq ==> eq as ceiling_morphism.
Proof.
  intros q r q_eq_r; unfold ceiling; now rewrite q_eq_r.
Qed.

Theorem ceiling_spec q n : q <= inject_Z n  <->  (ceiling q <= n)%Z.
Proof.
  split; intro.
  - apply Zle_sign_flip_l, floor_spec;
    now rewrite inject_Z_opp, <- Qopp_le_mono.
  - rewrite Qopp_le_mono, <- inject_Z_opp;
    now apply floor_spec, Zle_sign_flip_l.
Qed.

Theorem ceiling_spec_lt q n : inject_Z n < q  <->  (n < ceiling q)%Z.
Proof.
  rewrite Z.lt_nge; rewrite Qlt_nge; apply negate_iff; apply ceiling_spec.
Qed.

Theorem ceiling_monotonic q r : q <= r  ->  (ceiling q <= ceiling r)%Z.
Proof.
  intro q_le_r;
  apply ceiling_spec, Qle_trans with (1 := q_le_r), ceiling_spec, Z.le_refl.
Qed.

(* Relationship between floor and ceiling. *)

Theorem neg_ceiling_is_floor_neg q : (- ceiling q)%Z = floor (-q).
Proof.
  apply Z.opp_involutive.
Qed.

Theorem neg_floor_is_ceiling_neg q : (- floor q)%Z = ceiling (-q).
Proof.
  unfold ceiling; now rewrite Qopp_opp.
Qed.

(* We can recast floor and ceiling as functions from Q to Q. *)

Definition floorQ q := inject_Z (floor q).

Add Parametric Morphism : floorQ
    with signature Qeq ==> Qeq as floorQ_morphism.
Proof.
  intros q r q_eq_r; unfold floorQ; now rewrite q_eq_r.
Qed.

Theorem is_integer_floorQ q : is_integer (floorQ q).
Proof.
  apply is_integer_inject_Z.
Qed.

(* We could write a variation of floor_spec here, but as an experiment
   we'll break it up into two parts: applying a theorem of the form
   _ -> (_ <-> _) turns out to be awkward to do directly with apply. *)

Theorem floorQ_intro q n :
  is_integer n  ->  n <= q  ->  n <= floorQ q.
Proof.
  destruct 1 as [m m_eq_n]; unfold floorQ; rewrite <- m_eq_n, <- Zle_Qle;
  apply floor_spec.
Qed.

Theorem floorQ_le q : floorQ q <= q.
Proof.
  apply floor_spec, Z.le_refl.
Qed.

(* The following is useful for the auto hint database: it saves an
   application of Qle_trans. *)

Theorem floorQ_elim q n :
  is_integer n  ->  floorQ q < n  ->  q < n.
Proof.
  destruct 1 as [m m_eq_n]; unfold floorQ; rewrite <- m_eq_n, <- Zlt_Qlt;
  apply floor_spec_lt.
Qed.

(* Now we have corresponding results for all of the above for ceilingQ. *)

Definition ceilingQ q := inject_Z (ceiling q).

Add Parametric Morphism : ceilingQ
    with signature Qeq ==> Qeq as ceilingQ_morphism.
Proof.
  intros q r q_eq_r; unfold ceilingQ; now rewrite q_eq_r.
Qed.

Theorem is_integer_ceilingQ q : is_integer (ceilingQ q).
Proof.
  apply is_integer_inject_Z.
Qed.

Theorem ceilingQ_intro q n :
  is_integer n  ->  q <= n  ->  ceilingQ q <= n.
Proof.
  destruct 1 as [m m_eq_n]; unfold ceilingQ; rewrite <- m_eq_n, <- Zle_Qle;
  apply ceiling_spec.
Qed.

Theorem ceilingQ_elim q n :
  is_integer n  ->  n < q  ->  n < ceilingQ q.
Proof.
  destruct 1 as [m m_eq_n]; unfold ceilingQ; rewrite <- m_eq_n, <- Zlt_Qlt;
  apply ceiling_spec_lt.
Qed.

Theorem ceilingQ_le q : q <= ceilingQ q.
Proof.
  apply ceiling_spec, Z.le_refl.
Qed.

Lemma Qle_neg_switch x y : x <= y -> - y <= -x.
Proof.
  now rewrite <- Qopp_le_mono.
Qed.

Hint Immediate is_integer_inject_Z.
Hint Resolve Qle_neg_switch le_neg_switch le_neg_switch_r.
Hint Resolve is_integer_neg.
Hint Resolve floorQ_le floorQ_intro is_integer_floorQ.
Hint Resolve ceilingQ_le ceilingQ_intro is_integer_ceilingQ.
Hint Resolve Qle_antisym Qle_refl Qle_trans.

(* The following two lemmas are useful as part of an auto database,
   since they save one common use of Qle_trans. *)

Lemma floorQ_intro_l q r :
  q <= r  ->  floorQ q <= r.
Proof.
  eauto.
Qed.

Lemma ceilingQ_intro_r q r :
  q <= r  ->  q <= ceilingQ r.
Proof.
  eauto.
Qed.

Hint Resolve floorQ_intro_l ceilingQ_intro_r.

(* We can characterise integrality in terms of floorQ and ceilingQ. *)

Theorem floorQ_eq q : is_integer q -> floorQ q == q.
Proof.
  auto.
Qed.

Theorem ceilingQ_eq q : is_integer q -> ceilingQ q == q.
Proof.
  auto.
Qed.

Hint Resolve floorQ_eq ceilingQ_eq.

(* As a corollary of floorQ_eq, is_integer is decidable. *)

Corollary is_integer_dec q : {is_integer q} + {~ is_integer q}.
Proof.
  destruct (Qeq_dec (floorQ q) q) as [equal | notequal].
  - left; rewrite <- equal; apply is_integer_floorQ.
  - right; contradict notequal; now apply floorQ_eq.
Defined.

Theorem neg_floorQ_is_ceilingQ_neg q : - floorQ q == ceilingQ (- q).
Proof.
  auto.
Qed.

Theorem neg_ceilingQ_is_floorQ_neg q : - ceilingQ q == floorQ (- q).
Proof.
  auto.
Qed.

(* Results about floor, ceiling and absolute value. *)

Theorem Qabs_floor_le q r :
  is_integer r  ->  Qabs q <= r  ->  Qabs (floorQ q) <= r.
Proof.
  rewrite ?Qabs_Qle_condition; intro; destruct 1; auto.
Qed.

Theorem Qabs_ceiling_le q r :
  is_integer r  ->  Qabs q <= r  ->  Qabs (ceilingQ q) <= r.
Proof.
  rewrite ?Qabs_Qle_condition; intro; destruct 1; auto.
Qed.

(* XXX These two lemmas need to go elsewhere. *)

Require Import rearrange_tactic.

Lemma Qlt_le_succ x y : is_integer x -> is_integer y ->
                (x + 1 <= y  <->  x < y).
Proof.
  intros x_integer y_integer; split; intro H.
  - apply Qlt_le_trans with (y := x + 1); [rearrange_goal (0 < 1) | ]; easy.
  - destruct x_integer as [m Hm], y_integer as [n Hn].
    revert H; rewrite <- Hm; rewrite <- Hn; intro H.
    setoid_replace 1 with (inject_Z 1) by now compute.
    rewrite <- inject_Z_plus.
    rewrite <- Zle_Qle.
    apply Zlt_le_succ.
    rewrite Zlt_Qlt.
    easy.
Qed.

Lemma Qlt_le_pred x y : is_integer x -> is_integer y ->
                        (x < y  <->  x <= y - 1).
Proof.
  setoid_replace (x <= y - 1) with (x + 1 <= y) by (split; intro; rearrange).
  intros; split; now apply Qlt_le_succ.
Qed.
