Require Import ZArith.
Require Import QArith.
Require Import Qabs.

Require Import remedial.
Require Import rearrange_tactic.
Require Import floor_and_ceiling.
Require Import qpos.
Require Import twopower.
Require Import twopower_tactics.
Require Import cobinade.
Require Import binary_float.


Set Implicit Arguments.

Local Open Scope Q.

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

Lemma nonzero_product_is_nonzero (x y : Q) :
  ~(x == 0)%Q -> ~(y == 0)%Q -> ~(x * y == 0)%Q.
Proof.
  intros; contradict H; scale_by y; now ring_simplify.
Qed.

(* Notation to ease working with elements of subsets.

     For a nonzero float f, "[ f ]" is the corresponding element
     of nonzero_float, and the notation hides the (often complicated)
     proof term.

     Conversely, given a nonzero_float g, !g is the corresponding float. *)

Notation "[ e ]" := (exist _ e _).
Notation "! x" := (proj1_sig x) (at level 20, right associativity).

Local Open Scope float.

Lemma float_lt_nge p (f g : binary_float p) : f < g  <->  ~(g <= f).
Proof.
  apply Qlt_nge.
Qed.

Lemma float_le_ngt p (f g : binary_float p) : f <= g  <->  ~(g < f).
Proof.
  unfold float_le, float_lt.
  split; intro.
  now apply Qle_not_lt.
  now apply Qnot_lt_le.
Qed.

Definition nonzero_float p := { x : binary_float p | ~(x == 0) }.

Definition nonzero_float_eq p (f g : nonzero_float p) :=
  ! f == ! g.

Lemma nonzero_float_eq_reflexivity p (x : nonzero_float p) :
  nonzero_float_eq x x.
Proof.
  apply Qeq_refl.
Qed.

Lemma nonzero_float_eq_symmetry p (x y : nonzero_float p) :
  nonzero_float_eq x y -> nonzero_float_eq y x.
Proof.
  apply Qeq_sym.
Qed.

Lemma nonzero_float_eq_transitivity p (x y z : nonzero_float p) :
  nonzero_float_eq x y -> nonzero_float_eq y z -> nonzero_float_eq x z.
Proof.
  apply Qeq_trans.
Qed.

Add Parametric Relation (p : positive) : (nonzero_float p)
                                           (nonzero_float_eq (p:=p))
    reflexivity proved by (nonzero_float_eq_reflexivity (p:=p))
    symmetry proved by (nonzero_float_eq_symmetry (p:=p))
    transitivity proved by (nonzero_float_eq_transitivity (p:=p))
    as EqualNonzeroFloat.

Definition nonzero_float_opp p (f : nonzero_float p) : nonzero_float p.
Proof.
  refine [- !f]; destruct f as [x nonzero_x]; unfold float_opp, float_eq in *;
  simpl in *; contradict nonzero_x; rearrange.
Defined.

Lemma nonzero_float_opp_opp p (f : nonzero_float p) :
  !nonzero_float_opp (nonzero_float_opp f) == !f.
Proof.
  unfold nonzero_float_opp, float_eq, float_opp; simpl; ring.
Qed.

Lemma nonzero_float_opp_lt_switch p (f g : nonzero_float p) :
  !nonzero_float_opp f < !g  <->  !nonzero_float_opp g < !f.
Proof.
  unfold nonzero_float_opp, float_lt; simpl; split; intro; rearrange.
Qed.

Lemma nonzero_float_lt_opp_switch p (f g : nonzero_float p) :
  !f < !nonzero_float_opp g  <->  !g < !nonzero_float_opp f.
Proof.
  unfold nonzero_float_opp, float_lt; simpl; split; intro; rearrange.
Qed.

Lemma nonzero_float_le_opp_switch p (f g : nonzero_float p) :
  !f <= !nonzero_float_opp g  <->  !g <= !nonzero_float_opp f.
Proof.
  unfold nonzero_float_opp, float_le; simpl; split; intro; rearrange.
Qed.

Lemma nonzero_float_opp_negative_is_positive p (f : nonzero_float p) :
  !f < 0  ->  0 < !nonzero_float_opp f.
Proof.
  unfold nonzero_float_opp, float_lt; simpl; intro; rearrange.
Qed.

Lemma nonzero_float_opp_positive_is_negative p (f : nonzero_float p) :
  0 < !f  -> !nonzero_float_opp f < 0.
Proof.
  unfold nonzero_float_opp, float_lt; simpl; intro; rearrange.
Qed.

(* It's convenient to define a way to decompose our nonzero float
     into either a positive or negative float. *)

Definition float_by_sign p (f : nonzero_float p) : QPos + QPos.
Proof.
  destruct f as [[q q_representable] x_nonzero];
  destruct (Q_dec 0 q) as [[q1 | q2] | q3].
  - left; exact (exist _ q q1).
  - right; refine (exist _ (-q)%Q _); rearrange.
  - contradict x_nonzero; now symmetry.
Defined.

Lemma float_by_sign_spec p (f : nonzero_float p) :
  (!!f == match float_by_sign f with
          | inl x => !x
          | inr x => -(!x)
          end)%Q.
Proof.
  unfold float_by_sign; destruct f as [[q q_representable] x_nonzero];
  destruct (Q_dec 0 q) as [[q1 | q2] | q3];
  (simpl; ring || contradict x_nonzero).
Qed.

Definition low_exponent p (f : nonzero_float p) : Z :=
  match float_by_sign f with
  | inl x => (binade x - 'p + 1)%Z
  | inr x => (cobinade x - 'p)%Z
  end.

Definition low_significand_Q p (f : nonzero_float p) : Q :=
  match float_by_sign f with
  | inl x => !x / twopowerQ (low_exponent f)
  | inr x => -(!x / twopowerQ (low_exponent f))
  end%Q.

Lemma low_significand_is_integer p (f : nonzero_float p) :
  is_integer (low_significand_Q f).
Proof.
  pose proof (float_by_sign_spec f) as H;
  unfold low_significand_Q, low_exponent; destruct (float_by_sign f);
  destruct f as [[x x_representable] x_nonzero];
  simpl in H.
  - apply (large_representable_is_integer p).
    + apply scaled_representable_is_representable_div;
      now rewrite <- H.
    + twopower_left; rewrite Qabs_pos.
      * apply twopower_binade_le; omega.
      * apply Qlt_le_weak. now destruct q.
  - apply is_integer_neg, (large_representable_is_integer p).
    + apply scaled_representable_is_representable_div;
      assert (!q == -x)%Q as H0 by rearrange;
      rewrite H0; now apply neg_representable_is_representable.
    + twopower_left; rewrite Qabs_pos.
      * apply Qlt_le_weak, twopower_cobinade_lt; omega.
      * apply Qlt_le_weak; now destruct q.
Qed.

Definition low_significand p (f : nonzero_float p) :=
  floor (low_significand_Q f).

Lemma reconstruct_float p (f : nonzero_float p) :
  (inject_Z (low_significand f) * twopowerQ (low_exponent f) == !!f)%Q.
Proof.
  pose proof (low_significand_is_integer f);
  unfold low_significand, low_significand_Q, low_exponent in *.
  rewrite float_by_sign_spec; destruct float_by_sign.
  - twopower_right; now apply floor_integer.
  - twopower_right; setoid_replace (- !q / twopowerQ (cobinade q - 'p))
                    with (- (!q / twopowerQ (cobinade q - 'p)))%Q
      by (field; apply twopowerQ_nonzero); now apply floor_integer.
Qed.

Lemma low_significand_bound p (f : nonzero_float p) :
  match float_by_sign f with
  | inl x => twopowerQ ('p - 1) <= low_significand_Q f < twopowerQ (' p)
  | inr x => -twopowerQ ('p) <= low_significand_Q f < -twopowerQ ('p - 1)
  end.
Proof.
  unfold low_significand_Q, low_exponent; destruct float_by_sign; split.
  - twopower_left; apply twopower_binade_le; omega.
  - twopower_right; apply twopower_binade_lt; omega.
  - rewrite <- Qopp_le_mono; twopower_right; apply twopower_cobinade_le; omega.
  - rewrite <- Qopp_lt_mono; twopower_left; apply twopower_cobinade_lt; omega.
Qed.

Lemma next_up_significand_bound p (f : nonzero_float p) :
  match float_by_sign f with
  | inl x => twopowerQ ('p - 1) < low_significand_Q f + 1 <= twopowerQ (' p)
  | inr x => -twopowerQ ('p) < low_significand_Q f + 1 <= -twopowerQ ('p - 1)
  end.
Proof.
  pose proof (low_significand_bound f) as H;
  destruct float_by_sign; destruct H as [Hlower Hupper]; split.
  - apply Qle_lt_trans with (1 := Hlower); now rearrange_goal (0 < 1)%Q.
  - apply Qlt_le_succ.
    + apply low_significand_is_integer.
    + now apply is_integer_twopowerQ.
    + easy.
  - apply Qle_lt_trans with (1 := Hlower); now rearrange_goal (0 < 1)%Q.
  - apply Qlt_le_succ.
    + apply low_significand_is_integer.
    + apply is_integer_neg, is_integer_twopowerQ; now destruct p.
    + easy.
Qed.

Lemma next_up_significand_abs_upper_bound p (f : nonzero_float p) :
  (Qabs (inject_Z (low_significand f + 1)) <= twopowerQ (' p))%Q.
Proof.
  rewrite inject_Z_plus; change (inject_Z 1) with 1;
  setoid_replace (inject_Z (low_significand f))
  with (low_significand_Q f) by
      (unfold low_significand;
       apply floor_integer, low_significand_is_integer);
  pose proof (next_up_significand_bound f) as H;
  destruct float_by_sign; destruct H as [Hlower Hupper].
  - rewrite Qabs_pos.
    + easy.
    + apply Qlt_le_weak, Qlt_trans with (2 := Hlower), twopowerQ_positive.
  - rewrite Qabs_neg.
    + apply Qlt_le_weak; rearrange.
    + apply Qle_trans with (1 := Hupper), Qlt_le_weak.
      rearrange_goal (0 < twopowerQ ('p - 1))%Q.
      apply twopowerQ_positive.
Qed.

Lemma next_up_significand_abs_lower_bound p (f : nonzero_float p) :
  (twopowerQ ('p - 1) <= Qabs (inject_Z (low_significand f + 1)))%Q.
Proof.
  rewrite inject_Z_plus; change (inject_Z 1) with 1;
  setoid_replace (inject_Z (low_significand f))
  with (low_significand_Q f) by
      (unfold low_significand;
       apply floor_integer, low_significand_is_integer).
  pose proof (next_up_significand_bound f) as H.
  destruct float_by_sign; destruct H as [Hlower Hupper].
  - rewrite Qabs_pos.
    + now apply Qlt_le_weak.
    + apply Qlt_le_weak, Qlt_trans with (2 := Hlower), twopowerQ_positive.
  - rewrite Qabs_neg.
    + rearrange.
    + apply Qle_trans with (1 := Hupper).
      rearrange_goal (0 <= twopowerQ ('p - 1))%Q.
      apply twopowerQ_nonnegative.
Qed.

Definition next_up p (f : nonzero_float p) : nonzero_float p.
Proof.
  refine
    [float_from_significand_and_exponent
       p (low_significand f + 1) (low_exponent f)
       (next_up_significand_abs_upper_bound f)].
  (* Left with showing that we're nonzero. *)
  unfold float_from_significand_and_exponent.
  apply nonzero_product_is_nonzero.
  - apply Qabs_nonzero_inv, Qlt_le_trans with (y := twopowerQ ('p - 1)).
    + apply twopowerQ_positive.
    + apply next_up_significand_abs_lower_bound.
  - apply twopowerQ_nonzero.
Defined.


(* Theorem characterizing next_up. *)

Theorem next_up_spec p (f g : nonzero_float p) :
  proj1_sig (next_up f) <= proj1_sig g  <->  proj1_sig f < proj1_sig g.
Proof.
  split.
  - (* the easy direction: if next_up f <= g, then f < next_up f <= g *)
    intro.
    apply float_lt_le_trans with (2 := H).
    unfold next_up, float_lt; simpl.
    rewrite <- reconstruct_float.
    twopower_right.
    rewrite <- Zlt_Qlt.
    omega.
  - pose proof (low_significand_bound f).
    pose proof (float_by_sign_spec f).
    assert (low_exponent f = low_exponent f).
    easy.
    unfold low_exponent at 2 in H1.
    assert (low_significand_Q f == low_significand_Q f)%Q.
    easy.
    unfold low_significand_Q at 2 in H2.
    destruct float_by_sign; intro.
    + (* Case f positive. *)
      unfold next_up, float_from_significand_and_exponent, float_le; simpl.
      twopower_right.
      rewrite inject_Z_plus.
      apply Qlt_le_succ.
      * apply is_integer_inject_Z.
      * apply large_representable_is_integer with (p := p).
        apply scaled_representable_is_representable_div.
        destruct g as [[g_as_q g_as_q_representable] g_nonzero].
        easy.
        rewrite H1.
        twopower_left.
        rewrite Qabs_pos.
        apply Qle_trans with (y := !!f).
        rewrite H0.
        apply twopower_binade_le; omega.
        now apply Qlt_le_weak.
        apply Qlt_le_weak, Qlt_trans with (y := !!f).
        rewrite H0; now destruct q.
        easy.
      * twopower_left.
        apply Qle_lt_trans with (y := !!f).
        twopower_right.
        unfold low_significand.
        setoid_replace (inject_Z (floor (low_significand_Q f)))
        with (low_significand_Q f).
        rewrite H2.
        twopower_left.
        rewrite H0.
        apply Qle_refl.
        apply floor_integer.
        apply low_significand_is_integer.
        easy.
    + (* Case f negative. *)
      unfold next_up, float_from_significand_and_exponent, float_le; simpl.
      (* We have -twopowerQ (cobinade q) <= f < -twopowerQ (cobinade q - 1) *)
      (* Divide into cases: either g < -twopowerQ (cobinade q - 1),
         or -twopower (cobinade q - 1) <= g. *)
      destruct (Qlt_le_dec (!!g) (-twopowerQ (cobinade q - 1))).
      * (* Case where g is within the same (weak) binade. *)
        twopower_right.
        rewrite inject_Z_plus.
        apply Qlt_le_succ.
        apply is_integer_inject_Z.
        apply large_representable_is_integer with (p := p).
        apply scaled_representable_is_representable_div.
        now destruct g as [[c d] b].
        rewrite H1.
        twopower_left.
        rewrite Qabs_neg.
        apply Qlt_le_weak; rearrange.
        apply Qlt_le_weak,
        Qlt_trans with (y := (-twopowerQ (cobinade q - 1))%Q).
        easy.
        rearrange_goal (0 < twopowerQ (cobinade q - 1))%Q.
        apply twopowerQ_positive.
        unfold low_significand.
        setoid_replace (inject_Z (floor (low_significand_Q f)))
        with (low_significand_Q f).
        rewrite H2.
        twopower_right.
        rewrite <- H0.
        easy.
        apply floor_integer.
        apply low_significand_is_integer.
      * (* Case where g is not in the same binade. *)
        apply Qle_trans with (2 := q0).
        rewrite H1.
        (* twopower_right should work in place of the next three *)
        apply le_neg_switch_r.
        twopower_left.
        apply le_neg_switch_r.
        rewrite inject_Z_plus.
        apply Qlt_le_succ.
        apply is_integer_inject_Z.
        apply is_integer_neg.
        apply is_integer_twopowerQ.
        assert (0 < 'p)%Z by easy.
        omega.
        unfold low_significand.
        setoid_replace (inject_Z (floor (low_significand_Q f)))
        with (low_significand_Q f).
        rewrite H2.
        rewrite <- Qopp_lt_mono.
        rewrite H1.
        twopower_left.
        apply twopower_cobinade_lt.
        omega.
        apply floor_integer.
        apply low_significand_is_integer.
Qed.

Theorem next_up_spec_alt p (f g : nonzero_float p) :
  !g < !next_up f  <->  !g <= !f.
Proof.
  rewrite float_le_ngt, float_lt_nge; apply negate_iff, next_up_spec.
Qed.

Theorem next_up_positive p (f : nonzero_float p) :
  0 < !f  ->  0 < !next_up f.
Proof.
  intro; apply float_lt_trans with (1 := H), next_up_spec, float_le_refl.
Qed.

Theorem next_up_negative p (f : nonzero_float p) :
  !f < 0  ->  !next_up f < 0.
Proof.
  pose proof (next_up_significand_bound f);
  pose proof (float_by_sign_spec f);
  intro; unfold next_up, low_significand, float_lt;
  unfold float_from_significand_and_exponent;
  destruct float_by_sign; simpl.
  - (* Case f positive; should get a contradiction. *)
    assert (0 < !f) by (unfold float_lt; rewrite H0; now destruct q);
    assert (float_lt (p:=p) 0 0) as zero_lt_zero
        by (now apply float_lt_trans with (y := !f)).
    now contradict zero_lt_zero.
  - (* Case f negative. *)
    twopower_right.
    rewrite inject_Z_plus.
    setoid_replace (inject_Z (floor (low_significand_Q f)))
    with (low_significand_Q f).
    apply Qle_lt_trans with (y := (- twopowerQ ('p - 1))%Q).
    easy.
    rearrange_goal (0 < twopowerQ ('p - 1))%Q.
    apply twopowerQ_positive.
    apply floor_integer.
    apply low_significand_is_integer.
Qed.

Definition next_down p (f : nonzero_float p) :=
  nonzero_float_opp (next_up (nonzero_float_opp f)).

Theorem next_down_spec p (f g : nonzero_float p) :
  !f <= !next_down g  <->  !f < !g.
Proof.
  unfold next_down.
  rewrite <- nonzero_float_opp_opp at 2.
  rewrite nonzero_float_opp_lt_switch.
  rewrite nonzero_float_le_opp_switch.
  apply next_up_spec.
Qed.

Theorem next_down_spec_alt p (f g : nonzero_float p) :
  !next_down g < !f  <->  !g <= !f.
Proof.
  rewrite float_le_ngt, float_lt_nge; apply negate_iff, next_down_spec.
Qed.

Theorem next_down_positive p (f : nonzero_float p) :
  0 < !f  ->  0 < !next_down f.
Proof.
  intro; unfold next_down;
  now apply nonzero_float_opp_negative_is_positive,
  next_up_negative, nonzero_float_opp_positive_is_negative.
Qed.

Theorem next_down_negative p (f : nonzero_float p) :
  !f < 0  ->  !next_down f < 0.
Proof.
  intro; unfold next_down.
  now apply nonzero_float_opp_positive_is_negative,
  next_up_positive, nonzero_float_opp_negative_is_positive.
Qed.

Theorem next_up_next_down p (f : nonzero_float p) :
  !next_up (next_down f) == !f.
Proof.
  apply float_le_antisymm.
  - apply next_up_spec, next_down_spec, float_le_refl.
  - apply next_down_spec_alt, next_up_spec_alt, float_le_refl.
Qed.

Theorem next_down_next_up p (f : nonzero_float p) :
  !next_down (next_up f) == !f.
Proof.
  apply float_le_antisymm.
  - apply next_up_spec_alt, next_down_spec_alt, float_le_refl.
  - apply next_down_spec, next_up_spec, float_le_refl.
Qed.

(* next_up and next_down are monotonic and injective. *)

Theorem next_up_eq p (f g : nonzero_float p) :
  !f == !g  <->  !next_up f == !next_up g.
Proof.
  split; intro H.
  - apply float_le_antisymm; apply next_up_spec, next_up_spec_alt;
    rewrite H; apply float_le_refl.
  - apply float_le_antisymm; apply next_up_spec_alt, next_up_spec;
    rewrite H; apply float_le_refl.
Qed.

Theorem next_up_le p (f g : nonzero_float p) :
  !f <= !g  <->  !next_up f <= !next_up g.
Proof.
  split; intro.
  - now apply next_up_spec, next_up_spec_alt.
  - now apply next_up_spec_alt, next_up_spec.
Qed.

Theorem next_up_lt p (f g : nonzero_float p) :
  !f < !g  <->  !next_up f < !next_up g.
Proof.
  split; intro.
  - now apply next_up_spec_alt, next_up_spec.
  - now apply next_up_spec, next_up_spec_alt.
Qed.

Theorem next_down_eq p (f g : nonzero_float p) :
  !f == !g  <->  !next_down f == !next_down g.
Proof.
  split; intro H; apply float_le_antisymm;
  (apply next_down_spec, next_down_spec_alt
                           || apply next_down_spec_alt, next_down_spec);
  rewrite H; apply float_le_refl.
Qed.

Theorem next_down_le p (f g : nonzero_float p) :
  !f <= !g  <->  !next_down f <= !next_down g.
Proof.
  split; intro;
  (
    apply next_down_spec, next_down_spec_alt
    ||
    apply next_down_spec_alt, next_down_spec
  );
  easy.
Qed.

Theorem next_down_lt p (f g : nonzero_float p) :
  !f < !g  <->  !next_down f < !next_down g.
Proof.
  split; intro;
  (
    apply next_down_spec_alt, next_down_spec
    ||
    apply next_down_spec, next_down_spec_alt
  );
  easy.
Qed.

Add Parametric Morphism (p : positive) : (next_up (p:=p))
    with signature nonzero_float_eq (p:=p) ==> nonzero_float_eq (p:=p)
      as next_up_morphism.
Proof.
  intros; unfold nonzero_float_eq; now rewrite <- next_up_eq.
Qed.

Add Parametric Morphism (p : positive) : (next_down (p:=p))
    with signature nonzero_float_eq (p:=p) ==> nonzero_float_eq (p:=p)
      as next_down_morphism.
Proof.
  intros; unfold nonzero_float_eq; now rewrite <- next_down_eq.
Qed.

(* Example computations with next_up. *)

Definition tiny_precision_neg_one : nonzero_float 53.
Proof.
  refine [[(-(1))%Q]].
  easy.
  Grab Existential Variables.
  now exists ((-1)%Z), (0%Z).
Defined.

Eval compute in low_exponent tiny_precision_neg_one.
Eval compute in !!(next_up tiny_precision_neg_one).
Eval compute in !!(next_down tiny_precision_neg_one).
