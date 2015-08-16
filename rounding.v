(* Definitions and properties of rounding modes for binary floats. *)

(* We start with the round_toward_negative (rtn) rounding mode.  Given a
   rational number x, we'll construct the closest binary float (at precision p)
   that doesn't exceed x.

   We'll construct the float by giving its significand and exponent.  To do
   that, we'll need a lemma that the significand is bounded. *)

Require Import Qabs.

Require Import remedial.
Require Import rearrange_tactic.
Require Import floor_and_ceiling.
Require Import round.
Require Import twopower.
Require Import twopower_tactics.
Require Import binade.
Require Import binary_float.
Require Import next_up.

Local Open Scope Q.

(* There are two cases: x is zero, or x is nonzero. Let's first assume that x
   is nonzero. Then we can construct the significand and exponent directly. *)

Section RoundingForNonzero.

  Variable p : positive.
  Variable x : Q.
  Hypothesis x_nonzero : ~(x == 0).

  Let exponent : Z := (binadeQ x x_nonzero - (' p) + 1)%Z.
  Let scale : Q := twopowerQ exponent.

  Lemma _rtn_significand_bound :
    Qabs (inject_Z (floor (x / scale))) <= twopowerQ (' p).
  Proof.
    apply Qabs_floor_le; [now apply is_integer_twopowerQ |];
    subst scale exponent; twopower_right;
    apply Qlt_le_weak; apply (twopowerQ_binadeQ_lt _ _ x_nonzero); omega.
  Qed.

  Lemma _rtp_significand_bound :
    Qabs (inject_Z (ceiling (x / scale))) <= twopowerQ (' p).
  Proof.
    apply Qabs_ceiling_le; [now apply is_integer_twopowerQ |];
    subst scale exponent; twopower_right;
    apply Qlt_le_weak; apply (twopowerQ_binadeQ_lt _ _ x_nonzero); omega.
  Qed.

  Lemma _rte_significand_bound :
    Qabs (inject_Z (round (x / scale))) <= twopowerQ (' p).
  Proof.
    apply Qabs_round_le; [now apply is_integer_twopowerQ | ];
    subst scale exponent; twopower_right;
    apply Qlt_le_weak; apply (twopowerQ_binadeQ_lt _ _ x_nonzero); omega.
  Qed.

End RoundingForNonzero.

Definition round_toward_negative p x : binary_float p :=
  match Qeq_dec x 0 with
  | left x_zero => zero_float p
  | right x_nonzero =>
      let exponent := (binadeQ x x_nonzero - (' p) + 1)%Z in
      let scale : Q := twopowerQ exponent in
      let significand := floor (x / scale) in
      float_from_significand_and_exponent p significand exponent (
                                            _rtn_significand_bound _ _ _)
  end.

Definition round_toward_positive p x : binary_float p :=
  match Qeq_dec x 0 with
  | left x_zero => zero_float p
  | right x_nonzero =>
      let exponent := (binadeQ x x_nonzero - (' p) + 1)%Z in
      let scale : Q := twopowerQ exponent in
      let significand := ceiling (x / scale) in
      float_from_significand_and_exponent p significand exponent (
                                            _rtp_significand_bound _ _ _)
  end.

Definition round_ties_to_even p x : binary_float p :=
  match Qeq_dec x 0 with
  | left x_zero => zero_float p
  | right x_nonzero =>
      let exponent := (binadeQ x x_nonzero - (' p) + 1)%Z in
      let scale : Q := twopowerQ exponent in
      let significand := round (x / scale) in
      float_from_significand_and_exponent p significand exponent (
                                            _rte_significand_bound _ _ _)
  end.

Lemma round_toward_negative_spec (p : positive) (x : Q) (f : binary_float p) :
  proj1_sig f <= x   <->  (f <= round_toward_negative p x)%float.
Proof.
  (* Destruct to split into four subgoals. *)
  unfold round_toward_negative, float_le;
  destruct (Qeq_dec x 0) as [x_zero | x_nonzero]; [now rewrite x_zero | ];
  simpl; split; intro H.
  - (* Case x != 0, showing that f <= x -> f <= round x. *)
    twopower_left.
    case (Qle_ge_cases 0 x); intro.
    + (* Case 0 <= x.  Divide further depending on
         whether 2^(binade x) <= f or not. *)
      case (Qle_ge_cases (twopowerQ (binadeQ x x_nonzero)) (proj1_sig f));
      intro.
      * (* Case 2^(binade x) <= f.  Then we should be able to show
           that f is an integer. *)
        apply integer_le_floor.
        {
          apply (large_representable_is_integer p).
          - apply scaled_representable_is_representable_div; now destruct f.
          - match goal with
            | [ |- _ <= Qabs ?q ] => apply Qle_trans with (2 := Qle_Qabs _)
            end; now twopower_left.
        }
        {
          (* More twopower simplification. *)
          now twopower_left.
        }
      * (* Case f <= 2^(binade x).  Then we can apply transitivity. *)
        apply Qle_trans with (y := twopowerQ ('p - 1)).
        {
          now twopower_right.
        }
        {
          apply integer_le_floor.
          - apply is_integer_twopowerQ; assert (0 < 'p)%Z by easy; omega.
          - twopower_left;
            setoid_replace x with (Qabs x) at 2 by (symmetry; now apply Qabs_pos);
            apply (twopowerQ_binadeQ_le _ _ x_nonzero); apply Z.le_refl.
        }
    + (* Case x <= 0. *)
      apply integer_le_floor.
      * (* x <= 0, showing f / 2^(e-p+1) is an integer *)
        apply (large_representable_is_integer p).
        {
          (* Showing that f / 2^(e-p+1) is representable *)
          apply scaled_representable_is_representable_div; now destruct f.
        }
        {
          (* Showing that 2^(p-1) <= |f / 2^(e-p+1)| *)
          match goal with
          | [ |- _ <= Qabs ?q ] => apply Qle_trans with (2 := Qle_Qabs_neg _)
          end.
          apply Qle_trans with
          (y := - (x / twopowerQ (binadeQ x x_nonzero - ' p + 1))).
          - (* Showing that 2^(p-1) <= -(x/2^(e-p+1)) *)
            twopower_left.
            setoid_replace (-x) with (Qabs x) by (symmetry; now apply Qabs_neg);
            apply (twopowerQ_binadeQ_le _ _ x_nonzero); apply Z.le_refl.
          - (* Showing that -x/2^(e-p+1) <= -f/2^(e-p+1) *)
            rewrite <- Qopp_le_mono; now twopower_left.
        }
      * (* Showing that f / 2^(e-p+1) <= x / 2^(e-p+1) (again!) *)
        now twopower_left.
  - (* Showing that f <= round x -> f <= x. *)
    apply Qle_trans with (1 := H); twopower_right; apply floor_spec;
    apply Z.le_refl.
Qed.


(* With the specification in place, it's straightforward to prove some
   of the basic properties of round_toward_negative. *)

Add Parametric Morphism (p : positive) : (round_toward_negative p) with
    signature Qeq ==> (@float_eq p) as round_toward_negative_morphism.
Proof.
  intros x y x_eq_y; apply float_le_antisymm;
  rewrite <- round_toward_negative_spec;
  [ rewrite <- x_eq_y | rewrite x_eq_y ];
  apply round_toward_negative_spec; apply float_le_refl.
Qed.


Add Parametric Morphism (p : positive) : (round_toward_positive p)
    with signature Qeq ==> (@float_eq p) as round_toward_positive_morphism.
Proof.
  intros; unfold round_toward_positive, float_eq;
  destruct (Qeq_dec x 0), (Qeq_dec y 0).
  - easy.
  - contradict n. now rewrite <- H.
  - contradict n. now rewrite H.
  - simpl.
    assert (binadeQ y n0 = binadeQ x n)%Z by (now apply binadeQ_equiv).
    rewrite H0.
    now setoid_rewrite <- H.
Qed.

Add Parametric Morphism p : (round_ties_to_even p)
    with signature Qeq ==> float_eq (p := p) as round_ties_to_even_morphism.
Proof.
  intros x y H; unfold round_ties_to_even, float_eq;
  destruct (Qeq_dec x 0), (Qeq_dec y 0).
  - easy.
  - contradict n. now rewrite <- H.
  - contradict n. now rewrite H.
  - simpl.
    assert (binadeQ y n0 = binadeQ x n)%Z by (now apply binadeQ_equiv).
    rewrite H0.
    now setoid_rewrite <- H.
Qed.

Lemma round_toward_negative_monotonic (p : positive) x y :
  x <= y  ->  (round_toward_negative p x <= round_toward_negative p y)%float.
Proof.
  intro. rewrite <- round_toward_negative_spec.
  apply Qle_trans with (y := x).
  apply round_toward_negative_spec. apply float_le_refl. easy.
Qed.

Lemma round_toward_negative_id (p : positive) x :
  representable p x  <->  proj1_sig (round_toward_negative p x) == x.
Proof.
  rewrite binary_floats_are_representable.
  split; intro.
  destruct H.
  rewrite <- H.
  apply Qle_antisym.
  rewrite round_toward_negative_spec.
  apply float_le_refl.
  fold (float_le (x0) (round_toward_negative p (proj1_sig x0))).
  rewrite <- round_toward_negative_spec. apply Qle_refl.

  now exists (round_toward_negative p x).
Qed.

(* Variant of the specification. *)

Lemma round_toward_negative_spec_lt p x (f : binary_float p) :
  x < proj1_sig f <-> (round_toward_negative p x < f)%float.
Proof.
  rewrite Qlt_nge, float_lt_nge; apply negate_iff, round_toward_negative_spec.
Qed.

(* Results for round_toward_positive. *)

Lemma round_toward_positive_opp p x :
  (- round_toward_negative p x == round_toward_positive p (-x))%float.
Proof.
  unfold round_toward_negative, round_toward_positive, float_eq.
  destruct (Qeq_dec x 0), (Qeq_dec (-x) 0); simpl.
  - easy.
  - contradict n; now rewrite q.
  - contradict n; rewrite <- Qopp_opp; now rewrite q.
  - assert (binadeQ x n = binadeQ (-x) n0)%Z as H by (apply binadeQ_opp).
    rewrite H.
    match goal with
    | [ |- - (?x * ?y) == _] => setoid_replace (-(x*y)) with ((-x) * y) by ring
    end.
    apply Qmult_inj_r with (1 := twopowerQ_nonzero _).
    rewrite <- inject_Z_opp.
    apply inject_Z_injective.
    rewrite neg_floor_is_ceiling_neg.
    apply ceiling_morphism.
    field.
    apply twopowerQ_nonzero.
Qed.


Lemma round_toward_positive_spec p x (f : binary_float p) :
  x <= proj1_sig f  <->  (round_toward_positive p x <= f)%float.
Proof.
  setoid_replace x with (- - x) at 2 by ring.
  rewrite <- round_toward_positive_opp.
  setoid_replace (- round_toward_negative p (-x) <= f)%float
  with (-f <= round_toward_negative p (-x))%float.
  rewrite <- round_toward_negative_spec.

  split; intros.
  apply le_neg_switch_r.
  setoid_replace (- proj1_sig (-f)%float) with (proj1_sig f).
  easy.
  unfold float_opp, float_eq. simpl. ring.
  setoid_replace (proj1_sig f) with (- proj1_sig (-f)%float).
  apply le_neg_switch_r.
  easy.
  unfold float_opp, float_eq. simpl. ring.

  split; intros.
  now apply le_neg_switch.
  now apply le_neg_switch.
Qed.


Lemma round_toward_positive_spec_lt p x (f : binary_float p) :
  proj1_sig f < x  <->  (f < round_toward_positive p x)%float.
Proof.
  rewrite Qlt_nge, float_lt_nge; apply negate_iff, round_toward_positive_spec.
Qed.


Lemma round_toward_positive_monotonic p x y :
  x <= y  ->  (round_toward_positive p x <= round_toward_positive p y)%float.
Proof.
  intro x_le_y.
  rewrite <- round_toward_positive_spec.
  apply Qle_trans with (1 := x_le_y).
  apply round_toward_positive_spec, float_le_refl.
Qed.

(* Lemma that we'll need for the main theorem: the only discontinuities
   of round_toward_negative are elements of binary_float p.  Here's a way
   to state that result: if x <= y and round(x) != round(y), then there's
   an element of binary_float p in [x, y] *)

Lemma round_toward_negative_discontinuities p (x y : Q) :
  x <= y  ->
  ~(round_toward_negative p x == round_toward_negative p y)%float ->
  exists (z : binary_float p), x <= proj1_sig z <= y.
Proof.
  intros; exists (round_toward_negative p y); split.
  - apply Qlt_le_weak, round_toward_negative_spec_lt, float_le_not_eq;
    try apply round_toward_negative_monotonic; easy.
  - apply round_toward_negative_spec, float_le_refl.
Qed.

(* And the corresponding result for round_toward_positive. *)

Lemma round_toward_positive_discontinuities p (x y : Q) :
  x <= y ->
  ~(round_toward_positive p x  ==  round_toward_positive p y)%float ->
  exists (z : binary_float p), x <= proj1_sig z <= y.
Proof.
  intros H H0; exists (round_toward_positive p x); split.
  - apply round_toward_positive_spec, float_le_refl.
  - apply Qlt_le_weak, round_toward_positive_spec_lt,
    float_le_not_eq with (2 := H0); now apply round_toward_positive_monotonic.
Qed.

(* Now we need to get some handle on round_ties_to_even.

   For example, we want to show that round_ties_to_even x
   is the closest float to x; i.e., that for any float f,

    | round x - x| <=  | f - x |

   Sketch of proof: consider the cases f <= x and x <= f.

   If f <= x then f <= round_down x, and so

    | round x - x | <= | x - round_down x | == x - round_down x
                    <= x - f == | f - x |.

   The case x <= f is analogous. *)

Lemma f_twopower_diff x n f :
  x - inject_Z (f(x / twopowerQ n)) * twopowerQ n ==
((x / twopowerQ n) - inject_Z (f(x / twopowerQ n))) * twopowerQ n.
Proof.
  field; apply twopowerQ_nonzero.
Qed.


Lemma round_ties_to_even_closer_than_round_toward_negative p x :
  Qabs (x - proj1_sig (round_ties_to_even p x)) <=
  Qabs (x - proj1_sig (round_toward_negative p x)).
Proof.
  unfold round_ties_to_even, round_toward_negative;
  destruct (Qeq_dec x 0) as [x_zero | x_nonzero].
  - (* Case x == 0. *)
    now rewrite x_zero.
  - (* Case x != 0. *)
    rewrite ?float_from_significand_and_exponent_Q.
    rewrite ?f_twopower_diff.
    rewrite ?Qabs_Qmult.
    rewrite ?Qabs_twopowerQ.
    generalize (x / twopowerQ (binadeQ x x_nonzero - ' p + 1)); intro q.
    twopower_right.
    apply round_as_close_as_floor.
Qed.


Lemma round_ties_to_even_closer_than_round_toward_positive p x :
  Qabs (x - proj1_sig (round_ties_to_even p x)) <=
  Qabs (x - proj1_sig (round_toward_positive p x)).
Proof.
  unfold round_ties_to_even, round_toward_positive;
  destruct (Qeq_dec x 0) as [x_zero | x_nonzero].
  - (* Case x == 0. *)
    now rewrite x_zero.
  - (* Case x != 0. *)
    rewrite ?float_from_significand_and_exponent_Q.
    rewrite ?f_twopower_diff.
    rewrite ?Qabs_Qmult.
    rewrite ?Qabs_twopowerQ.
    generalize (x / twopowerQ (binadeQ x x_nonzero - 'p + 1)); intro q.
    twopower_right.
    apply round_as_close_as_ceiling.
Qed.

Lemma round_ties_to_even_nearest p x (f : binary_float p) :
  Qabs (x - proj1_sig (round_ties_to_even p x)) <= Qabs (x - proj1_sig f).
Proof.
  destruct (Qle_ge_cases (proj1_sig f) x).
  - (* Case f <= x. *)
    apply Qle_trans with (y := Qabs (x - proj1_sig (round_toward_negative p x))).
    + (* | x - round x | <= | x - round_down x | *)
      apply round_ties_to_even_closer_than_round_toward_negative.
    + (* | x - round_down x | <= | x - f | *)
      rewrite ?Qabs_pos.
      rearrange_goal (proj1_sig f <= proj1_sig (round_toward_negative p x)).
      assert (f <= round_toward_negative p x)%float.
      now apply (round_toward_negative_spec p x f).
      assumption.
      rearrange.
      rearrange_goal (proj1_sig (round_toward_negative p x) <= x).
      apply round_toward_negative_spec.
      apply Qle_refl.
  - (* Case x <= f *)
    apply Qle_trans with (y := Qabs (x - proj1_sig (round_toward_positive p x))).
    + (* |x - round x | <= |x - round_up x | *)
      apply round_ties_to_even_closer_than_round_toward_positive.
    + (* |x - round_up x | <= |x - f| *)
      rewrite ?Qabs_neg.
      assert (round_toward_positive p x <= f)%float.
      now apply (round_toward_positive_spec p x f).
      unfold float_le in H0.
      rearrange.
      rearrange.
      rearrange_goal (x <= proj1_sig (round_toward_positive p x)).
      apply round_toward_positive_spec.
      apply Qle_refl.
Qed.

(* Claim: if round(x) < round(y) then there's a z representable in
   precision p + 1 such that x <= z <= y.

   Sketch of proof:

   First, we define next_up and next_down.

   Then we show that

   x <= (round(x) + next_up(round(x)) / 2
     <= round(y) + next_down(round(y)) / 2
     <= y.

   where the middle inequality holds because round(x) <= next_down(round(y))
   and next_up(round(x)) <= round(y).

   And those follow from:  f < g  <->  next_up(f) <= g,
                           f < g  <->  f <= next_down(g)
   for nonzero floats f and g.

   Note that next_up and next_down are only well-defined for nonzero
   floats.

   Finally we'll need to show that for a nonzero float f representable
   in precision p, (f + next_up(f)) / 2 is representable in precision
   p + 1, and similarly for next_down.
*)

Lemma round_toward_negative_le_round_ties_to_even p x :
  (round_toward_negative p x <= round_ties_to_even p x)%float.
Proof.
  unfold float_le.
  rearrange_goal (x - !round_ties_to_even p x <= x - !round_toward_negative p x).
  rewrite <- (Qabs_pos (x - !round_toward_negative p x)).
  apply Qle_trans with (y := Qabs (x - !round_ties_to_even p x)).
  apply Qle_Qabs.
  apply round_ties_to_even_nearest.
  rearrange_goal (!round_toward_negative p x <= x).
  apply round_toward_negative_spec.
  apply float_le_refl.
Qed.

Lemma round_ties_to_even_le_round_toward_positive p x :
  (round_ties_to_even p x <= round_toward_positive p x)%float.
Proof.
  unfold float_le.
  rearrange_goal (-(x - !round_ties_to_even p x) <= - (x - !round_toward_positive p x)).
  rewrite <- (Qabs_neg (x - !round_toward_positive p x)).
  apply Qle_trans with (y := Qabs (x - !round_ties_to_even p x)).
  apply Qle_Qabs_neg.
  apply round_ties_to_even_nearest.
  rearrange_goal (x <= !round_toward_positive p x).
  apply round_toward_positive_spec.
  apply float_le_refl.
Qed.

Lemma round_toward_negative_for_positive p x :
  0 < x  ->  (0 < round_toward_negative p x)%float.
Proof.
  intro.
  unfold round_toward_negative.
  destruct (Qeq_dec x 0); unfold float_lt.
  - now rewrite <- q at 2.
  - unfold float_from_significand_and_exponent; simpl;
    apply qpos.Q_mul_pos_pos with (2 := twopowerQ_positive _).
    apply Qlt_le_trans with (y := twopowerQ ('p - 1)).
    apply twopowerQ_positive.
    apply integer_le_floor.
    apply is_integer_twopowerQ.
    assert (0 < 'p)%Z by easy; omega.
    twopower_left.
    setoid_replace x with (Qabs x) at 2.
    apply (twopowerQ_binadeQ_le (binadeQ x n) x n), Z.le_refl.
    rewrite Qabs_pos. easy. apply Qlt_le_weak. easy.
Qed.


Lemma round_toward_positive_for_negative p x :
  x < 0  ->  (round_toward_positive p x < 0)%float.
Proof.
  intro; unfold round_toward_positive.
  destruct (Qeq_dec x 0); unfold float_lt.
  - now rewrite <- q at 1.
  - unfold float_from_significand_and_exponent; simpl.
    twopower_right.
    apply Qle_lt_trans with (y := -twopowerQ ('p - 1)).
    apply integer_le_ceiling.
    apply is_integer_neg.
    apply is_integer_twopowerQ.
    assert (0 < 'p)%Z by easy; omega.
    apply Qdiv_le_mult.
    apply twopowerQ_positive.
    match goal with
    | [ |- _ <= - ?a * ?b ] =>
      setoid_replace (- a * b) with (- (a * b)) by ring
    end.
    apply le_neg_switch_r.
    twopower_collect.
    twopower_exponent_simplify.
    rewrite <- Qabs_neg.
    eapply twopowerQ_binadeQ_le, Zle_refl.
    now apply Qlt_le_weak.
    rearrange_goal (0 < twopowerQ ('p - 1)).
    apply twopowerQ_positive.
Qed.

Lemma round_ties_to_even_for_positive p x :
  (0 < x)  ->  (0 < round_ties_to_even p x)%float.
Proof.
  intro; apply float_lt_le_trans with (y := round_toward_negative p x).
  - now apply round_toward_negative_for_positive.
  - apply round_toward_negative_le_round_ties_to_even.
Qed.

Lemma round_ties_to_even_for_negative p x :
  x < 0  ->  (round_ties_to_even p x < 0)%float.
Proof.
  intro; apply float_le_lt_trans with (y := round_toward_positive p x).
  - apply round_ties_to_even_le_round_toward_positive.
  - now apply round_toward_positive_for_negative.
Qed.

Lemma round_ties_to_even_for_nonzero p x :
  ~(x == 0) -> ~(round_ties_to_even p x == 0)%float.
Proof.
  intro x_nonzero.
  case (Qlt_gt_cases _ _ x_nonzero); intro.
  - now apply Qlt_not_eq, round_ties_to_even_for_negative.
  - now apply Qnot_eq_sym, Qlt_not_eq, round_ties_to_even_for_positive.
Qed.

Lemma round_toward_negative_for_nonzero p x :
  ~(x == 0) -> ~(round_toward_negative p x == 0)%float.
Proof.
  intro x_nonzero.
  case (Qlt_gt_cases _ _ x_nonzero); intro.
  - apply Qlt_not_eq.
    eapply Qle_lt_trans.
    apply round_toward_negative_spec.
    apply float_le_refl.
    easy.
  - now apply Qnot_eq_sym, Qlt_not_eq, round_toward_negative_for_positive.
Qed.

(* To show that x <= (round x + next_up (round x)) / 2 :
   This is equivalent to showing that

      2 * x <= round x + next_up (round x)

   or that

      x - round(x) <= next_up (round x) - x

   But this follows from the fact that round x is the closest
   float to x, on showing that next_up (round x) - x is nonnegative.
   That is, we must show that

       x <= next_up (round x)

   And this follows from

       x <= next_up (round_down x) <= next_up (round x)

   where the second inequality is clear, and the first inequality
   is equivalent to round_down x <= next_up (round_down x) by the
   specification of round_down.

 *)

(* x < !f iff round_down x < f *)
(* !f <= x iff !f <= round_down x. *)


Definition round_toward_negative_nz p x (x_nonzero : ~(x == 0)) : nonzero_float p.
Proof.
  refine [round_toward_negative p x].
  now apply round_toward_negative_for_nonzero.
Defined.

Definition round_toward_positive_nz p x (x_nonzero : ~(x == 0)) : nonzero_float p.
Proof.
  refine [round_toward_positive p x].
  case (Qlt_gt_cases _ _ x_nonzero); intro H.
  - now apply Qlt_not_eq, round_toward_positive_for_negative.
  - apply Qnot_eq_sym, Qlt_not_eq, Qlt_le_trans with (1 := H),
    round_toward_positive_spec, float_le_refl.
Defined.

Definition round_ties_to_even_nz p x (x_nonzero : ~(x == 0)) : nonzero_float p.
Proof.
  refine [round_ties_to_even p x]; now apply round_ties_to_even_for_nonzero.
Defined.


Lemma x_le_next_up_round_x p x x_nonzero :
  x < !!next_up (round_ties_to_even_nz p x x_nonzero).
Proof.
  apply round_toward_negative_spec_lt;
  change (round_toward_negative p x)
  with (!round_toward_negative_nz p x x_nonzero);
  apply next_up_spec_alt, round_toward_negative_le_round_ties_to_even.
Qed.

(* Now we want to show that for any nonzero x,
   x <= (round x + next_up (round x)) / 2. *)

Definition next_tie_up p x x_nonzero : Q :=
  let f := round_ties_to_even_nz p x x_nonzero in
  (!!f + !!next_up f) / 2.


Theorem ties_representable p (f : nonzero_float p) :
  representable (p + 1) ((!!f + !!next_up f) / 2).
Proof.
  unfold next_up. unfold float_from_significand_and_exponent.
  rewrite <- reconstruct_float.
  simpl.
  rewrite <- Qmult_plus_distr_l.
  change 2 with (twopowerQ 1).
  apply scaled_representable_is_representable_div.
  apply scaled_representable_is_representable.
  rewrite <- inject_Z_plus.
  apply small_integers_are_representable.
  pose proof (low_significand_bound f).
  destruct (float_by_sign f); unfold low_significand;
  repeat (rewrite inject_Z_plus);
  setoid_replace (inject_Z (floor (low_significand_Q f)))
  with (low_significand_Q f)
    by (apply floor_integer, low_significand_is_integer);
  rewrite Pos2Z.inj_add.
  - rewrite Qabs_pos.
    + apply Qlt_le_succ.
      * repeat apply is_integer_add;
        (apply low_significand_is_integer || apply is_integer_inject_Z).
      * now apply is_integer_twopowerQ.
      * rearrange_goal
          ((low_significand_Q f + 1) * 2 <= twopowerQ (' p + 1)).
        (* Should make this change part of twopower_prepare. *)
        change 2 with (twopowerQ 1).
        twopower_right.
        apply Qlt_le_succ.
        apply low_significand_is_integer.
        now apply is_integer_twopowerQ.
        easy.
    + assert (0 <= low_significand_Q f) by
          (eapply Qle_trans; [ apply twopowerQ_nonnegative | apply H]).
      repeat (change 0 with (0 + 0); apply Qplus_le_compat; try easy).
  - rewrite Qabs_neg.
    + apply Qlt_le_succ.
      * apply is_integer_neg; repeat apply is_integer_add;
        (apply low_significand_is_integer || apply is_integer_inject_Z).
      * now apply is_integer_twopowerQ.
      * rearrange_goal
          (- twopowerQ (' p + 1) <= low_significand_Q f * 2).
        change 2 with (twopowerQ 1).
        apply remedial.le_neg_switch.
        twopower_right.
        apply remedial.le_neg_switch.
        easy.
    + rearrange_goal (2 * low_significand_Q f + 1 <= 0).
      apply Qlt_le_succ.
      apply is_integer_mul.
      apply is_integer_inject_Z.
      apply low_significand_is_integer.
      apply is_integer_inject_Z.
      scale_by (/ 2).
      easy.
      rearrange_goal (low_significand_Q f < 0).
      eapply Qlt_trans.
      apply H.
      rearrange_goal (0 < twopowerQ ('p - 1)).
      apply twopowerQ_positive.
Qed.

Lemma le_next_tie_up p x x_nonzero : x <= next_tie_up p x x_nonzero.
Proof.
  unfold next_tie_up.
  set (f := round_ties_to_even_nz p x x_nonzero).
  scale_by 2. now compute.
  rearrange_goal (x - !!f <= !!next_up f - x).
  apply Qle_trans with (y := Qabs (x - !!f)).
  apply Qle_Qabs.
  setoid_replace (!!next_up f - x) with (Qabs (x - !!next_up f)).
  apply round_ties_to_even_nearest.
  rewrite Qabs_neg.
  rearrange.
  rearrange_goal (x <= !!next_up f).
  unfold f.
  apply Qlt_le_weak.
  apply x_le_next_up_round_x.
Qed.

Definition next_tie_down p x x_nonzero : Q :=
  let f := round_ties_to_even_nz p x x_nonzero in
  (!!next_down f + !!f) / 2.

Lemma next_tie_down_le p x x_nonzero : next_tie_down p x x_nonzero <= x.
Proof.
  unfold next_tie_down.
  set (f := round_ties_to_even_nz p x x_nonzero).
  scale_by 2. now compute.
  rearrange_goal (-(x - !!f) <= x - !!next_down f).
  apply Qle_trans with (y := Qabs (x - !!f)).
  apply Qle_Qabs_neg.
  setoid_replace (x - !!next_down f) with (Qabs (x - !!next_down f)).
  apply round_ties_to_even_nearest.
  rewrite Qabs_pos. easy.
  rearrange_goal (!!next_down f <= x).
  apply Qlt_le_weak.
  apply round_toward_positive_spec_lt.
  change (round_toward_positive p x)
  with (!round_toward_positive_nz p x x_nonzero).
  apply next_down_spec_alt, round_ties_to_even_le_round_toward_positive.
Qed.

Theorem round_ties_to_even_jumps p x y :
  (round_ties_to_even p x < round_ties_to_even p y)%float ->
  exists h, (representable (p + 1) h /\ x <= h <= y).
Proof.
  (* Divide into cases x zero, x nonzero, and similarly for y. *)
  intro; destruct (Qeq_dec x 0) as [x_zero | x_nonzero];
  destruct (Qeq_dec y 0) as [y_zero | y_nonzero].
  - (* Case x == y == 0. Here round_ties_to_even p x < round_ties_to_even p y
       gives a contradiction. *)
    setoid_rewrite x_zero in H.
    setoid_rewrite y_zero in H.
    now compute in H.
  - (* Case x == 0, y != 0 *)
    assert (round_ties_to_even p x == 0)%float
      by (rewrite x_zero; now compute); rewrite H0 in H.
    exists (next_tie_down p y y_nonzero).
    split.
    + unfold next_tie_down; generalize (round_ties_to_even_nz p y y_nonzero);
      intro; setoid_rewrite <- next_up_next_down at 2;
      apply ties_representable.
    + split.
      * rewrite x_zero.
        unfold next_tie_down.
        apply Qmult_le_div.
        easy.
        change (0 * 2) with (0 + 0).
        apply Qplus_le_compat; apply Qlt_le_weak.
        change 0 with (! (zero_float p)).
        apply next_down_positive.
        easy.
        easy.
      * apply next_tie_down_le.
  - (* Case x != 0, y == 0 *)
    assert (round_ties_to_even p y == 0)%float
      by (rewrite y_zero; now compute); rewrite H0 in H.
    exists (next_tie_up p x x_nonzero).
    rewrite y_zero. clear H0 y_zero.
    split.
    + apply ties_representable.
    + split.
      * apply le_next_tie_up.
      * unfold next_tie_up.
        apply Qdiv_le_mult; try easy.
        change (0 * 2) with (0 + 0).
        apply Qplus_le_compat; apply Qlt_le_weak;
        now try apply next_up_negative.
  - (* Final case: x, y both nonzero. *)
    exists (next_tie_up p x x_nonzero).
    split.
    + apply ties_representable.
    + split.
      * apply le_next_tie_up.
      * apply Qle_trans with (y := next_tie_down p y y_nonzero).
        unfold next_tie_up, next_tie_down.
        apply Qmult_le_r.
        easy.
        apply Qplus_le_compat.
        apply next_down_spec.
        easy.
        apply next_up_spec.
        easy.
        apply next_tie_down_le.
Qed.
