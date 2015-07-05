(* Definitions and properties of rounding modes for binary floats. *)

(* We start with the round_toward_negative (rtn) rounding mode.  Given a rational
   number x, we'll construct the closest binary float (at precision p)
   that doesn't exceed x.

   We'll construct the float by giving its significand and exponent.  To do
   that, we'll need a lemma that the significand is bounded. *)

Require Import Qabs.

Require Import remedial.
Require Import floor_and_ceiling.
Require Import twopower.
Require Import binary_float.

Local Open Scope Q.

(* Some tactics for dealing with powers of 2. *)

(* To prove representability, we need to know that the significand is bounded. *)

Ltac twopower_l_to_r :=
  match goal with
  | [ |- _ / twopowerQ _ <= _ ] => apply Qdiv_le_mult with (1 := twopowerQ_positive _)
  | [ |- _ * twopowerQ _ <= _ ] => apply Qmult_le_div with (1 := twopowerQ_positive _)
  end.

Ltac twopower_r_to_l :=
  match goal with
  | [ |- _ <= _ / twopowerQ _ ] => apply Qmult_le_div with (1 := twopowerQ_positive _)
  | [ |- _ <= _ * twopowerQ _ ] => apply Qdiv_le_mult with (1 := twopowerQ_positive _)
  end.

Ltac twopower_prepare :=
  try match goal with
      | [ |- - (?n / twopowerQ ?e) <= _ ] =>
        setoid_replace (- (n / twopowerQ e)) with ((-n) / twopowerQ e)
          by (field; apply twopowerQ_nonzero)
      | [ |- _ <= - (?n / twopowerQ ?e)] =>
        setoid_replace (- (n / twopowerQ e)) with ((-n) / twopowerQ e)
          by (field; apply twopowerQ_nonzero)
      | [ |- - (?n * twopowerQ ?e) <= _ ] =>
        setoid_replace (- (n * twopowerQ e)) with ((-n) * twopowerQ e) by ring
      | [ |- Qabs (_ / twopowerQ ?e) <= _ ] =>
        rewrite Qabs_div, Qabs_twopowerQ; [ | apply twopowerQ_nonzero ]
      end.

(* Tactics to be applied post moving powers of two around. *)

Ltac twopower_collect :=
  try match goal with
      | [ |- _ <= twopowerQ _ * twopowerQ _ ] => rewrite <- twopowerQ_mul
      | [ |- _ <= twopowerQ _ / twopowerQ _ ] => rewrite <- twopowerQ_div
      | [ |- twopowerQ _ * twopowerQ _ <= _ ] => rewrite <- twopowerQ_mul
      | [ |- _ / twopowerQ _ * twopowerQ _ <= _ ] =>
        unfold Qdiv;
          rewrite <- twopowerQ_inv;
          rewrite <- Qmult_assoc;
          rewrite <- twopowerQ_mul
      end.

Ltac twopower_cleanup :=
  try match goal with
      | [ |- _ * twopowerQ 0 <= _ ] => replace (twopowerQ 0) with 1 by easy;
          rewrite Qmult_1_r
      | [ |- 0 * twopowerQ _ <= _ ] => rewrite Qmult_0_l
      | [ |- _ <= 0 * twopowerQ _ ] => rewrite Qmult_0_l
      end.


Ltac twopower_exponent_simplify :=
  try match goal with
      | [ |- _ <= twopowerQ ?e ] => ring_simplify e
      | [ |- twopowerQ ?e <= _ ] => ring_simplify e
      | [ |- _ <= _ * twopowerQ ?e ] => ring_simplify e
      | [ |- _ * twopowerQ ?e <= _ ] => ring_simplify e
      end.

Ltac twopower_left := twopower_prepare; twopower_r_to_l; twopower_collect;
                      twopower_exponent_simplify; twopower_cleanup.
Ltac twopower_right := twopower_prepare; twopower_l_to_r; twopower_collect;
                      twopower_exponent_simplify; twopower_cleanup.


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
  rewrite <- round_toward_negative_spec; [ rewrite <- x_eq_y | rewrite x_eq_y ];
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

(* XXX This one should go elsewhere. *)

Add Parametric Morphism (p : positive) : (proj1_sig (A:=Q) (P:=representable p)) with
    signature (@float_eq p) ==> Qeq as inclusion_morphism.
Proof.
  intros x y.
  unfold float_eq.
  easy.
Qed.

(* XXX And this one, too. *)

Add Parametric Morphism (p : positive) : (@float_le p)
    with signature (@float_eq p) ==> (@float_eq p) ==> iff as float_le_morphism.
Proof.
  unfold float_eq, float_le.
  intros.
  rewrite H.
  rewrite H0.
  easy.
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
  (round_toward_negative p x <> round_toward_negative p y)%float ->
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
  (round_toward_positive p x  <>  round_toward_positive p y)%float ->
  exists (z : binary_float p), x <= proj1_sig z <= y.
Proof.
  intros H H0; exists (round_toward_positive p x); split.
  - apply round_toward_positive_spec, float_le_refl.
  - apply Qlt_le_weak, round_toward_positive_spec_lt,
    float_le_not_eq with (2 := H0); now apply round_toward_positive_monotonic.
Qed.
