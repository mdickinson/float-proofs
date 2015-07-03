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



(* Twopower cases we have to deal with:

   _ / twopowerQ _ <= twopowerQ _

   - (_ / twopowerQ _) <= twopowerQ _

   _ <= _ * twopowerQ _

   twopowerQ _ <= _ / twopowerQ _

   _ / twopowerQ e <= _ / twopowerQ e

   - (_ / twopowerQ e) <= - (_ / twopowerQ e)

   *)



(* There are two cases: x is zero, or x is nonzero. Let's first assume that x
   is nonzero. Then we can construct the significand and exponent directly. *)

Section RoundTowardNegativeNonzero.

Variable p : positive.
Variable x : Q.

Hypothesis x_nonzero : ~(x == 0).

Let exponent : Z := (binadeQ x x_nonzero - (' p) + 1)%Z.
Let scale : Q := twopowerQ exponent.
Let significand : Z := floor (x / scale).

(* Prove that the significand is bounded. *)

Lemma _rtn_significand_bound : Qabs (inject_Z significand) <= twopowerQ (' p).
Proof.
  apply Qabs_case; intros _; subst significand scale exponent.
  - apply floor_spec, floor_monotonic;
    twopower_right;
    apply Qlt_le_weak, Qle_lt_trans with (1 := Qle_Qabs _),
                                         (twopowerQ_binadeQ_lt _ _ x_nonzero); omega.
  - setoid_rewrite <- inject_Z_opp; setoid_rewrite neg_floor_is_ceiling_neg;
    apply integer_le_ceiling2; [ now apply is_integer_twopowerQ | ];
    twopower_right;
    apply Qlt_le_weak, Qle_lt_trans with (1 := Qle_Qabs_neg _),
      (twopowerQ_binadeQ_lt _ _ x_nonzero); omega.
Qed.

Definition _rtn_nonzero : binary_float p :=
  float_from_significand_and_exponent p significand exponent
                                      _rtn_significand_bound.

End RoundTowardNegativeNonzero.

(* Now we can finally define the round_toward_negative rounding mode. *)

Definition round_toward_negative p x : binary_float p :=
  match Qeq_dec x 0 with
  | left _ => zero_float p
  | right x_nonzero => _rtn_nonzero p x x_nonzero
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
