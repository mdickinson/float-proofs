(* Proofs of the main theorems. *)

Require Import ZArith.
Require Import QArith.
Require Import Qabs.

Require Import floor_and_ceiling.
Require Import binary_float.
Require Import separation_results.
(* Importing this just for the [ ] and ! notations;
   move them elsewhere. *)
Require Import next_up.
Require Import twopower.
Require Import rounding.
Require Import rearrange_tactic.

Section MainTheorem.

  Variables p q r : positive.
  Variable x : binary_float p.
  Variable y : binary_float q.

  Hypothesis x_nonzero : ~(x == 0)%float.
  Hypothesis y_nonzero : ~(y == 0)%float.
  Hypothesis p_small : ('p <= 'q + 'r)%Z.
  Hypothesis x_over_y_large : twopowerQ ('q + 'r) <= Qabs (!x / !y).

  Theorem round_floor_is_round_ceiling :
    (round_ties_to_even r (floorQ (!x / !y)) ==
     round_ties_to_even r (ceilingQ (!x / !y)))%float.
  Proof.
    (* Proof:

       Suppose not.

       Then round (floor (x / y)) < round (ceiling (x / y)).

       So there's a z representable in precision r + 1
       such that 

           floor (x / y) <= z <= ceiling (x / y).
  
       Then by the first separation theorem,

           x / y == z.

       But then x / y is an integer, so ... contradiction.

    *)

    (* Start the proof by contradiction, by assuming that the two
       values are unequal. *)
    destruct (float_eq_dec (round_ties_to_even r (floorQ (!x / !y)))
                           (round_ties_to_even r (ceilingQ (!x / !y)))); try easy;
    try easy; exfalso.

    assert (round_ties_to_even r (floorQ (!x / !y)) <
            round_ties_to_even r (ceilingQ (!x / !y)))%float.
    apply float_le_not_eq.
    apply round_ties_to_even_monotonic.
    apply Qle_trans with (y := (!x / !y)).
    apply floor_spec, Z.le_refl.
    apply ceiling_spec, Z.le_refl.
    easy.

    (* Now we're reduced to the assumption that round (floor (x / y)) <
       round (ceiling (x / y)). *)
    destruct (round_ties_to_even_jumps r (floorQ (!x / !y)) (ceilingQ (!x / !y)) H)
             as [ z [z_representable z_bounds] ].
    set (z_as_float := (exist _ z z_representable : binary_float (r + 1))).

    change z with (!z_as_float) in z_bounds.
    assert (!x / !y == !z_as_float).
    apply first_separation_theorem.
    easy.
    easy.
    easy.
    rewrite Pos2Z.inj_add; omega.
    rewrite Pos2Z.inj_add; setoid_replace ('q + ('r + 1) - 1)%Z with ('q + 'r)%Z.
    easy.
    omega.

    (* Now we've shown that !x / !y == !z_as_float.  But this should be
       a contradiction...  Why? *)
    (* We need to show that z is an integer.  This follows from the fact
       that large representable numbers are integers... *)
    assert (is_integer z).
    apply (large_representable_is_integer (r + 1)).
    easy.
    rewrite Pos2Z.inj_add.
    setoid_replace ('r + 1 - 1)%Z with ('r)%Z by omega.
    (* Need to show that 2^r <= |z|.
       We know that floor(abs(x / y)) <= |z|.
       so enough to show that 2^r <= floor (abs (x / y))
       which is equivalent to showing that 2^r <= abs (x / y),
       since 2^r is integral.  But that property we have in spades. *)
    apply Qle_trans with (y := floorQ (Qabs (!x / !y))).
    apply Qabs_case; intro.
    apply integer_le_floor.
    apply is_integer_twopowerQ.
    easy.
    setoid_rewrite <- Qabs_pos at 2.
    apply Qle_trans with (2 := x_over_y_large).
    apply twopowerQ_monotonic_le.
    assert (0 <= 'q)%Z by easy.
    omega.
    easy.
    setoid_replace (floorQ (- (!x / !y)))
    with (- ceilingQ (!x / !y)).
    apply remedial.le_neg_switch_r.
    apply integer_le_ceiling.
    apply is_integer_neg.
    apply is_integer_twopowerQ.
    easy.
    apply remedial.le_neg_switch_r.
    setoid_rewrite <- Qabs_neg.
    apply Qle_trans with (2 := x_over_y_large).
    apply twopowerQ_monotonic_le.
    assert (0 <= 'q)%Z by easy.
    omega.
    easy.
    unfold floorQ, ceilingQ.
    rewrite <- inject_Z_opp.
    f_equiv.
    now rewrite neg_ceiling_is_floor_neg.
    (* Now showing that floor |x / y| <= | z |,
       given that floor (x / y) <= z <= ceiling (x / y). *)
    (* Divide into cases: either x / y <= 0, or x / y >= 0. *)
    apply Qabs_case; intro.
    (* Case 1: 0 <= x / y. *)
    rewrite Qabs_pos.
    easy.
    apply Qle_trans with (y := floorQ (!x / !y)).
    apply integer_le_floor.
    exists (0%Z). easy.
    easy.
    easy.
    (* Case 2: x / y <= 0. *)
    rewrite Qabs_neg.
    setoid_replace (floorQ (- (!x / !y)))
    with (- ceilingQ (!x / !y)).
    rearrange_goal (z <= ceilingQ (!x / !y)).
    easy.
    unfold floorQ, ceilingQ.
    rewrite <- inject_Z_opp.
    f_equiv.
    now rewrite neg_ceiling_is_floor_neg.
    apply Qle_trans with (y := ceilingQ (!x / !y)).
    easy.
    apply integer_le_ceiling.
    now (exists 0%Z).
    easy.

    (* Now we know that z is an integer. This should contradict H. *)
    assert (floorQ (!x / !y) == ceilingQ (!x / !y)).
    setoid_replace (floorQ (!x / !y)) with (!x / !y).
    setoid_replace (ceilingQ (!x / !y)) with (!x / !y).
    easy.
    apply ceiling_integer.
    rewrite H0.
    easy.
    apply floor_integer.
    rewrite H0.
    easy.
    assert (round_ties_to_even r (floorQ (!x / !y)) ==
            round_ties_to_even r (ceilingQ (!x / !y)))%float.
    rewrite H2.
    easy.
    contradiction.
  Qed.

End MainTheorem.

Check round_floor_is_round_ceiling.