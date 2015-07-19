(* Definitions of next_up and next_down for binary floats. *)

(* For a positive float f, we can define next_up f as

   (f / twopowerQ (binadeQ f)) + 1) * twopowerQ (binadeQ f) *)

Require Import ZArith.
Require Import QArith.
Require Import Qabs.
Require Import remedial.
Require Import rearrange_tactic.
Require Import floor_and_ceiling.
Require Import twopower.
Require Import twopower_tactics.
Require Import binary_float.

(* We need a function to decompose a nonzero float into its exponent
   and significand, as integers. *)

Section NonzeroFloatResults.

  (* First assume that we have a nonzero float. *)
  Variable p : positive.
  Variable f : binary_float p.
  Variable f_nonzero : ~(proj1_sig f == 0).

  (* The exponent is straightforward.  We first define the significand
     in Q, then we need to show that it's an integer. *)
  Let exponent := (binadeQ (proj1_sig f) f_nonzero - (' p) + 1)%Z.
  Let significand := floor (proj1_sig f / twopowerQ exponent).
  
  Let significandQ := proj1_sig f / twopowerQ exponent.
  Definition decompose_float := (significand, exponent).

  Lemma significandQ_is_integer : is_integer significandQ.
  Proof.
    destruct f as [x [ m [e [m_small xme]] ]];
    subst significandQ exponent;
    setoid_replace
      (x / twopowerQ (binadeQ x f_nonzero - 'p + 1))
    with (
      ((x / twopowerQ e) *
       (twopowerQ e / twopowerQ (binadeQ x f_nonzero - 'p + 1)))).
    - (* Showing that the product is an integer. *)
      apply is_integer_mul.
      + (* is_integer (x / 2^e) *)
        exists m; twopower_left; now symmetry.
      + (* is_integer (twopower / twopower) *)
        rewrite <- twopowerQ_div;
        apply is_integer_twopowerQ;
        assert (binadeQ x f_nonzero < e + ' p)%Z; [ | omega];
        apply twopowerQ_binadeQ_lt;
        rewrite xme;
        now twopower_right.
    - field; split; apply twopowerQ_nonzero.
  Qed.

  Lemma undecompose_float :
    proj1_sig f == inject_Z (significand) * twopowerQ exponent.
  Proof.
    assert (inject_Z (significand) == significandQ) by
        (apply floor_integer, significandQ_is_integer);
    subst significandQ; twopower_left; now symmetry.
  Qed.

  Lemma significand_bounded :
    twopowerQ (' p - 1) <= Qabs (inject_Z significand) < twopowerQ ('p).
  Proof.
    setoid_replace (inject_Z significand) with significandQ by
        (apply floor_integer, significandQ_is_integer);
    subst significandQ exponent; split.
    - twopower_left; apply (twopowerQ_binadeQ_le _ _ f_nonzero); omega.
    - twopower_right; apply (twopowerQ_binadeQ_lt _ _ f_nonzero); omega.
  Qed.

End NonzeroFloatResults.

Check decompose_float.
Check significand_bounded.
Check undecompose_float.