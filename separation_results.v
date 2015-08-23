(* Prove the two main separation lemmas. *)

Require Import QArith.
Require Import Qabs.

Require Import rearrange_tactic.
Require Import remedial.
Require Import qpos.
Require Import is_integer.
Require Import floor_and_ceiling.
Require Import is_multiple_of.
Require Import twopower.
Require Import twopower_tactics.
Require Import binade.
Require Import binary_float.

Local Open Scope Q.

Lemma is_multiple_of_twopower (m n : Z) :
  (m <= n)%Z  ->  is_multiple_of (twopowerQ m) (twopowerQ n).
Proof.
  exists (twopowerQ (n - m)); split.
  - apply is_integer_twopowerQ; omega.
  - now twopower_left.
Qed.

(* We need to know that binadeQ behaves nicely with respect to multiplication
   by powers of two.  Here's the QPos version of the theorem we need. *)

Lemma binade_for_twopower_multiple (e : Z) (x y : QPos) :
  (y == twopower e * x)%QPos ->  (binade y = e + binade x)%Z.
Proof.
  (* Prove an inequality in both directions. *)
  intro H; apply Z.le_antisymm.

  (* Showing that binade y <= e + binade x. *)
  apply Zplus_le_reg_l with (p := (-e)%Z); ring_simplify.
  apply twopower_binade_le.
  replace (-e + binade y)%Z with (binade y - e)%Z by ring.
  rewrite twopower_div.
  apply QPos_div_mul_le_r.
  rewrite QPos.mul_comm.
  rewrite <- H.
  apply twopower_binade_le.
  apply Z.le_refl.

  (* Showing that e + binade x <= binade y. *)
  apply twopower_binade_le.
  rewrite twopower_mul.
  rewrite H.
  apply QPos.mul_le_mono_l.
  apply twopower_binade_le.
  apply Z.le_refl.
Qed.


Lemma binadeQ_for_twopower_multiple (e : Z) (x : Q)
  (x_nonzero : ~(x == 0)) (y : Q) (y_nonzero: ~(y == 0)) :
  y == twopowerQ e * x  ->  (binadeQ y y_nonzero = e + binadeQ x x_nonzero)%Z.
Proof.
  intro H.
  unfold binadeQ.
  set (xpos := exist _ (Qabs x) (Qabs_nonzero x x_nonzero)).
  set (ypos := exist _ (Qabs y) (Qabs_nonzero y y_nonzero)).

  assert (Qabs y == twopowerQ e * Qabs x).
  assert (twopowerQ e == Qabs (twopowerQ e)).
  symmetry.
  apply Qabs_pos.
  apply Qlt_le_weak.
  unfold twopowerQ.
  now destruct (twopower e).

  rewrite H0.
  rewrite H.
  apply Qabs_Qmult.

  assert (ypos == twopower e * xpos)%QPos.
  unfold QPos.eq.
  assert (twopowerQ e == inject_Z 2 ^ e) by easy.
  simpl; now rewrite <- H1.

  (* Now we're reduced to a statement in QPos. *)
  now apply binade_for_twopower_multiple.
Qed.


(*
   ulp of a nonzero float x at precision p is 2**(binade x - p + 1).

   if x = m * 2**e with 2**(p-1) <= m < 2**p, then

   2**(p-1+e) <= x < 2**(p+e), so binade(x) = p-1+e.
   so e = binade(x) - p + 1.
*)

Definition ulp p (x : binary_float p) (x_nonzero : ~(proj1_sig x == 0)) : Q :=
  twopowerQ (binadeQ (proj1_sig x) x_nonzero - 'p + 1).

Lemma is_multiple_of_ulp p (x : binary_float p)
  (x_nonzero : ~(proj1_sig x == 0)) :
    is_multiple_of (ulp _ x x_nonzero) (proj1_sig x).
Proof.
  unfold ulp.
  unfold is_multiple_of.
  unfold binary_float in x.
  destruct x. simpl.
  simpl in x_nonzero.
  unfold representable in r.
  destruct r as [m H0].
  destruct H0 as [e H1].
  destruct H1 as [m_is_small x_is_m_2e].

  (* We now have that x = m * 2^e, with |m| < 2^p,
     and we must show that x = m0 * 2^(binade(x) - p + 1)
     for some integer m0.  It's therefore enough to show
     that e >= binade(x) - p + 1.

     And that follows from:
        binade(x) == binade(m) + e, and
        binade(m) <= p - 1.
  *)

  assert(m_nonzero : ~(inject_Z m == 0)).
  intro H.
  rewrite H in x_is_m_2e.

  rewrite Qmult_0_l in x_is_m_2e.
  apply x_nonzero.
  easy.

  assert(binadeQ x x_nonzero = binadeQ (inject_Z m) m_nonzero + e)%Z.
  rewrite Z.add_comm.
  apply binadeQ_for_twopower_multiple.
  rewrite Qmult_comm.
  easy.

  rewrite H.
  setoid_rewrite x_is_m_2e.

  (* Now showing that there's an integral m0 such that:

       m*2^e == m0*2^(binade m + e - 'p + 1)

       That m0 must be m * 2^('p - 1 - binade m). *)

  exists (inject_Z m * twopowerQ ('p - 1 - binadeQ (inject_Z m) m_nonzero)).
  split.
  apply is_integer_mul.
  apply is_integer_inject_Z.
  apply is_integer_twopowerQ.

  assert (binadeQ (inject_Z m) m_nonzero < 'p)%Z.
  unfold binadeQ.
  set (mpos := exist _ (Qabs (inject_Z m))
                     (Qabs_nonzero (inject_Z m) m_nonzero)).
  apply twopower_binade_lt.
  easy.

  omega.

  rewrite <- Qmult_assoc.
  rewrite <- twopowerQ_mul.
  replace ('p - 1 - binadeQ (inject_Z m) m_nonzero +
           (binadeQ (inject_Z m) m_nonzero + e - 'p + 1))%Z with e by ring.
  reflexivity.
Qed.

Lemma large_floats_are_integral (p : positive) (x : binary_float p) :
  let y := proj1_sig x in
  twopowerQ ('p - 1) <= Qabs y  ->  is_integer y.
Proof.
  apply large_representable_is_integer; now destruct x.
Qed.

Lemma abs_floor (x y : Q) :
  inject_Z (floor x) <= y <= inject_Z (ceiling x)  ->
  inject_Z (floor (Qabs x)) <= Qabs y.
Proof.
  intros.
  (* Cases: x <= 0 versus x >= 0; y <= 0 versus y >= 0. *)
  apply Qabs_case; intro; apply Qabs_case; intro.
  (* 0 <= x, 0 <= y *)
  easy.
  (* 0 <= x, y <= 0 *)
  apply Qle_trans with (y := 0).

  apply Qle_trans with (y := y).
  easy.
  easy.
  replace 0 with (- 0) by auto.
  apply Qopp_le_compat; easy.

  (* case x <= 0 <= y *)
  apply Qle_trans with (y := 0).
  apply Qopp_le_mono.
  replace (- 0) with 0 by auto.
  apply Qle_trans with (y := y). easy.
  rewrite <- inject_Z_opp.
  rewrite neg_floor_is_ceiling_neg.
  assert (- - x == x).
  apply Qopp_involutive.
  rewrite H2.
  easy.
  easy.

  (* case x <= 0, y <= 0 *)
  rewrite <- neg_ceiling_is_floor_neg; rewrite inject_Z_opp.
  destruct H. rearrange.
Qed.


Section SeparationTheorems.

(* In this section we assemble the hypotheses and results common to
   both separation theorems. *)

(* We start with x, y and z floating-point numbers of precisions p, q and r
   respectively. *)

Variables p q r : positive.
Variable x : binary_float p.
Variable y : binary_float q.
Variable z : binary_float r.

(* Next, we assume that x and y are nonzero, and deduce that x/y is, too. *)

Hypothesis x_nonzero : ~ proj1_sig x == 0.
Hypothesis y_nonzero : ~ proj1_sig y == 0.

Let x_over_y := proj1_sig x / proj1_sig y.

Lemma x_over_y_nonzero : ~(x_over_y == 0).
Proof.
  subst x_over_y.
  contradict x_nonzero.
  scale_by (/(proj1_sig y)).
  rewrite x_nonzero.
  ring.
Qed.

(* We assume that floor(x/y) <= z <= ceiling(x/y). *)

Hypothesis z_bounds : floorQ x_over_y <= proj1_sig z <= ceilingQ x_over_y.

(* We introduce the binades of x, y and z as separate variables. *)

Let a := binadeQ (proj1_sig x) x_nonzero.
Let b := binadeQ (proj1_sig y) y_nonzero.
Let c := binadeQ x_over_y x_over_y_nonzero.

(* We'll show that x and y*z are both multiples of quantum. *)

Let quantum := twopowerQ (b + 1).

Lemma x_over_y_minus_z_small : Qabs (x_over_y - proj1_sig z) < 1.
Proof.
  apply Qabs_case; destruct z_bounds; intro.
  (* Split: show x/y - z < 1 and z - x/y < 1. *)
  - apply Qle_lt_trans with (y := x_over_y - floorQ x_over_y).
    + rearrange.
    + rearrange_goal (x_over_y < floorQ x_over_y + inject_Z 1);
      unfold floorQ; rewrite <- inject_Z_plus; apply floor_spec_lt; omega.
  - apply Qle_lt_trans with (y := ceilingQ x_over_y - x_over_y).
    + rearrange.
    + rearrange_goal (ceilingQ x_over_y - inject_Z 1 < x_over_y);
      unfold Qminus, ceilingQ; rewrite <- inject_Z_opp, <- inject_Z_plus;
      apply ceiling_spec_lt; omega.
Qed.

Lemma x_minus_yz_small :
  Qabs (proj1_sig x - (proj1_sig y) * (proj1_sig z)) < quantum.
Proof.
  apply Qlt_trans with (y := Qabs (proj1_sig y)).
  rewrite <- Qmult_lt_r with (z := / Qabs (proj1_sig y)).
  field_simplify.
  rewrite <- Qabs_div.
  setoid_replace ((proj1_sig x - proj1_sig y * proj1_sig z) / proj1_sig y)
    with (proj1_sig x / proj1_sig y - proj1_sig z) by field.
  apply x_over_y_minus_z_small.
  easy.
  assumption.
  intro. apply y_nonzero. apply Qabs_zero. easy.
  intro. apply y_nonzero. apply Qabs_zero. easy.
  apply Qinv_lt_0_compat.
  apply Qabs_nonzero.
  assumption.

  subst quantum.
  apply (twopowerQ_binadeQ_lt (b + 1) (proj1_sig y) (y_nonzero)).
  subst b.
  omega.
Qed.


Section FirstSeparationTheorem.

(* Let's take just one of the cases of the theorem, the case where p < q + r
   and abs(x / y) >= twopower (q + r - 1). *)

Hypothesis p_small : ('p < 'q + 'r)%Z.

Hypothesis x_over_y_large :
  twopowerQ ('q + 'r - 1) <= Qabs x_over_y.

(* Now we've got everything in place to start proving that under the hypotheses
   above, x / y is an integer. *)

(* First we show that z is integral. *)

Lemma z_integral : is_integer (proj1_sig z).
Proof.
  (* It's enough to show that abs(z) >= 2**(r-1). *)
  apply large_floats_are_integral.
  (* Proof strategy:
     2^(q+r-1) <= |x / y|, so
     2^(q+r-1) <= floor |x / y|  (because 2^(q+r-1) is an integer).
     But floor |x / y| <= |z|.
     So 2^(q+r-1) <= |z|. *)
  (* Want to use Qle_trans, with y := ... *)
  assert (twopower ('r-1) <= twopower ('q + 'r - 1))%QPos.
  apply twopower_monotonic_le.
  apply Z.sub_le_mono.
  assert (0 <= 'q)%Z.
  auto with zarith.
  replace ('r)%Z with (0 + 'r)%Z at 1.
  apply Zplus_le_compat_r.
  assumption.
  auto with zarith.
  easy.

  apply Qle_trans with (y := proj1_sig (twopower ('q + 'r - 1))).
  easy.
  clear H.

  apply Qle_trans with (y := inject_Z (floor (Qabs x_over_y))).
  apply floorQ_intro.
  apply is_integer_twopowerQ.
  assert (1 <= 'q)%Z by apply Pos.le_1_l.
  assert (1 <= 'r)%Z by apply Pos.le_1_l.
  auto with zarith.
  easy.
  now apply abs_floor.
Qed.

(* Now we show that both x and y*z are integral multiples of 2^(b+1),
   where b is the binade of y. *)

(* From our assumption that x/y is large, we have:

     2^(q+r-1) <= |x/y|

   and if the binade of x is a and that of y is b, we also have

     |x/y| < 2^(a-b+1).

   hence |y| * 2^(q+r-1) <= |x|,

   taking binades, we get:

     bin(y) + q + r - 1 <= bin(x).

   so 2^(b+q+r-1) <= x,

   and so q+r-1 <= a - b.

   Now x is a multiple of 2^(a-p+1), and

     a - p + 1 >= b + q + r - p

   and since p < q + r, we have

     a - p + 1 >= b + q + r - p > b

   so

     a - p + 1 >= b + 1.

   Step 1: show that q + r - 1 <= a - b.
   Step 2: show that p <= q + r - 1 (from p < q + r).
   Step 3: deduce that p <= a - b, hence that b + 1 <= a - p + 1.
   Step 4: now since x is a multiple of 2^(a - p + 1), it's a multiple
     of 2^(b+1).

   So why is y*z a multiple of 2^(b+1)?  Well, y is a multiple
   of 2^(b+1-q), and z is a multiple of 2^(c+1-r) (where c is
   the binade of z). So y*z is a multiple of 2^(b+c+2-r-q),
   and we have to show that b + 1 <= b + c + 2 - r - q,
   or equivalently that q + r <= c + 1

   We haven't yet used the hypothesis that x/y is large.

   So: let c be the binade of (x / y).  The tricky bit is showing
   that z is a multiple of 2^(c+1-r), which follows from
   binade(x / y) <= binade(z), which in turn follows from
   binade(floor(abs(x/y))) == binade(x/y), along with
   floor(abs(x/y)) <= abs(z).
*)

Lemma a_minus_b_large : ('q + 'r - 1 < a - b + 1)%Z.
Proof.
  apply twopowerQ_injective_lt;
  apply Qle_lt_trans with (1 := x_over_y_large);
  clear c; subst x_over_y;
  rewrite Qabs_div; [ | discharge_positivity_constraints ];
  apply Qlt_le_trans with (y := twopowerQ (a + 1) / twopowerQ b).
  - apply Qlt_le_trans with (y := twopowerQ (a + 1) / Qabs (proj1_sig y)).
    + scale_by (Qabs (proj1_sig y));
      rearrange_goal (Qabs (proj1_sig x) < twopowerQ (a + 1));
      apply (twopowerQ_binadeQ_lt (a + 1) (proj1_sig x) (x_nonzero));
      subst a; omega.
    + pose proof (twopowerQ_positive b);
      pose proof (twopowerQ_positive (a + 1));
      scale_by (twopowerQ b);
      scale_by (Qabs (proj1_sig y));
      scale_by (/ (twopowerQ (a + 1)));
      rearrange_goal (twopowerQ b <= Qabs (proj1_sig y));
  
      apply (twopowerQ_binadeQ_le b (proj1_sig y) (y_nonzero));
      subst b; omega.
  - twopower_right; apply Qle_refl.
Qed.

Lemma a_minus_b_large_le : ('q + 'r - 1 <= a - b)%Z.
Proof.
  apply Zlt_succ_le.
  apply a_minus_b_large.
Qed.


(* Showing that x is a multiple of quantum. *)

Let ulp_x := ulp _ x (x_nonzero).

Lemma x_is_quantized : is_multiple_of quantum (proj1_sig x).
Proof.
  apply is_multiple_of_transitive with (b := ulp_x).
  subst ulp_x.
  subst quantum.
  unfold ulp.
  apply is_multiple_of_twopower.

  assert ('p <= a - b)%Z.
  apply Z.le_trans with (m := ('q + 'r - 1)%Z).
  now apply Z.lt_le_pred.

  apply a_minus_b_large_le.
  replace (binadeQ (proj1_sig x) x_nonzero) with a by easy.
  omega.

  apply is_multiple_of_ulp.
Qed.

(* Showing that z is a multiple of 2^(c - r + 1). *)

(* Problem here is that c is the binade of x/y, not the binade of z.

   Now 2^c <= Qabs (x / y), by definition.
   so 2^c <= floor (Qabs (x / y)).
   so 2^c <= z.  *)

(* Minor annoyance: we have to show that z is nonzero before
   we can compute its binade. *)

Lemma z_nonzero : ~(proj1_sig z == 0).
Proof.
  (* It's enough to show that abs z is positive. *)
  apply Qabs_nonzero_inv.
  (* We show that 0 < 2^(q+r-1) <= floor (x / y) <= |z|. *)
  apply Qlt_le_trans with (y := inject_Z (floor (Qabs x_over_y))).
  replace 0 with (inject_Z 0) by (now compute).
  apply Qlt_le_trans with (y := twopowerQ ('q + 'r - 1)).
  apply twopowerQ_positive.
  apply floorQ_intro.
  apply is_integer_twopowerQ.
  assert (0 < 'q)%Z by easy; assert (0 < 'r)%Z by easy; omega.
  easy.
  now apply abs_floor.
Qed.

Lemma binade_z_large : (c <= binadeQ (proj1_sig z) z_nonzero)%Z.
Proof.
  apply twopowerQ_binadeQ_le.
  apply Qle_trans with (y := inject_Z (floor (Qabs x_over_y))).
  apply floorQ_intro.

  (* Now showing that 2^c is integral. *)
  apply is_integer_twopowerQ.
  subst c.
  apply twopowerQ_binadeQ_le.
  apply Qle_trans with (y := twopowerQ ('q + 'r - 1)).
  apply twopowerQ_monotonic_le.
  assert (0 < 'q)%Z by easy; assert (0 < 'r)%Z by easy; omega.
  easy.

  apply (twopowerQ_binadeQ_le c (x_over_y) x_over_y_nonzero).
  subst c.
  auto with zarith.

  now apply abs_floor.
Qed.

Lemma z_is_multiple_of_ulp_x_over_y :
  is_multiple_of (twopowerQ (c - 'r + 1)) (proj1_sig z).
Proof.
  apply is_multiple_of_transitive with (
    b := twopowerQ (binadeQ (proj1_sig z) z_nonzero - 'r + 1)).
  apply is_multiple_of_twopower.
  assert (c <= binadeQ (proj1_sig z) z_nonzero)%Z by (apply binade_z_large).
  omega.

  apply is_multiple_of_ulp.
Qed.


Lemma yz_is_quantized :
  is_multiple_of quantum (proj1_sig y * proj1_sig z).
Proof.
  apply is_multiple_of_transitive with (
    b := twopowerQ (b - 'q + 1) * twopowerQ (c - 'r + 1)).
  unfold quantum.
  setoid_rewrite <- twopowerQ_mul.
  apply is_multiple_of_twopower.
  (* need that q + r <= c + 1 *)
  assert ('q + 'r - 1 <= c)%Z by (now apply twopowerQ_binadeQ_le).
  omega.

  apply is_multiple_of_product.
  apply is_multiple_of_ulp.
  apply z_is_multiple_of_ulp_x_over_y.
Qed.

Lemma x_minus_yz_is_quantized :
  is_multiple_of quantum ((proj1_sig x) - (proj1_sig y)*(proj1_sig z)).
Proof.
  apply is_multiple_of_sub.
  apply x_is_quantized.
  apply yz_is_quantized.
Qed.

(* Okay, great: now we know that x - y*z is a multiple of 2^(b+1).
   Next we show that |x - y*z| < 2^(b+1), and then go on to deduce
   that x == y*z.

   But |x/y - z| < 1, so |x - y*z| < |y| < 2^(b+1).  Done! *)

Lemma x_is_yz : proj1_sig y * proj1_sig z == proj1_sig x.
Proof.
  apply Qplus_inj_r with (z := -(proj1_sig y * proj1_sig z)).
  ring_simplify.
  setoid_replace ((-1 # 1) * proj1_sig y * proj1_sig z + proj1_sig x) with
    (proj1_sig x - proj1_sig y * proj1_sig z) by ring.
  symmetry.
  apply small_multiple_is_zero with (m := quantum).
  apply x_minus_yz_is_quantized.
  apply x_minus_yz_small.
Qed.


Theorem first_separation_theorem : x_over_y == proj1_sig z.
Proof.
  unfold x_over_y.
  scale_by (proj1_sig y).
  pose proof x_is_yz.
  rearrange.
Qed.


Lemma x_over_y_integral : is_integer x_over_y.
Proof.
  rewrite first_separation_theorem.
  apply z_integral.
Qed.

End FirstSeparationTheorem.

Section SecondSeparationTheorem.

(* The second separation theorem applies to the case where p >= q + r. *)

Hypothesis p_large : ('q + 'r <= 'p)%Z.

Hypothesis x_over_y_large : ('p <= a - b)%Z.

(* Could be moved earlier: doesn't require p_large or x_over_y_large. *)

Lemma a_small : (a - b - 1 <= c)%Z.
Proof.
  subst a b c; unfold binadeQ;
  remember (
    exist (fun x0 : Q => (0 < x0)%Q) (Qabs x_over_y)
    (Qabs_nonzero x_over_y x_over_y_nonzero)
  ) as x_over_y_pos;
  remember (
    exist (fun x0 : Q => (0 < x0)%Q) (Qabs (proj1_sig x))
    (Qabs_nonzero (proj1_sig x) x_nonzero)) as x_pos;
  remember (
    exist (fun x0 : Q => (0 < x0)%Q) (Qabs (proj1_sig y))
    (Qabs_nonzero (proj1_sig y) y_nonzero)) as y_pos;
  assert (x_over_y_pos == x_pos / y_pos)%QPos as H by (
    unfold QPos.eq; rewrite Heqx_pos, Heqy_pos, Heqx_over_y_pos;
    setoid_rewrite Qabs_div; easy); rewrite H; apply binade_div.
Qed.


Lemma z_large2 : twopowerQ c <= Qabs (proj1_sig z).
Proof.
  apply Qle_trans with (y := floorQ (Qabs x_over_y)).
  apply floorQ_intro.
  apply is_integer_twopowerQ.
  apply Z.le_trans with (m := ('p - 1)%Z).
  assert (0 < 'p)%Z by easy; omega.
  pose proof a_small; omega.
  apply (twopowerQ_binadeQ_le c x_over_y x_over_y_nonzero).
  apply Zle_refl.
  now apply abs_floor.
Qed.


Lemma z_nonzero2 : ~ proj1_sig z == 0.
Proof.
  apply Qabs_nonzero_inv.
  apply Qlt_le_trans with (y := twopowerQ c).
  apply twopowerQ_positive.
  apply z_large2.
Qed.


Lemma binade_z_large2 : (c <= binadeQ (proj1_sig z) z_nonzero2)%Z.
Proof.
  apply twopowerQ_binadeQ_le.
  apply z_large2.
Qed.


Lemma z_integral2 : is_integer (proj1_sig z).
Proof.
  apply (large_representable_is_integer r); try (now destruct z);
  apply (twopowerQ_binadeQ_le ('r - 1) (proj1_sig z) (z_nonzero2));
  apply Z.le_trans with (2 := binade_z_large2);
  pose proof a_small; assert (0 < 'q)%Z by easy; omega.
Qed.

Lemma x_is_quantized2 : is_multiple_of quantum (proj1_sig x).
Proof.
  apply is_multiple_of_transitive with (b := twopowerQ (a - 'p + 1)).
  apply is_multiple_of_twopower; omega.
  apply is_multiple_of_ulp.
Qed.


Lemma yz_is_quantized2 : is_multiple_of quantum (proj1_sig y * proj1_sig z).
Proof.
  apply is_multiple_of_transitive with (b := twopowerQ ((b - 'q + 1) + (
    c - 'r + 1))).
  apply is_multiple_of_twopower; pose proof a_small; omega.
  rewrite twopowerQ_mul.
  apply is_multiple_of_product.
  apply is_multiple_of_ulp.
  apply is_multiple_of_transitive with (
    b := twopowerQ (binadeQ (proj1_sig z) z_nonzero2 - 'r + 1)).
  apply is_multiple_of_twopower.
  pose proof binade_z_large2. omega.
  apply is_multiple_of_ulp.
Qed.

Lemma x_minus_yz_is_quantized2 :
  is_multiple_of quantum ((proj1_sig x) - (proj1_sig y)*(proj1_sig z)).
Proof.
  apply is_multiple_of_sub.
  apply x_is_quantized2.
  apply yz_is_quantized2.
Qed.

Lemma x_is_yz2 : proj1_sig y * proj1_sig z == proj1_sig x.
Proof.
  apply Qplus_inj_r with (z := -(proj1_sig y * proj1_sig z)).
  ring_simplify.
  setoid_replace ((-1 # 1) * proj1_sig y * proj1_sig z + proj1_sig x) with
    (proj1_sig x - proj1_sig y * proj1_sig z) by ring.
  symmetry.
  apply small_multiple_is_zero with (m := quantum).
  apply x_minus_yz_is_quantized2.
  apply x_minus_yz_small.
Qed.

Theorem second_separation_theorem : x_over_y == proj1_sig z.
Proof.
  unfold x_over_y.
  scale_by (proj1_sig y).
  pose proof x_is_yz2.
  rearrange.
Qed.

Theorem x_over_y_integral2 : is_integer x_over_y.
Proof.
  rewrite second_separation_theorem.
  apply z_integral2.
Qed.

End SecondSeparationTheorem.

End SeparationTheorems.