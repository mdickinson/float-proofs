(* XXX To do: define floorQ as the composition of inject_Z and floor, and
   use it everywhere.  Similarly for ceilingQ. *)

(* Define subsets of the rationals representable as binary floats
   with various precisions. *)

Require Import QArith.
Require Import Qabs.

Require Import qpos.
Require Import floor_and_ceiling.
Require Import twopower.

Open Scope Q.

(* Some remedial lemmas. *)

Lemma pos_lt_Z_lt (p q : positive) : (p < q)%positive  ->  ('p < 'q)%Z.
Proof.
  easy.
Qed.

Lemma lt_sum_is_diff_lt (a b c : Q) : a < b + c  <->  a - c < b.
Proof.
  split; intro.

  apply Qplus_lt_r with (z := c).
  setoid_replace (c + (a - c)) with a by ring.
  setoid_replace (c + b) with (b + c) by ring.
  easy.

  apply Qplus_lt_r with (z := -c).
  setoid_replace (-c + a) with (a - c) by ring.
  setoid_replace (-c + (b + c)) with b by ring.
  easy.
Qed.
  
(* Want that a < b + c  <->  a - b < c. *)
Definition nonzero (x : Q) := ~(0 == x).

Lemma nonzero_div (x y : Q) : nonzero x -> nonzero y -> nonzero (x / y).
Proof.
  intros.
  intro.
  apply H.
  setoid_replace x with (x / y * y).
  setoid_rewrite <- H1.
  field.
  field.
  intro.
  apply H0.
  easy.
Qed.

  
Lemma nonzero_qpos (q : QPos) : nonzero (proj1_sig q).
Proof.
  destruct q; simpl.
  intro. rewrite <- H in q.
  revert q.
  compute. easy.
Qed.

  
Lemma Qdiv_mul (a b c : Q) :
  (~ 0 == b) ->  (a / b == c  <->  a == c * b).
Proof.
  intro; split; intro.

  setoid_replace a with (a / b * b).
  now rewrite H0.
  rewrite Qmult_comm; rewrite Qmult_div_r.
  easy.
  now contradict H.

  setoid_replace c with (c * b / b).
  now rewrite H0.
  rewrite Qdiv_mult_l.
  easy.
  now contradict H.
Qed.

Lemma Qabs_zero (x : Q) : 0 == Qabs x  ->  0 == x.
Proof.
  apply Qabs_case.
    easy.
    intros; setoid_replace x with (- - x) by (now rewrite Qopp_opp);
    now rewrite <- H0.
Qed.

Lemma Qabs_div (a b : Q) :
  (~ 0 == b) -> Qabs (a / b) == Qabs a / Qabs b.
Proof.
  intro.
  setoid_replace (Qabs a) with (Qabs (a / b) * Qabs b).

  rewrite Qdiv_mult_l.
  easy.
  contradict H; now apply Qabs_zero.

  rewrite <- Qabs_Qmult; rewrite Qmult_comm; rewrite Qmult_div_r;
    auto with qarith.
Qed.

Lemma Qdiv_lt_le (a b c d : Q) :
  0 < a  ->  0 < c  ->
  a < b  ->  c <= d  ->  a / d < b / c.
Proof.
  intros.
  assert (0 < d) by (apply Qlt_le_trans with (y := c); assumption).
  assert (0 < b) by (apply Qlt_trans with (y := a); assumption).

  apply Qmult_lt_r with (z := c * d).
  apply Q_mul_pos_pos; assumption.

  setoid_replace (a / d * (c * d)) with (a * c) by field.
  setoid_replace (b / c * (c * d)) with (b * d) by field.

  apply Qlt_le_trans with (y := b * c).
  apply Qmult_lt_r; assumption.
  apply Qmult_le_l; assumption.
  auto with qarith.
  auto with qarith.
Qed.


Definition twopowerQ (x : Z): Q := proj1_sig (twopower x).

Lemma twopowerQ_positive (p : Z) : 0 < twopowerQ p.
Proof.
  unfold twopowerQ; now destruct (twopower p).
Qed.

Lemma twopowerQ_monotonic_le (p q : Z) :
  (p <= q)%Z  ->  twopowerQ p <= twopowerQ q.
Proof.
  apply twopower_monotonic_le.
Qed.


Lemma twopowerQ_injective_le (p q : Z) :
  twopowerQ p <= twopowerQ q  ->  (p <= q)%Z.
Proof.
  apply twopower_injective_le.
Qed.


Lemma twopowerQ_injective_lt (p q : Z) :
  twopowerQ p < twopowerQ q  ->  (p < q)%Z.
Proof.
  apply twopower_injective_lt.
Qed.


Definition representable_in_precision (p : positive) (x : Q) :=
  exists (m : Z) (e : Z),
    (x == (inject_Z m) * proj1_sig (twopower e)) /\
    (Zabs m < 2 ^ 'p)%Z.

(* Relationship between 2^ and twopower. *)

Lemma twopowerQ_twopower_nonneg (m : Z) :
  (0 <= m)%Z  ->  twopowerQ m == inject_Z (2 ^ m).
Proof.
  unfold twopowerQ. simpl. intro.
  symmetry.
  now apply Qpower.Zpower_Qpower.
Qed.


Lemma small_integer_is_zero (x : Q) :
  is_integer x -> Qabs x < 1 -> 0 == x.
Proof.
  intro.
  apply Qabs_case; intros.

  setoid_replace x with (inject_Z (floor x)) by (symmetry; now apply floor_integer).
  apply inject_Z_injective.
  rewrite floor_spec_alt. auto.

  setoid_replace x with (inject_Z (ceiling x)) by (symmetry; now apply ceiling_integer).
  apply inject_Z_injective.
  rewrite ceiling_spec_alt.
  setoid_replace (inject_Z 0 - 1) with (- (1)) by ring.
  assert (-(1) < x) by (now apply Qneg_le).
  auto.
Qed.  

  
Lemma is_integer_twopower (x : Z) :
  (0 <= x)%Z -> is_integer (proj1_sig (twopower x)).
Proof.
  intro; simpl.
  rewrite <- Qpower.Zpower_Qpower.
  apply is_integer_inject_Z. easy.
Qed.

(* Now we can define the subsets of binary floats of various precisions. *)
Definition binary_float (p : positive) :=
  { x : Q | representable_in_precision p x}. 

(* Large binary floats are integral: a precision-p float that's
   larger than 2**(p-1) must be an integer. *)

Lemma Qabs_Zabs (x : Z) : Qabs (inject_Z x) == inject_Z (Z.abs x).
Proof.
  now unfold Qabs.
Qed.

Lemma Qabs_twopower (x : Z) : Qabs (proj1_sig (twopower x)) == proj1_sig (twopower x).
Proof.
  apply Qabs_pos.
  destruct (twopower x). simpl. auto with qarith.
Qed.

(* for any integers x and y and rational number q, 2^x <= q * 2^y   ->  2^(x - y) <= q *)

Lemma twopowerQ_mul (x y : Z) :
  twopowerQ x * twopowerQ y == twopowerQ (x + y).
Proof.
  unfold twopowerQ; simpl; now rewrite Qpower.Qpower_plus.
Qed.

Lemma twopower_lr (x y : Z) (q : Q) :
  twopowerQ x <= q * twopowerQ y  ->  twopowerQ (x - y) <= q.
Proof.
  unfold twopowerQ.
  (* multiply both sides by 2^y on the right using Qmult_le_r. *)
  (*      : forall x y z : Q, 0 < z -> (x * z <= y * z <-> x <= y) *)
  intro.
  apply Qmult_le_r with (z := proj1_sig (twopower y)).
  (* Now trying to show that 0 < proj1_sig (...), but that
     should be immediate. *)
  destruct (twopower y). easy.
  replace (proj1_sig (twopower y)) with (twopowerQ y).
  replace (proj1_sig (twopower (x - y))) with (twopowerQ (x - y)).
  replace (proj1_sig (twopower y)) with (twopowerQ y) in H.
  replace (proj1_sig (twopower x)) with (twopowerQ x) in H.
  assert (twopowerQ (x - y) * twopowerQ y == twopowerQ x).

  assert (twopowerQ (x - y) * twopowerQ y == twopowerQ ((x - y) + y)).
  apply twopowerQ_mul.
  rewrite H0.
  assert (x - y + y = x)%Z.
  auto with zarith.
  rewrite H1. easy.
  rewrite H0. easy.
  easy.
  easy.
  easy.
  easy.
Qed.
  
Lemma rhs_negative_lt (x y : Q) : x < -y -> y < -x.
Proof.
  intro.
  setoid_replace y with (- - y).
  now rewrite <- Qopp_lt_mono.
  symmetry.
  apply Qopp_opp.
Qed.

Lemma abs_nonzero (x : Q) : ~(0 == x)  -> 0 < Qabs x.
Proof.
  apply Qabs_case; intros.
  now apply Qle_not_eq.

  apply rhs_negative_lt.
  setoid_replace (-0) with 0.
  apply Qle_not_eq. easy. contradict H0. now symmetry.

  unfold Qopp.
  simpl.
  easy.
Qed.

Lemma abs_nonzero_inv (x : Q) : 0 < Qabs x -> nonzero x.
Proof.
  apply Qabs_case; intros; intro; now rewrite <- H1 in H0.
Qed.


Definition binadeQ (x : Q) (x_nonzero : ~(0 == x)) : Z.
  refine (binade (exist _ (Qabs x) _)).
  now apply abs_nonzero.
Defined.

(*
   ulp of a nonzero float x at precision p is 2**(binade x - p + 1).

   if x = m * 2**e with 2**(p-1) <= m < 2**p, then

   2**(p-1+e) <= x < 2**(p+e), so binade(x) = p-1+e.
   so e = binade(x) - p + 1.
*)


(* Analog of the binade-twopower adjunction results. *)

Lemma twopowerQ_binadeQ_le (n : Z) (q : Q) (q_nonzero : nonzero q) :
  twopowerQ n <= Qabs q  <->  (n <= binadeQ q q_nonzero)%Z.
Proof.
  unfold twopowerQ, binadeQ; now rewrite <- twopower_binade_le.
Qed.

Lemma twopowerQ_binadeQ_lt (n : Z) (q : Q) (q_nonzero: nonzero q) :
  (binadeQ q q_nonzero < n)%Z  <->  Qabs q < twopowerQ n.
Proof.
  unfold twopowerQ, binadeQ; now rewrite <- twopower_binade_lt.
Qed.

Definition ulp p (x : binary_float p) (x_nonzero : ~(0 == proj1_sig x)) : Q :=
  twopowerQ (binadeQ (proj1_sig x) x_nonzero - 'p + 1).

Definition is_multiple_of (y x : Q) :=
  exists (m : Q), is_integer m  /\  x == m * y.

Add Morphism is_multiple_of : is_multiple_of_morphism.
  intros.
  unfold is_multiple_of.
  split; intro.
  destruct H1. exists x1. split. easy. rewrite <- H0. rewrite <- H. easy.
  destruct H1. exists x1. split. easy. rewrite H0. rewrite H. easy.
Qed.

Lemma is_multiple_of_additive (m a b : Q) :
  is_multiple_of m a -> is_multiple_of m b -> is_multiple_of m (a + b).
Proof.
  unfold is_multiple_of.
  intros.
  destruct H.
  destruct H0.
  exists (x + x0).
  split.
  now apply is_integer_add.
  destruct H.
  destruct H0.
  rewrite H1.
  rewrite H2.
  symmetry.
  apply Qmult_plus_distr_l.
Qed.

Lemma is_multiple_of_neg (m a : Q) :
  is_multiple_of m a -> is_multiple_of m (-a).
Proof.
  unfold is_multiple_of; intro.
  destruct H. destruct H.
  exists (-x).
  split.
  now apply is_integer_neg.
  rewrite H0.
  ring.
Qed.
  

Lemma is_multiple_of_abs (m a : Q) :
  is_multiple_of m a -> is_multiple_of m (Qabs a).
Proof.
  apply Qabs_case; intros; [ easy | now apply is_multiple_of_neg].
Qed.
  
Lemma is_multiple_of_sub (m a b : Q) :
  is_multiple_of m a -> is_multiple_of m b -> is_multiple_of m (a - b).
Proof.
  intros; apply is_multiple_of_additive; [ | apply is_multiple_of_neg]; easy.
Qed.

Lemma is_multiple_of_product (a b c d : Q):
  is_multiple_of a b -> is_multiple_of c d -> is_multiple_of (a*c) (b*d).
Proof.
  intros a_divides_b c_divides_d.
  destruct a_divides_b as [m a_divides_b].
  destruct c_divides_d as [n c_divides_d].
  exists (m*n).
  split.
  now apply is_integer_mul.
  rewrite (proj2 a_divides_b).
  rewrite (proj2 c_divides_d).
  ring.
Qed.
  

Lemma is_multiple_of_transitive (a b c : Q):
  is_multiple_of a b -> is_multiple_of b c -> is_multiple_of a c.
Proof.
  unfold is_multiple_of; intros ab bc; destruct ab as [m Hab];
  destruct bc as [n Hbc]; exists (n * m); split.
    now apply is_integer_mul.
    rewrite (proj2 Hbc); rewrite (proj2 Hab); ring.
Qed.


Lemma small_multiple_is_zero (m a : Q) :
  is_multiple_of m a  ->  Qabs a < m  ->  a == 0.
Proof.
  unfold is_multiple_of.
  intros a_multiple a_bounded.
  assert (0 < m) as m_positive by (apply Qle_lt_trans with (y := Qabs a); [apply Qabs_nonneg | easy]).
  
  assert (Qabs m == m) as m_positive2 by (apply Qabs_pos; now apply Qlt_le_weak).

  assert (~ m == 0) as m_nonzero.
  intro. rewrite H in m_positive.
  revert m_positive. easy.

  destruct a_multiple as [x is_multiple].
  destruct is_multiple as [x_is_integer a_is_xm].
  rewrite a_is_xm.

  cut (x == 0).
  intro x_zero. rewrite x_zero. ring.

  assert (x == a / m) as x_is_a_by_m.
  rewrite a_is_xm.
  field. easy.

  assert (Qabs x < 1).
  rewrite x_is_a_by_m.
  rewrite Qabs_div.
  apply Qlt_shift_div_r.
  now rewrite m_positive2.

  rewrite m_positive2.
  now ring_simplify.

  now contradict m_nonzero.
  symmetry.
  now apply small_integer_is_zero.
Qed.


Lemma is_multiple_of_twopower (m n : Z) :
  (m <= n)%Z  ->  is_multiple_of (twopowerQ m) (twopowerQ n).
Proof.
  unfold is_multiple_of.
  exists (twopowerQ (n - m)).
  split.
  apply is_integer_twopower.
  omega.
  rewrite twopowerQ_mul.
  now replace (n - m + m)%Z with n by ring.
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
  (x_nonzero : nonzero x) (y : Q) (y_nonzero: nonzero y) :
  y == twopowerQ e * x  ->  (binadeQ y y_nonzero = e + binadeQ x x_nonzero)%Z.
Proof.
  intro H.
  unfold binadeQ.
  set (xpos := exist _ (Qabs x) (abs_nonzero x x_nonzero)).
  set (ypos := exist _ (Qabs y) (abs_nonzero y y_nonzero)).

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


Lemma is_multiple_of_ulp p (x : binary_float p)
  (x_nonzero : ~(0 == proj1_sig x)) :
    is_multiple_of (ulp _ x x_nonzero) (proj1_sig x).
Proof.
  unfold ulp.
  unfold is_multiple_of.
  unfold binary_float in x.
  destruct x. simpl.
  simpl in x_nonzero.
  unfold representable_in_precision in r.
  destruct r as [m H0].
  destruct H0 as [e H1].
  destruct H1 as [x_is_m_2e m_is_small].

  (* We now have that x = m * 2^e, with |m| < 2^p,
     and we must show that x = m0 * 2^(binade(x) - p + 1)
     for some integer m0.  It's therefore enough to show
     that e >= binade(x) - p + 1.

     And that follows from:
        binade(x) == binade(m) + e, and
        binade(m) <= p - 1.
  *)

  assert(m_nonzero : nonzero (inject_Z m)).
  unfold nonzero.
  intro.
  rewrite <- H in x_is_m_2e.
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
  apply is_integer_twopower.

  assert (binadeQ (inject_Z m) m_nonzero < 'p)%Z.
  unfold binadeQ.
  set (mpos := exist _ (Qabs (inject_Z m)) (abs_nonzero (inject_Z m) m_nonzero)).
  apply twopower_binade_lt.

  assert (Qabs (inject_Z m) < twopowerQ ('p)).
  rewrite Qabs_Zabs.

  rewrite twopowerQ_twopower_nonneg.
  now rewrite <- Zlt_Qlt.
  easy.
  
  unfold QPos.lt.
  assert (proj1_sig mpos == Qabs (inject_Z m)).
  easy.
  rewrite H1.
  assumption.
  
  (* Current goal should follow from H0 by simple arithmetic. *)
  omega.

  rewrite <- Qmult_assoc.
  rewrite twopowerQ_mul.
  replace ('p - 1 - binadeQ (inject_Z m) m_nonzero + (binadeQ (inject_Z m) m_nonzero + e - 'p + 1))%Z with e by ring.
  reflexivity.
Qed.


Lemma large_floats_are_integral (p : positive) (x : binary_float p) :
  let y := proj1_sig x in
  proj1_sig (twopower ('p - 1)) <= Qabs y  ->  is_integer y.
Proof.
  (* How to prove? x is a float, so it's of the form m * 2**e for some m and e
     with m < 2^p.  It's enough to show that e >= 0.  But if e < 0 then

       abs(x) < 2^(p+e) <= 2^(p-1)
     which contradicts our assumptions.
  *)
  intro.
  destruct x.
  simpl in y.
  assert (x == y).
  easy.
  rewrite <- H.
  clear H.
  clear y.
  (* The above mess just got us out of binary_float land.  Now we
     have a proposition to prove in Q / Qpos. *)
  unfold representable_in_precision in r.
  destruct r.
  destruct H.
  destruct H.
  (* Main aim now is to prove that x1 is nonnegative, so that (inject 2)^x1 is integral. *)
  intro.
  rewrite H in H1.
  rewrite H.
  apply is_integer_mul.
  apply is_integer_inject_Z.
  apply is_integer_twopower.
  (* Now all we have to do is show that 0 <= x1. *)
  (* We're given that 2^(p-1) <= abs (x0 * 2^x1),
     and that x0 < 2^p, hence that
     2^(p-1) < 2^p * 2^x1.
     It follows that p - 1 < (p + x1), and hence that -1 < x1, or 0 <= x1.
     *)
  rewrite Qabs_Qmult in H1.
  rewrite Qabs_Zabs in H1.
  rewrite Qabs_twopower in H1.
  (* Now we've got a statement of the form 2^e <= m * 2^f, and
     we want to turn it into a statement of the form 2^(e-f) <= m. *)
  
  assert (-1 < x1)%Z.

  assert (twopowerQ (' p - 1 - x1) <= inject_Z (Z.abs x0)).
  apply twopower_lr. easy.

  assert (inject_Z (Z.abs x0) < twopowerQ ('p)).
  unfold twopowerQ.

  assert (inject_Z (Z.abs x0) < inject_Z (2 ^ 'p)).
  now rewrite <- Zlt_Qlt.
  assert (inject_Z (2^ 'p) == proj1_sig (twopower (' p))).

  assert (inject_Z (Z.abs x0) < inject_Z (2 ^ 'p)).
  now rewrite <- Zlt_Qlt.
  assert (inject_Z (2^ 'p) == proj1_sig (twopower (' p))).

  rewrite Qpower.Zpower_Qpower.
  
  easy.
  easy.
  easy.
  rewrite <- H4.
  easy.

  assert (twopowerQ ('p - 1 - x1) < twopowerQ ('p)).
  now apply Qle_lt_trans with (y := inject_Z (Z.abs x0)).
  
  assert ('p - 1 - x1 < ' p)%Z.
  now apply twopower_injective_lt.
  auto with zarith.
  auto with zarith.
Qed.


Lemma le_floor (x y : Q) :
  x <= y  ->
  is_integer x ->
  x <= inject_Z (floor y).
Proof.
  intro x_le_y.
  unfold is_integer.
  intro.
  destruct H.
  rewrite <- H.
  rewrite <- Zle_Qle.
  apply floor_spec.
  rewrite H. easy.
Qed.


Lemma rhs_negative_le (x y : Q) : x <= -y -> y <= -x.
Proof.
  intro.
  setoid_replace y with (- - y).
  now rewrite <- Qopp_le_mono.
  symmetry. auto with qarith.
  apply Qopp_opp.
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
  apply rhs_negative_le.
  rewrite <- inject_Z_opp.
  rewrite neg_floor_is_ceiling_neg.
  setoid_replace (- - x) with x.
  easy.
  apply Qopp_involutive.
Qed.
  
Section FloorDivision.

(* Let's try to prove a theorem. *)

(* We start with x, y and z floating-point numbers of precisions p, q and r
   respectively. *)

Variables p q r : positive.
Variable x : binary_float p.
Variable y : binary_float q.
Variable z : binary_float r.

(* Next, we assume that x and y are nonzero and that floor(x/y) <= z <= ceiling(x/y). *)

Hypothesis x_nonzero : ~ 0 == proj1_sig x.
Hypothesis y_nonzero : ~ 0 == proj1_sig y.

Let x_over_y := proj1_sig x / proj1_sig y.

Hypothesis z_bounds : inject_Z (floor x_over_y) <= proj1_sig z <= inject_Z (ceiling x_over_y).

(* Let's take just one of the cases of the theorem, the case where p < q + r
   and abs(x / y) >= twopower (q + r - 1). *)

Hypothesis p_small : (p < q + r)%positive.

Hypothesis x_over_y_large :
  twopowerQ ('q + 'r - 1) <= Qabs x_over_y.

(* Now we've got everything in place to start proving that under the hypotheses above,
   x / y is an integer. *)

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
  replace ('r) with (0 + 'r)%Z at 1.
  apply Zplus_le_compat_r.
  assumption.
  auto with zarith.
  easy.

  apply Qle_trans with (y := proj1_sig (twopower ('q + 'r - 1))).
  easy.
  clear H.

  apply Qle_trans with (y := inject_Z (floor (Qabs x_over_y))).
  apply le_floor. easy.
  apply is_integer_twopower.
  assert (1 <= 'q)%Z.
  apply Pos.le_1_l.
  assert (1 <= 'r)%Z by apply Pos.le_1_l.
  auto with zarith.
  apply abs_floor. easy.
Qed.

(* Now we show that both x and y*z are integral multiples of 2^(b+1),
   where b is the binade of y. *)

Lemma x_over_y_nonzero : nonzero x_over_y.
Proof.
  now apply nonzero_div.
Qed.
  

Let a := binadeQ (proj1_sig x) x_nonzero.
Let b := binadeQ (proj1_sig y) y_nonzero.
Let c := binadeQ x_over_y x_over_y_nonzero.

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
  apply twopowerQ_injective_lt.
  apply Qle_lt_trans with (y := Qabs x_over_y).
  assumption.
  clear c.
  subst x_over_y.
  rewrite Qabs_div.

  apply Qlt_le_trans with (y := twopowerQ (a + 1) / twopowerQ b).
  apply Qdiv_lt_le.

  apply Qabs_case.
  apply nonzero_and_nonneg_implies_positive.
  intro. apply x_nonzero. symmetry. easy.
  intro. assert (0 <= -proj1_sig x).
  apply Qopp_le_mono.
  setoid_replace (- - proj1_sig x) with (proj1_sig x) by field.
  setoid_replace (- 0) with 0 by easy.
  easy.
  apply nonzero_and_nonneg_implies_positive.
  intro.
  apply x_nonzero.
  setoid_replace (proj1_sig x) with (- - proj1_sig x) by field.
  now rewrite H1.
  easy.
  unfold twopowerQ.
  destruct (twopower b). simpl. easy.

  apply (twopowerQ_binadeQ_lt (a + 1) (proj1_sig x) (x_nonzero)).
  subst a. omega.

  apply (twopowerQ_binadeQ_le b (proj1_sig y) (y_nonzero)).
  subst b. omega.

  apply Qle_shift_div_r.

  apply twopowerQ_positive.
  rewrite twopowerQ_mul.
  apply twopowerQ_monotonic_le.
  omega.

  easy.
Qed.

Lemma a_minus_b_large_le : ('q + 'r - 1 <= a - b)%Z.
Proof.
  apply Zlt_succ_le.
  apply a_minus_b_large.
Qed.


(* We'll show that x and y*z are both multiples of quantum. *)

Let quantum := twopowerQ (b + 1).

Let ulp_x := ulp _ x (x_nonzero).

(* Showing that x is a multiple of quantum. *)

Lemma x_is_quantized : is_multiple_of quantum (proj1_sig x).
Proof.
  apply is_multiple_of_transitive with (b := ulp_x).
  subst ulp_x.
  subst quantum.
  unfold ulp.
  apply is_multiple_of_twopower.

  assert ('p <= a - b)%Z.
  apply Z.le_trans with (m := ('q + 'r - 1)%Z).
  apply Z.lt_le_pred.
  rewrite <- Pos2Z.inj_add.

  now apply pos_lt_Z_lt.
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

Lemma z_nonzero : nonzero (proj1_sig z).
Proof.
  (* It's enough to show that abs z is positive. *)
  apply abs_nonzero_inv.
  (* We show that 0 < 2^(q+r-1) <= floor (x / y) <= |z|. *)
  apply Qlt_le_trans with (y := inject_Z (floor (Qabs x_over_y))).
  replace 0 with (inject_Z 0) by (now compute).
  apply Qlt_le_trans with (y := twopowerQ ('q + 'r - 1)).
  apply twopowerQ_positive.
  apply le_floor.
  assumption.
  apply is_integer_twopower.
  assert (0 < 'q)%Z by easy; assert (0 < 'r)%Z by easy; omega.
  now apply abs_floor.
Qed.

Lemma binade_z_large : (c <= binadeQ (proj1_sig z) z_nonzero)%Z.
Proof.
  apply twopowerQ_binadeQ_le.
  apply Qle_trans with (y := inject_Z (floor (Qabs x_over_y))).
  apply le_floor.

  apply (twopowerQ_binadeQ_le c (x_over_y) x_over_y_nonzero).
  subst c.
  auto with zarith.

  (* Now showing that 2^c is integral. *)
  apply is_integer_twopower.
  
  subst c.
  apply twopowerQ_binadeQ_le.
  apply Qle_trans with (y := twopowerQ ('q + 'r - 1)).
  apply twopowerQ_monotonic_le.
  assert (0 < 'q)%Z by easy; assert (0 < 'r)%Z by easy; omega.
  assumption.
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
  setoid_rewrite twopowerQ_mul.
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

Lemma x_over_y_minus_z_small : Qabs (x_over_y - proj1_sig z) < 1.
Proof.
  (* Split: show x/y - z < 1 and z - x/y < 1. *)
  apply Qabs_case; intro.

  (* To show: x/y - z < 1. *)
  apply lt_sum_is_diff_lt.
  rewrite Qplus_comm.
  apply lt_sum_is_diff_lt.
  apply Qlt_le_trans with (y := inject_Z (floor x_over_y)).
  apply lt_sum_is_diff_lt.
  now apply floor_spec_alt.
  apply z_bounds.

  setoid_replace (-(x_over_y - proj1_sig z)) with (proj1_sig z - x_over_y) by ring.
  apply lt_sum_is_diff_lt.
  apply Qle_lt_trans with (y := inject_Z (ceiling x_over_y)).
  apply z_bounds.
  rewrite Qplus_comm.
  apply lt_sum_is_diff_lt.
  now apply ceiling_spec_alt.
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
  intro. apply y_nonzero. easy.
  assumption.
  intro. apply y_nonzero. apply Qabs_zero. easy.
  intro. apply y_nonzero. apply Qabs_zero. easy.
  apply Qinv_lt_0_compat.
  apply abs_nonzero.
  assumption.

  subst quantum.
  apply (twopowerQ_binadeQ_lt (b + 1) (proj1_sig y) (y_nonzero)).
  subst b.
  omega.
Qed.


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


Lemma z_is_x_over_y : x_over_y == proj1_sig z.
Proof.
  unfold x_over_y.
  apply Qdiv_mul.
  easy.
  rewrite Qmult_comm.
  now rewrite x_is_yz.
Qed.


Lemma x_over_y_integral : is_integer x_over_y.
Proof.
  rewrite z_is_x_over_y.
  apply z_integral.
Qed.

End FloorDivision.

Check x_over_y_integral.