Require Import QArith.
Require Import Qpower.
Require Import QOrderedType.

Require Import floor_and_ceiling.
Require Import remedial.
Require Import rearrange_tactic.
(* Require Import qpos. *)
Require Import interval.

Local Open Scope Q.

Lemma Qpower_nonzero_nonzero : forall (q : Q) (n : Z), ~(0 == q) -> ~(0 == q^n).
Proof.
  intros q n q_nonzero qn_zero; now assert (0 == 1) by (
  setoid_replace 1 with ((q * (/q))^n) by
  (rewrite Qmult_inv_r by (now apply QOrder.neq_sym); now rewrite Qpower_1);
  rewrite Qmult_power, <- qn_zero; auto with qarith).
Qed.

Lemma Qpower_pos_pos : forall (q : Q) (n : Z), 0 < q -> 0 < q^n.
Proof.
  intros q n q_pos; apply QOrder.le_neq_lt;
  [apply Qpower_pos | apply Qpower_nonzero_nonzero]; auto with qarith.
Qed.

Lemma power_lower_bound (b : Q) (m : Z) :
  1 < b -> (0 <= m)%Z ->
  (1 + inject_Z m * (b - 1)) <= b^m.
Proof.
  (* Proof by induction on m. *)
  intros b_large; revert m; apply natlike_ind.
  - (* Base case. *)
    now ring_simplify.
  - (* Induction step. *)
    intros m m_pos IH.
    (* Showing that 1 + (m + 1) * (b - 1) <= b ^ (m + 1).
       But this follows because

        b ^ (m + 1) = (1 + (b - 1)) * b^m
                    >= 1 + (b - 1)) * (1 + m (b - 1) by the IH
                    = 1 + (b - 1) + m(b - 1) + positive
                    >= 1 + (b - 1) + m (b - 1)
                     = 1 + (m + 1)(b - 1).

     *)
    apply Qle_trans with (y := b * (1 + inject_Z m * (b - 1))).
    + unfold Z.succ. rewrite inject_Z_plus.
      setoid_replace (inject_Z 1) with 1 by ring.
      setoid_replace b with (1 + (b - 1)) at 2 by ring.
      remember (b - 1) as c.
      ring_simplify.
      rearrange_goal (0 <= inject_Z m * c^2).
      apply Qmult_le_0_compat.
      auto with zarith qarith.
      apply Qpower.Qsqr_nonneg.
    + setoid_replace (b ^ (Z.succ m)) with (b * (b ^ m)).
      apply Qmult_le_l.
      now apply Qlt_trans with (y := 1).
      easy.
      unfold Z.succ.
      rewrite Qpower.Qpower_plus.
      ring.
      assert (0 < b).
      now apply Qlt_trans with (y := 1).
      auto with qarith.
Qed.

Lemma power_arbitrarily_large b : 1 < b -> forall c, exists m, c < b^m.
Proof.
  intros b_large c.
  - (* If c < 1, m = 0 will do. *)
    destruct (Qlt_le_dec c 1).
    + (* Case c < 1. *) exists (0%Z); easy.
    + (* Case 1 <= c. *)
      assert (exists m, (0 <= m)%Z /\ c < 1 + inject_Z m * (b - 1)).
      * exists (1 + floor ((c - 1) / (b - 1)))%Z.
        split.
        replace (0%Z) with (1 + (-1))%Z by ring.
        apply Z.add_le_mono_l.
        apply Z.le_trans with (m := (0%Z)).
        easy.
        apply floor_spec.
        apply Qmult_le_div.
        rearrange.
        ring_simplify.
        rearrange.
        rearrange_goal (c - 1 <
                        inject_Z (1 + floor ((c - 1) / (b - 1))) * (b - 1)).
        apply Qdiv_lt_mult.
        rearrange.
        generalize ((c - 1) / (b - 1)); intro r.
        SearchAbout (floor _ < _)%Z.
        apply floor_spec_lt.
        auto with zarith.
      * destruct H as [m [H1 H2]].
        exists m.
        apply Qlt_le_trans with (1 := H2).
        now apply power_lower_bound.
Qed.

Lemma power_arbitrarily_small b : 1 < b ->
  forall c, 0 < c -> exists m, b^m < c.
Proof.
  intros b_large c c_pos.
  destruct (power_arbitrarily_large b b_large (/ c)) as [m H].
  exists (-m)%Z.
  rewrite Qpower.Qpower_opp.
  apply Qlt_shift_inv_r.
  apply Qpower_pos_pos.
  now apply Qlt_trans with (y := 1).
  rewrite Qmult_comm.
  apply Qdiv_lt_mult.
  easy.
  setoid_replace (1 / c) with (/ c) by field.
  easy.
  auto with qarith.
Qed.

(* We need actual computable upper and lower bounds. *)

Lemma power_of_large_is_large b e : 1 <= b -> (0 <= e)%Z -> 1 <= b^e.
Proof.
  intro b_large; revert e.
  apply natlike_ind.
  - (* Base case. *) now compute.
  - intros.
    unfold Z.succ.
    rewrite Qpower.Qpower_plus.
    setoid_replace (b^1) with b by easy.
    apply Qle_trans with (1 := b_large).
    setoid_replace b with (1 * b) at 1 by ring.
    apply Qmult_le_compat_r.
    easy.
    now apply Qle_trans with (y := 1).
    assert (0 < b).
    apply Qlt_le_trans with (2 := b_large).
    easy.
    auto with qarith.
Qed.

Lemma power_monotonic_in_second b e f : 1 <= b -> (e <= f)%Z -> b^e <= b^f.
Proof.
  intros b_large e_le_f.
  replace f with (e + (f - e))%Z by ring.
  rewrite Qpower.Qpower_plus.
  setoid_replace (b ^ e) with (b ^ e * 1) at 1 by ring.
  apply Qmult_le_l.
  apply Qpower_pos_pos.
  apply Qlt_le_trans with (y := 1).
  easy.
  easy.
  apply power_of_large_is_large.
  easy.
  auto with zarith.
  assert (0 < b).
  now apply Qlt_le_trans with (y := 1).
  auto with qarith.
Qed.

Lemma power_injective_lt b e f :
  1 < b -> b^e < b^f -> (e < f)%Z.
Proof.
  intro b_large.
  intro H.
  apply Z.nle_gt.
  contradict H.
  apply Qle_not_lt.
  apply power_monotonic_in_second.
  apply Qlt_le_weak.
  easy.
  easy.
Qed.


Section ilog_bounds.
  Variable b : Q.
  Hypothesis b_large : 1 < b.

  Definition log_upper (c : Q) (c_positive : 0 < c) : Z :=
    Z.max 0 (1 + floor ((c - 1) / (b - 1))).

  Lemma log_upper_bound c c_positive : c < b^(log_upper c c_positive).
  Proof.
    unfold log_upper.
    destruct (Qlt_le_dec c 1) as [c_lt_1 | c_ge_1].
    - apply Qlt_le_trans with (1 := c_lt_1).
      apply power_of_large_is_large.
      now apply Qlt_le_weak.
      apply Z.le_max_l.
    - remember ((1 + floor ((c - 1) / (b - 1)))%Z) as m.
      apply Qlt_le_trans with (y := 1 + inject_Z m * (b - 1)).
      + rearrange_goal (c - 1 < inject_Z m * (b - 1)).
        apply Qdiv_lt_mult.
        rearrange.
        rewrite Heqm.
        generalize ((c - 1) / (b - 1)) as q; intro q.
        apply floor_spec_lt.
        auto with zarith.
      + apply Qle_trans with (y := b ^ m).
        apply power_lower_bound.
        easy.
        rewrite Heqm.
        replace 0%Z with (1 + -1)%Z by ring.
        apply Z.add_le_mono_l.
        apply Z.le_trans with (m := 0%Z).
        easy.
        apply floor_spec.
        ring_simplify.
        apply Qmult_le_div.
        rearrange.
        ring_simplify.
        rearrange.
        apply power_monotonic_in_second.
        now apply Qlt_le_weak.
        apply Z.le_max_r.
  Qed.

  Definition log_lower (c : Q) (c_positive : 0 < c) : Z.
  Proof.
    refine (- (log_upper (/c) _))%Z; now apply Qinv_lt_0_compat.
  Defined.

  Lemma log_lower_bound c c_positive : b^(log_lower c c_positive) < c.
  Proof.
    unfold log_lower.
    rewrite Qpower.Qpower_opp.
    apply Qlt_shift_inv_r.
    apply Qpower_pos_pos.
    now apply Qlt_trans with (y := 1).
    rewrite Qmult_comm.
    apply Qdiv_lt_mult.
    easy.
    setoid_replace (1 / c) with (/ c).
    apply log_upper_bound.
    field.
    auto with qarith.
  Qed.

  Lemma log_lower_lt_log_upper c c_positive :
    (log_lower c c_positive < log_upper c c_positive)%Z.
  Proof.
    apply power_injective_lt with (b := b).
    easy.
    apply Qlt_trans with (y := c).
    apply log_lower_bound.
    apply log_upper_bound.
  Qed.

End ilog_bounds.

Lemma eight_positive : 0 < (8#1).
Proof. easy. Qed.

Check log_upper (2#1) (8#1) eight_positive.
Eval compute in log_upper (3#2) (8#1) eight_positive.
Eval compute in log_lower (3#2) (8#1) eight_positive.

Eval compute in log_upper (3#2) (1#8) eight_positive.
Eval compute in log_lower (3#2) (1#8) eight_positive.

Section ilog.
  Variable b c : Q.
  Hypothesis b_large : 1 < b.
  Hypothesis c_pos : 0 < c.

  Let cond m := negb (Qle_bool (b^m) c).

  Lemma cond_false m : cond m = false <-> b^m <= c.
  Proof.
    unfold cond; split; intro.
    - now apply Qle_bool_iff, negb_false_iff.
    - now apply negb_false_iff, Qle_bool_iff.
  Qed.

  Lemma cond_true m : cond m = true <-> c < b^m.
  Proof.
    setoid_replace (cond m = true) with (~(cond m = false)).
    setoid_replace (c < b^m) with (~(b^m <= c)).
    now rewrite cond_false.
    apply Qlt_nge.
    destruct (cond m); split; intro; try easy.
    exfalso.
    auto.
  Qed.

  Lemma cond_monotonic m n : cond m = false -> cond n = true -> (m < n)%Z.
  Proof.
    rewrite cond_false, cond_true.
    intros H0 H1.
    apply (power_injective_lt b).
    auto.
    apply Qle_lt_trans with (y := c); easy.
  Qed.

  Lemma cond_log_lower_false : cond (log_lower b c c_pos) = false.
  Proof.
    rewrite cond_false.
    apply Qlt_le_weak.
    apply log_lower_bound.
    easy.
  Qed.

  Lemma cond_log_upper_true : cond (log_upper b c c_pos) = true.
  Proof.
    rewrite cond_true.
    apply log_upper_bound.
    easy.
  Qed.

  Definition ilog :=
    last_false cond cond_monotonic _ _ cond_log_lower_false cond_log_upper_true.

  Lemma ilog_spec k :
    b^k <= c  <->  (k <= ilog)%Z.
  Proof.
    rewrite <- cond_false; apply last_false_spec.
  Qed.

End ilog.

Definition ilog_example : Z.
  refine (ilog (3#1) (1#82) _ _); now compute. Defined.

Example ilog_example_equality : ilog_example = (-5)%Z.
Proof.
  now compute.
Qed.