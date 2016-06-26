Require Import ZArith.

Set Implicit Arguments.

Local Open Scope Z.

Inductive interval : Set :=
| build_interval m n (m_le_n : m <= n) : interval.

Definition low (i : interval) :=
  match i with
  | @build_interval m n _ => m
  end.

Definition high (i : interval) :=
  match i with
  | @build_interval m n _ => n
  end.

Definition mid (i : interval) :=
  match i with
  | @build_interval m n _ => (m + n) / 2
  end.

Lemma low_le_mid i : low i <= mid i.
Proof.
  unfold low, mid; destruct i;
  apply Z.div_le_lower_bound; auto with zarith.
Qed.

Lemma mid_le_high i : mid i <= high i.
Proof.
  unfold mid, high; destruct i;
  replace n with (n * 2 / 2) at 2 by (now apply Z_div_mult_full);
  apply Z.div_le_mono; auto with zarith.
Qed.

Definition low_half i := build_interval (low_le_mid i).
Definition high_half i := build_interval (mid_le_high i).

Definition length (i : interval) :=
  match i with
  | @build_interval m n _ => n - m
  end.

(* Now we can describe the type of bisection trees. *)

Inductive bisection_tree : interval -> Set :=
| bisection_leaf i : length i = 1 -> bisection_tree i
| bisection_fork i : bisection_tree (low_half i) ->
                     bisection_tree (high_half i) -> bisection_tree i.

(* We want to define a bisection tree for each nontrivial interval i.

   First, the lemmas we'll need to make the recursive definition. *)

Lemma elim_half_eq a b : a * 2 = b -> a = b / 2.
Proof.
  intro H; rewrite <- H; symmetry; now apply Z_div_mult_full.
Qed.

Lemma elim_half_eq_1 a b : a * 2 + 1 = b -> a = b / 2.
Proof.
  intro H; rewrite <- H; rewrite Z.div_add_l; auto with zarith.
Qed.


Lemma len_low_half_0 i p : length i = 2*p -> length (low_half i) = p.
Proof.
  unfold length, low_half, low, mid; destruct i as [m n _]; intro;
  replace n with (2 * p + m) by auto with zarith;
  replace ((m + (2 * p + m)) / 2) with (m + p) by (apply elim_half_eq; ring);
  ring.
Qed.

Lemma len_low_half_1 i p : length i = 2*p + 1 -> length (low_half i) = p.
Proof.
  unfold length, low_half, low, mid; destruct i as [m n _]; intro;
  replace n with (2 * p + 1 + m) by auto with zarith;
  replace ((m + (2 * p + 1 + m)) / 2) with (m + p)
    by (apply elim_half_eq_1; ring);
  ring.
Qed.

Lemma len_high_half_0 i p : length i = 2*p -> length (high_half i) = p.
Proof.
  unfold length, high_half, high, mid; destruct i as [m n _]; intro;
  replace n with (2 * p + m) by auto with zarith;
  replace ((m + (2 * p + m)) / 2) with (m + p) by (apply elim_half_eq; ring);
  ring.
Qed.

Lemma len_high_half_m1 i p : length i = 2*p - 1 -> length (high_half i) = p.
Proof.
  unfold length, high_half, high, mid; destruct i as [m n _]; intro;
  replace n with (2 * p - 1 + m) by auto with zarith;
  replace ((m + (2 * p - 1 + m)) / 2) with (m + p - 1)
    by (apply elim_half_eq_1; ring).
  ring.
Qed.


Definition bisect_interval_pos p :
  forall (b : bool), forall i,
      length i = (Z.pos p + (if b then 1 else 0)) -> bisection_tree i.
Proof.
  induction p; intro b; case_eq b; intros Hb i Hlen;
  try (apply bisection_fork; (apply (IHp true) + apply (IHp false));
    (apply len_low_half_0 + apply len_high_half_0 +
     apply len_low_half_1 + apply len_high_half_m1);
    rewrite Hlen;
    (rewrite Pos2Z.inj_xO + rewrite Pos2Z.inj_xI); ring);
  try (apply bisection_fork; apply bisection_leaf;
    (apply len_low_half_0 + apply len_high_half_0); now rewrite Hlen).
  try (apply bisection_leaf; now rewrite Hlen).
Defined.

Definition bisect_interval i : 0 < length i -> bisection_tree i.
Proof.
  intro i_nontrivial; apply (bisect_interval_pos (Z.to_pos (length i)) false);
  rewrite Z2Pos.id; auto with zarith.
Defined.

Section bisect_interval_examples.

  Notation "m || n" := (@build_interval m n _).
  Notation "[ x ]" := (bisection_leaf x _).

  Definition interval1 : interval. now refine (@build_interval 2 3 _). Defined.
  Definition bisect1 : bisection_tree interval1.
  Proof.
    now refine (bisect_interval interval1 _).
  Defined.

  Eval compute in bisect1.

  Definition interval2 : interval. now refine (@build_interval 5 7 _). Defined.
  Definition bisect2 : bisection_tree interval2.
  Proof.
    now refine (bisect_interval interval2 _).
  Defined.

  Eval compute in bisect2.

  Definition interval3 : interval. now refine (@build_interval 10 15 _).
  Defined.
  Definition bisect3 : bisection_tree interval3.
  Proof.
    now refine (bisect_interval interval3 _).
  Defined.

  Eval compute in bisect3.

End bisect_interval_examples.

(* Here's the main recursive function. *)

Fixpoint bisect_search_tree (P : Z -> bool) i (t : bisection_tree i) :=
  match t with
  | bisection_leaf x _ => x
  | bisection_fork low_subtree high_subtree =>
    if P (mid i)
    then bisect_search_tree P low_subtree
    else bisect_search_tree P high_subtree
  end.

Section bisect_search_tree_facts.

  Variable P : Z -> bool.
  Variable i : interval.
  Variable t : bisection_tree i.

  Theorem convergence : length (bisect_search_tree P t) = 1.
  Proof.
    induction t; [ | simpl; case_eq (P (mid i)) ]; auto.
  Qed.

  Theorem high_true : P (high i) = true ->
                      P (high (bisect_search_tree P t)) = true.
  Proof.
    induction t; [ | simpl; case_eq (P (mid i)) ]; auto.
  Qed.

  Theorem low_false : P (low i) = false ->
                      P (low (bisect_search_tree P t)) = false.
  Proof.
    induction t; [ | simpl; case_eq (P (mid i)) ]; auto.
  Qed.

End bisect_search_tree_facts.

(*
bisect_search_tree
     : (Z -> bool) -> forall i : interval, bisection_tree i -> interval
*)

(*
bisect_interval
     : forall i : interval, 0 < length i -> bisection_tree i
 *)

Definition bisection_search P i i_nontrivial :=
  bisect_search_tree P (bisect_interval i i_nontrivial).

(*
bisection_search
     : (Z -> bool) -> forall i : interval, 0 < length i -> interval
 *)

Section bisection_search_facts.

  Variable P : Z -> bool.
  Variable i : interval.
  Hypothesis i_nontrivial : 0 < length i.

  Let result := bisection_search P i i_nontrivial.

  Theorem bisection_search_converges :
    length result = 1.
  Proof.
    apply convergence.
  Qed.

  Theorem bisection_search_high_true :
    P (high i) = true -> P (high result) = true.
  Proof.
    apply high_true.
  Qed.

  Theorem bisection_search_low_false :
    P (low i) = false -> P (low result) = false.
  Proof.
    apply low_false.
  Qed.

  Theorem bisection_search_low_high : high result = low result + 1.
  Proof.
    replace 1 with (length result) by (apply bisection_search_converges).
    unfold low, high, length; destruct result; auto with zarith.
  Qed.

End bisection_search_facts.

Section first_true.

  Variable P : Z -> bool.
  Hypothesis P_monotonic : forall m n, P m = false -> P n = true -> m < n.

  Variables m n : Z.
  Hypothesis P_false : P m = false.
  Hypothesis P_true : P n = true.

  Let m_le_n : m <= n.
  Proof.
    apply Z.lt_le_incl; auto.
  Qed.
  
  Let initial := build_interval m_le_n.

  Let initial_nontrivial : 0 < length initial.
  Proof.
    unfold length, initial.
    assert (m < n -> 0 < n - m) by auto with zarith.
    auto.
  Qed.
    
  Definition first_true := high (bisection_search P initial initial_nontrivial).
  Definition last_false := low (bisection_search P initial initial_nontrivial).

  (* Basic facts. *)

  Theorem first_true_last_false : first_true = last_false + 1.
  Proof.
    apply bisection_search_low_high.
  Qed.

  Theorem first_true_spec k : P k = true  <->  first_true <= k.
  Proof.
    split; intro H.
    - rewrite first_true_last_false.
      apply Z.le_succ_l.
      apply P_monotonic.
      apply bisection_search_low_false.
      apply P_false.
      apply H.
    - apply Bool.not_false_is_true; contradict H; apply Zlt_not_le.
      apply P_monotonic.
      apply H.
      apply bisection_search_high_true.
      apply P_true.
  Qed.

  Theorem last_false_spec k : P k = false  <->  k <= last_false.
  Proof.
    split; intro H.
    - replace last_false with (first_true - 1) by (rewrite first_true_last_false; ring).      apply Z.lt_le_pred.
      apply P_monotonic.
      apply H.
      apply bisection_search_high_true.
      auto.
    - apply Bool.not_true_is_false.
      contradict H.
      apply Zlt_not_le.
      apply P_monotonic.
      apply bisection_search_low_false.
      auto.
      auto.
  Qed.
End first_true.


Section bisection_search_example.

  Definition P m := 200 <? m * m.

  Definition i : interval. now refine (@build_interval (-20) 50 _). Defined.

  Definition result : interval. now refine (bisection_search P i _). Defined.

  (* Eval compute in high result. *)

End bisection_search_example.