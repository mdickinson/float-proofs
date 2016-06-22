Require Import ZArith.

Set Implicit Arguments.

Local Open Scope Z.

Inductive interval : Set :=
| build_interval m n (m_le_n : m <= n) : interval.

Definition length (i : interval) :=
  match i with
  | @build_interval m n _ => n - m
  end.

Definition low (i : interval) :=
  match i with
  | @build_interval m n _ => m
  end.

Definition mid (i : interval) :=
  match i with
  | @build_interval m n _ => (m + n) / 2
  end.

Definition high (i : interval) :=
  match i with
  | @build_interval m n _ => n
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

(* Now we can describe the type of bisection trees. *)

Inductive bisection_tree : interval -> Set :=
| bisection_leaf i : length i = 1 -> bisection_tree i
| bisection_fork i : bisection_tree (low_half i) ->
                     bisection_tree (high_half i) -> bisection_tree i.

(* We want to define a bisection tree for each nontrivial interval i.

   First, the lemmas we'll need to make the recursive definition. *)

Check Z_div_mult_full.


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

Check bisect_search_tree.

(*
bisect_search_tree
     : (Z -> bool) -> forall i : interval, bisection_tree i -> interval
*)

Check bisect_interval.

(*
bisect_interval
     : forall i : interval, 0 < length i -> bisection_tree i
 *)

Definition bisection_search P i i_nontrivial :=
  bisect_search_tree P (bisect_interval i i_nontrivial).

Check bisection_search.

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

End bisection_search_facts.

Check bisection_search_converges.
Check bisection_search_high_true.

Section bisection_search_example.

  Definition P m := 200 <? m * m.

  Definition i : interval. now refine (@build_interval (-20) 50 _). Defined.

  Definition result : interval. now refine (bisection_search P i _). Defined.

  Eval compute in high result.

End bisection_search_example.

Section first_true.
  (* Using the bisection search to find the first integer
     for which a given proposition is true. *)

  Variable P : Z -> bool.
  Hypothesis P_monotonic : forall n m, n <= m -> P n = true -> P m = true.

  Variables low high : Z.
  Hypothesis P_low_false : P low = false.
  Hypothesis P_high_true : P high = true.

  (* Given the above setup, there's a unique integer n such
     that P m = true for all n <= m and P m = false for all m < n. *)

  Lemma low_lt_high : low < high.
  Proof.
    SearchAbout (_ < _  \/ _).
    destruct (Z.lt_ge_cases low high).
    - easy.
    - assert (P low = true) by (now apply (P_monotonic H)).
      assert (false = true).
      transitivity (P low).
      auto.
      auto.
      contradict H1. easy.
  Qed.

  Lemma low_le_high : low <= high.
  Proof.
    apply Z.lt_le_incl, low_lt_high.
  Qed.

  Let search_interval := build_interval low_le_high.

  Definition first_true : Z.
  Proof.
    refine (Top.high (bisection_search P search_interval _)).
    unfold length, search_interval.
    pose proof low_lt_high.
    auto with zarith.
  Defined.

  Theorem first_true_is_true : P first_true = true.
  Proof.
    unfold first_true.
    apply bisection_search_high_true.
    now simpl.
  Qed.

  (* Want to show that for all m,

     P m = true <-> first_true <= m.




   *)

End first_true.

Check first_true.