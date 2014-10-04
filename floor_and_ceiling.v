Require Import ZArith.
Require Import QArith.
Require Import Qabs.


Open Scope Z.

Lemma negate_iff : forall P Q, (P <-> Q)  ->  (~P <-> ~Q).
Proof.
  tauto. 
Qed.

Lemma floor_spec_Z : forall a b n,
  (0 < b) -> (n * b <= a  <->  n <= a / b).
Proof.
  intros; rewrite Z.mul_comm; split; intro.
    now apply Z.div_le_lower_bound.
    apply Z.le_trans with (m := b * (a / b)).
      now apply Z.mul_le_mono_pos_l.
      now apply Z.mul_div_le.
Qed.

Lemma floor_spec_Z_lt : forall a b n,
  (0 < b) -> (a < n * b  <->  a / b < n).
Proof.
  intros a b n b_positive.
  setoid_replace (a < n * b) with (~ n * b <= a) by (split; auto with zarith).
  setoid_replace (a / b < n) with (~ n <= a / b) by (split; auto with zarith).
  apply negate_iff. now apply floor_spec_Z.
Qed.


Open Scope Q.

(* Some helper lemmas that we'll need later. *)

Lemma Qopp_le_mono : forall x y : Q, x <= y  <->  -y <= -x.
Proof.
  intros; unfold Qopp; unfold Qle; simpl;
  split; intro; apply Z.opp_le_mono; ring_simplify; assumption.
Qed.


Lemma Qopp_lt_mono : forall x y : Q, x < y  <->  -y < -x.
Proof.
  intros; unfold Qopp; unfold Qlt; simpl;
  split; intro; apply Z.opp_lt_mono; ring_simplify; assumption.
Qed.

(* Define the floor function, and prove its characteristic property. *)
Definition floor (x : Q) : Z := (Qnum x / ' Qden x)%Z.

(* Three distinct characterisations of the floor function. *)

Lemma floor_spec : forall (x:Q) (n:Z),
  inject_Z n <= x  <->  (n <= floor x)%Z.
Proof.
  intros; unfold inject_Z; unfold floor; unfold Qle;
  rewrite Z.mul_1_r; apply floor_spec_Z; apply Pos2Z.is_pos.
Qed.

(* It's much easier to prove that "floor" is a setoid morphism
   using "floor_spec" than using the definition directly. *)

Add Morphism floor : floor_morphism.
  intros x y x_eq_y; apply Z.le_antisymm; apply floor_spec;
  [ rewrite <- x_eq_y | rewrite x_eq_y ]; apply floor_spec; auto with zarith.
Qed.

Lemma floor_spec_lt : forall (x:Q) (n:Z),
  x < inject_Z n  <->  (floor x < n)%Z.
Proof.
  intros x n;
  setoid_replace (x < inject_Z n) with (~ inject_Z n <= x) by (split; auto with qarith);
  setoid_replace (floor x < n)%Z with (~ n <= floor x)%Z by (split; auto with zarith);
  apply negate_iff; exact (floor_spec x n).
Qed.

Lemma floor_spec_alt : forall (x:Q) (n:Z),
  n = floor x  <->  inject_Z n <= x /\ x < inject_Z n + 1.
Proof.
  intros x n;
  replace (inject_Z n + 1) with (inject_Z (n + 1)) by (rewrite inject_Z_plus; trivial);
  split; intro;
  [
    split; [apply floor_spec | apply floor_spec_lt]; auto with zarith
  |
    apply Z.le_antisymm;
    [ apply floor_spec | apply Zlt_succ_le; apply floor_spec_lt]; tauto
  ].
Qed.

Lemma floor_inject : forall n : Z, floor (inject_Z n) = n.
Proof.
  intro n; apply Z.le_antisymm; [ rewrite Zle_Qle | ]; apply floor_spec;
  [apply Zle_refl | apply Qle_refl].
Qed.

Lemma floor_monotonic : forall q r : Q,
  q <= r  ->  (floor q <= floor r)%Z.
Proof.
  intros q r q_le_r.
  apply floor_spec.
  apply Qle_trans with (y := q).
  apply floor_spec. now apply Zle_refl. assumption.
Qed.

(* Define the ceiling function, and prove its characteristic property. *)

Definition ceiling (x : Q) : Z := (-floor(-x))%Z.

Add Morphism ceiling : ceiling_morphism.
  intros x y x_eq_y; unfold ceiling; rewrite x_eq_y; reflexivity.
Qed.

Lemma ceiling_spec : forall (x:Q) (n:Z),
    x <= inject_Z n  <->  (ceiling x <= n)%Z.
Proof.
  intros; setoid_replace (- floor (-x) <= n)%Z with (-n <= floor (- x))%Z by (
    split; intro; apply Z.opp_le_mono; ring_simplify; assumption);
  rewrite <- floor_spec; rewrite inject_Z_opp;
  apply Qopp_le_mono.
Qed.


Lemma ceiling_spec_lt : forall (x:Q) (n:Z),
  inject_Z n < x  <->  (n < ceiling x)%Z.
Proof.
  intros x n;
  setoid_replace (inject_Z n < x) with (~ x <= inject_Z n) by (
    split; auto with qarith);
  setoid_replace (n < ceiling x)%Z with (~ ceiling x <= n)%Z by (
    split; auto with zarith);
  apply negate_iff; exact (ceiling_spec x n).
Qed.


Lemma ceiling_spec_alt : forall (x:Q) (n:Z),
  n = ceiling x  <->  inject_Z n - 1 < x /\ x <= inject_Z n.
Proof.
  intros. replace (inject_Z n - 1) with (inject_Z (n - 1)) by (
    unfold Z.sub; rewrite inject_Z_plus; auto);
  split; intro;
  [
    split; [apply ceiling_spec_lt | apply ceiling_spec]; auto with zarith
  |
    apply Z.le_antisymm;
    [ apply Z.lt_pred_le; apply ceiling_spec_lt | apply ceiling_spec]; tauto
  ].
Qed.


Lemma ceiling_inject : forall n : Z, ceiling (inject_Z n) = n.
Proof.
  intro n; apply Z.le_antisymm; [ | rewrite Zle_Qle]; apply ceiling_spec;
  [auto with qarith | auto with zarith].
Qed.


Lemma ceiling_monotonic : forall q r : Q,
  q <= r  ->  (ceiling q <= ceiling r)%Z.
Proof.
  intros.
  apply ceiling_spec.
  apply Qle_trans with (y := r).
  easy. apply ceiling_spec. apply Z.le_refl.
Qed.


Lemma neg_ceiling_is_floor_neg : forall q : Q,
  (- ceiling q)%Z = floor (-q).
Proof.
  unfold ceiling. intro. now rewrite Z.opp_involutive.
Qed.

Lemma neg_floor_is_ceiling_neg : forall q : Q,
  (- floor q)%Z = ceiling (-q).
Proof.
  unfold ceiling. intro. now rewrite Qopp_opp.
Qed.


Definition is_integer (q : Q) : Prop :=
  exists n : Z, inject_Z n == q.

Lemma floor_ceiling_bound : forall q : Q, (ceiling q <= floor q + 1)%Z.
Proof.
  intro.
  apply ceiling_spec.
  rewrite inject_Z_plus.
  replace (inject_Z 1) with 1 by auto with qarith.
  remember (floor q) as n.
  assert (q < inject_Z n + 1).
  apply floor_spec_alt; assumption.
  auto with qarith.
Qed.
  
Lemma floor_le_ceiling : forall q : Q, (floor q <= ceiling q)%Z.
Proof.
  intro.
  rewrite Zle_Qle.
  apply Qle_trans with (y := q).
  apply floor_spec.  auto with zarith.
  apply ceiling_spec. auto with zarith.
Qed.


Lemma floor_integer : forall q : Q,
  is_integer q  <->  inject_Z (floor q) == q.
Proof.
  intro q.
  split; unfold is_integer; intro.
    (* q an integer -> ... *)
    destruct H.
    rewrite <- H.
    assert (inject_Z (floor (inject_Z x)) <= inject_Z x).
    apply floor_spec. auto with zarith.
    assert (inject_Z x <= inject_Z (floor (inject_Z x))).
    rewrite <- Zle_Qle.
    apply floor_spec. auto with qarith.
    auto with qarith.

    (* ... -> q an integer *)
    exists (floor q). assumption.
Qed.


Lemma ceiling_integer : forall q : Q,
  is_integer q  <->  inject_Z (ceiling q) == q.
Proof.
  intro q.
  split; unfold is_integer; intro;
  [ destruct H; rewrite <- H;
    rewrite ceiling_inject; reflexivity
    | exists (ceiling q); assumption].
Qed.


Lemma le_not_eq : forall a b : Q, a <= b -> ~(a == b) -> a < b.
Proof.
  intros a b H H0; apply Qnot_le_lt; intro; apply H0; now apply Qle_antisym.
Qed.


Lemma floor_ceiling_gap : forall q : Q,
  ~(is_integer q) -> (ceiling q = floor q + 1)%Z.
Proof.
  intros q q_not_integer.
  assert (floor q < ceiling q)%Z.
  apply ceiling_spec_lt.
  apply le_not_eq.
    apply floor_spec; apply Z.le_refl.
    intro; apply q_not_integer; now apply floor_integer.
  assert (ceiling q <= floor q + 1)%Z by (apply floor_ceiling_bound).
  omega.
Qed.


Lemma floor_ceiling_gap_Q : forall q : Q,
  ~is_integer q -> inject_Z (ceiling q) == inject_Z (floor q) + 1.
Proof.
  intros. replace 1 with (inject_Z 1) by reflexivity.
  rewrite <- inject_Z_plus. apply inject_Z_injective.
  now apply floor_ceiling_gap.
Qed.

(* Define the round function, which rounds to the nearest integer,
   rounding halfway cases to the nearest even integer. *)

Definition round (q : Q) : Z :=
  let n := floor q in
  match Qcompare (q - inject_Z n) (1 # 2) with
  | Lt => floor q
  | Eq => if Z.even n then floor q else ceiling q
  | Gt => ceiling q
  end.


Add Morphism round : round_morphism.
Proof.
  intros; unfold round; now rewrite ?H.
Qed.

Lemma Q_sub_add : forall a b c : Q,
  a - b == c  ->  a == b + c.
Proof.
  intros. apply Qplus_inj_r with (z := -b). rewrite <- H. ring.
Qed.


Lemma tie_floor_ceiling : forall q,
  q - inject_Z (floor q) == 1 # 2  ->  inject_Z (ceiling q) - q == 1 # 2.
Proof.
  intros. rewrite floor_ceiling_gap_Q.
  setoid_replace (inject_Z (floor q)) with (q - (1 # 2)) by (rewrite <- H; ring); ring.
  rewrite floor_integer; intro; rewrite H0 in H; now ring_simplify in H.
Qed.


Lemma frac_part_nonnegative : forall q : Q, 0 <= q - inject_Z (floor q).
Proof.
  intro;
  apply Qplus_le_l with (z := inject_Z (floor q)); ring_simplify;
  apply floor_spec; apply Z.le_refl.
Qed.

Lemma negfrac_part_nonpositive: forall q : Q, q - inject_Z (ceiling q) <= 0.
Proof.
  intro;
  apply Qplus_le_l with (z := inject_Z (ceiling q)); ring_simplify;
  apply ceiling_spec; apply Z.le_refl.
Qed.

Lemma Qneg_le : forall a b, -a < b -> -b < a.
Proof.
  intros.
  apply Qplus_lt_l with (z := b - a).
  ring_simplify. now ring_simplify in H.
Qed.


Lemma round_error : forall q,
  Qabs (q - inject_Z (round q)) <= 1 # 2.
Proof.
  intros; unfold round.
  case_eq (q - inject_Z (floor q) ?= 1 # 2).
    (* First subcase: halfway case. *)
    intro. apply Qeq_alt in H. case (Z.even (floor q)).
      rewrite H; now compute.
      setoid_replace (q - inject_Z (ceiling q)) with
        (- (inject_Z (ceiling q) - q)) by ring; now rewrite tie_floor_ceiling.
    (* Second subcase: fractional part < 1 # 2. *)
    rewrite Qabs_pos by (apply frac_part_nonnegative); rewrite <- Qlt_alt;
    apply Qlt_le_weak.
    (* Third subcase: fractional part > 1 # 2. *)
    rewrite Qabs_neg by (apply negfrac_part_nonpositive); rewrite <- Qgt_alt.
    intro.
    setoid_replace (inject_Z (ceiling q)) with (inject_Z (floor q) + 1) by (
      apply floor_ceiling_gap_Q; rewrite floor_integer; intro; rewrite H0 in H;
      ring_simplify in H; easy).
    apply Qlt_le_weak; apply Qneg_le; apply Qplus_lt_l with (z := 1); now ring_simplify.
Qed.


Lemma round_floor_or_ceiling : forall q,
  round q = floor q  \/  round q = ceiling q.
Proof.
  intro q; unfold round; destruct (Qcompare (q - inject_Z (floor q)) (1 # 2));
  destruct (Z.even (floor q)); tauto.
Qed.


Lemma Zeven_odd : forall n : Z, Z.even n = false  <->  Z.odd n = true.
Proof.
  intro; split; intro.
  rewrite <- Z.negb_even. rewrite H. easy.
  rewrite <- Z.negb_odd. rewrite H. easy.
Qed.

Lemma Znoteven_bool_iff : forall n : Z, Z.even n = false  <->  Zodd n.
Proof.
  setoid_rewrite Zeven_odd; apply Zodd_bool_iff.
Qed.
  
Lemma tie_characterization : forall q,
  Qabs (q - inject_Z (round q)) == 1 # 2  ->  q - inject_Z (floor q) == 1 # 2.
Proof.
  intros.
  (* round q is either floor q or ceiling q. *)
  destruct (round_floor_or_ceiling q); rewrite H0 in H; clear H0.
  (* Case 1: round q is floor q.
     Then q - inject_Z (floor q) is nonnegative. ... *)
  rewrite <- Qabs_pos. easy.
  apply Qplus_le_r with (z := inject_Z (floor q)); ring_simplify;
    apply floor_spec; apply Zle_refl.

  (* Case 2: round q is ceiling q. *)
  assert (Qabs (q - inject_Z (ceiling q)) == - (q - inject_Z (ceiling q))).
  apply Qabs_neg. apply Qplus_le_r with (z := inject_Z (ceiling q)).
    ring_simplify. apply ceiling_spec. apply Zle_refl.
  rewrite H0 in H.

  assert (inject_Z (ceiling q) == inject_Z (floor q) + 1).
  apply floor_ceiling_gap_Q.
  rewrite ceiling_integer.
  intro. rewrite H1 in H. now ring_simplify in H.
  rewrite H1 in H. clear H0. clear H1.

  apply Qplus_inj_r with (z := -q + inject_Z (floor q) + (1 # 2)).
  ring_simplify. now ring_simplify in H.
Qed.

  
Lemma round_error_half : forall q,
  let rounded := round q in
  (Qabs (q - inject_Z (rounded)) == 1 # 2) -> Zeven rounded.
Proof.
  intros q rounded; unfold rounded; intro; unfold round.
  case_eq (q - inject_Z (floor q) ?= 1 # 2);
  [rewrite <- Qeq_alt | rewrite <- Qlt_alt | rewrite <- Qgt_alt]; intro.
  (* Case 1: halfway case. *)
  rewrite floor_ceiling_gap.
  case_eq (Z.even (floor q)); intro.
    (* Case 1.1. *)
    now apply Zeven_bool_iff.
    (* Case 1.2. *)
    apply Zodd_plus_Zodd; [now apply Znoteven_bool_iff | easy].
    (* make good on proof that q is not an integer. *)
    rewrite floor_integer. intro. rewrite H1 in H0.
    now ring_simplify in H0.

  (* Case 2 *)
  absurd (q - inject_Z (floor q) == 1 # 2).
    auto with qarith.
    now apply tie_characterization.

  (* Case 3 *)
  absurd (q - inject_Z (floor q) == 1 # 2).
    auto with qarith.
    now apply tie_characterization.
Qed.
