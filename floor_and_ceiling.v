Section floor_and_ceiling.

Require Import ZArith.
Require Import QArith.
Require Import Qabs.


Open Scope Z.

Lemma floor_spec_Z : forall a b n,
  (0 < b) -> (n * b <= a  <->  n <= a / b).
Proof.
  intros; rewrite Z.mul_comm; split; intro.
    now apply Z.div_le_lower_bound.
    apply Z.le_trans with (m := b * (a / b)).
      now apply Z.mul_le_mono_pos_l.
      now apply Z.mul_div_le.
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

Lemma negate_iff : forall P Q, (P <-> Q)  ->  (~P <-> ~Q).
Proof.
  tauto. 
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

Add Morphism floor : Q_floor_morph.
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

(* Define the ceiling function, and prove its characteristic property. *)

Definition ceiling (x : Q) : Z := (-floor(-x))%Z.

Add Morphism ceiling : Q_ceiling_morph.
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


Lemma floor_ceiling_gap : forall q : Q,
  ~(is_integer q) -> (ceiling q = floor q + 1)%Z.
Proof.
  intros q q_not_integer.
  assert (ceiling q <= floor q + 1)%Z by (apply floor_ceiling_bound).
  assert (floor q < ceiling q)%Z.
  apply ceiling_spec_lt.

  (* It should be enough to show that inject_Z (floor q) <= q. *)
  assert (inject_Z (floor q) <= q) by (apply floor_spec; auto with zarith).
  assert (~(inject_Z (floor q) == q)) by (intro; apply q_not_integer; apply floor_integer; assumption).
  auto with qarith.

  auto with zarith.
Qed.


(* Define the round function, which rounds to the nearest integer,
   rounding halfway cases to the nearest even integer. *)

Definition round (q : Q) : Z :=
  let n := floor q in
  match (Qcompare (q - inject_Z n) (1 # 2)) with
  | Lt => floor q
  | Eq => if (Zeven_odd_dec n) then (floor q) else (ceiling q)
  | Gt => ceiling q
  end.


Add Morphism round : round_morphism.
Proof.
  intros x y x_eq_y.
  unfold round.
  rewrite x_eq_y.
  destruct (y - inject_Z (floor y) ?= 1 # 2).
  destruct (Zeven_odd_dec (floor x)); destruct (Zeven_odd_dec (floor y)).
  rewrite x_eq_y; reflexivity.
  absurd (Zeven (floor x)); [rewrite x_eq_y; apply Zodd_not_Zeven | ]; assumption.
  absurd (Zeven (floor x)); [apply Zodd_not_Zeven | rewrite x_eq_y] ; assumption.
  rewrite x_eq_y; reflexivity.
  rewrite x_eq_y; reflexivity.
  rewrite x_eq_y; reflexivity.
Qed.

Lemma round_error : forall q,
  Qabs (q - inject_Z (round q)) <= 1 # 2.
Proof.
  intros.
  unfold round.
  case_eq (Qcompare (q - inject_Z (floor q)) (1 # 2)); intro.
    (* Case of a tie. *)
    apply Qeq_alt in H.
    destruct (Zeven_odd_dec (floor q)).
    rewrite H.
    simpl. auto with qarith.

    assert (ceiling q = (floor q + 1))%Z.
    apply floor_ceiling_gap.
    assert (~ q == inject_Z (floor q)).
    intro.
    assert (q - inject_Z (floor q) == 0).
    rewrite <- H0. ring.
    revert H1.
    rewrite H.
    unfold Qeq. simpl. auto with zarith.

    intro.
    apply H0.
    symmetry.
    apply floor_integer. trivial.
    assert (inject_Z (ceiling q) - q == 1 # 2).
    rewrite H0.
    rewrite inject_Z_plus.
    revert H.
    generalize (inject_Z (floor q)).
    intro. intro.
    setoid_replace q with (q - q0 + q0) by ring.
    rewrite H.
    ring_simplify. reflexivity.

    setoid_replace (q - inject_Z (ceiling q)) with
                   (-(inject_Z (ceiling q) - q)) by ring.
    rewrite H1.
    simpl. auto with qarith.

    (* case q - floor q < 1/2 *)
    assert (q - inject_Z (floor q) < 1 # 2) by auto with qarith.
    rewrite Qabs_pos.
    auto with qarith.
    assert (inject_Z (floor q) <= q) by (apply floor_spec; auto with zarith).
    
    rewrite <- Qplus_le_l with (z := inject_Z (floor q)).
    ring_simplify. assumption.

    (* case q - floor q > 1/2 *)
    assert (q - inject_Z (ceiling q) <= 0).
    rewrite <- Qplus_le_l with (z := inject_Z (ceiling q)).
    ring_simplify. apply ceiling_spec.  apply Zle_refl.
    rewrite Qabs_neg.
    ring_simplify.
    assert (q - inject_Z (floor q) > 1 # 2).
    auto with qarith.

    assert (ceiling q = (floor q + 1))%Z.
    apply floor_ceiling_gap.
      (* proving that q is not an integer *)
      assert (~ q == inject_Z (floor q)).
      intro.
      revert H1. rewrite <- H2. setoid_replace (q - q) with 0 by ring.
      unfold Qlt. simpl. auto with zarith.
      intro. apply H2. symmetry. apply floor_integer. assumption.

    rewrite H2.
    rewrite inject_Z_plus.
    clear H0 H2 H.

    rewrite <- Qplus_le_l with (z := q - (1 # 2) - inject_Z (floor q)).
    ring_simplify.
    auto with qarith. assumption.
Qed.


Lemma round_floor_or_ceiling : forall q,
  round q = floor q  \/  round q = ceiling q.
Proof.
  intro q; unfold round; destruct (Qcompare (q - inject_Z (floor q)) (1 # 2));
  destruct (Zeven_odd_dec (floor q)); tauto.
Qed.


Lemma round_error_half : forall q,
  let rounded := round q in
  (Qabs (q - inject_Z (rounded)) == 1 # 2) -> Zeven rounded.
Proof.
  intro q. intro. unfold rounded. intro H.

  unfold round.
  case_eq (Qcompare (q - inject_Z (floor q)) (1 # 2)); intro.

    (* Subgoal 1: case where fractional part is exactly 1 # 2.
       (The other two cases should give contradictions. *)
    assert (ceiling q = floor q + 1)%Z.
      apply floor_ceiling_gap.
      assert (~(q == inject_Z (floor q))).
        intro.
        revert H0.
        rewrite <- H1.
        setoid_replace (q - q) with 0 by ring.
        unfold Qcompare. simpl. discriminate.
      intro. apply H1. symmetry. apply floor_integer. assumption.
    rewrite H1.   
    generalize (floor q). clear q rounded H H0 H1.
    intros. destruct (Zeven_odd_dec z). assumption.
    apply Zeven_Sn. assumption.

    (* Subgoal 2: frac part < 1 / 2.  Show that this is inconsistent
       with Qabs (q - inject_Z (round q)) == 1 / 2. *)
    pose proof (round_floor_or_ceiling q).
    elim H1.

    intro.
    revert H.
    rewrite H2.
    assert (0 <= q - inject_Z (floor q)).
    apply Qplus_le_l with (z := inject_Z (floor q)).
    ring_simplify. apply floor_spec. apply Zle_refl.

    rewrite Qabs_pos by apply H.
    intro.
    absurd (q - inject_Z (floor q) == 1 # 2); auto with qarith.

    intro.
    rewrite H2 in H.
    rewrite Qabs_neg in H.
    absurd (q - inject_Z (floor q) == 1 # 2).
    auto with qarith.
    
    assert (q == inject_Z (ceiling q) - (1 # 2)) by (rewrite <- H; ring).
    rewrite H3 at 1.
    apply Qplus_inj_r with (z := 1 # 2).
    ring_simplify.
    replace 1 with (inject_Z 1) by reflexivity.
    rewrite <- inject_Z_opp.
    rewrite <- inject_Z_plus.
    apply inject_Z_injective.
    apply Z.add_cancel_l with (p := floor q).
    ring_simplify.
    apply floor_ceiling_gap.

    (* Now we have to show that q is not an integer *)
    clear H0 H1 H2 H3 rounded.
    intro.
    assert (q == inject_Z (floor q)).
      symmetry.
      apply floor_integer.
      assumption.
    revert H.    
    rewrite H1 at 1.
    generalize (floor q).
    generalize (ceiling q).
    intros.
    clear q H0 H1.
    assert (- (inject_Z z0 - inject_Z z) == inject_Z (z - z0)).
    unfold Z.sub.
    rewrite inject_Z_plus.
    rewrite inject_Z_opp.
    ring.
    rewrite H0 in H.
    revert H.
    clear H0.
    generalize (z - z0)%Z.
    intros. clear z z0.
    revert H.
    unfold Qeq. simpl.

    (* Current goal is:  z1 * 2 = 1 -> False *)
    intro.    
    assert ((z1 * 2) mod 2 = 1 mod 2).
    apply f_equal2. assumption. trivial.
    assert ((z1 * 2) mod 2 = ((z1 mod 2) * (2 mod 2)) mod 2)%Z by (apply Zmult_mod).
    rewrite H1 in H0.
    revert H0.
    assert (2 mod 2 = 0)%Z.
    compute. reflexivity.
    rewrite H0.
    ring_simplify (z1 mod 2 * 0)%Z.
    compute.
    discriminate.

    assert (q <= inject_Z (ceiling q)).
    apply ceiling_spec. auto with zarith.
    apply Qplus_le_l with (z := inject_Z (ceiling q)).
    ring_simplify. assumption.

  (* Subgoal 3: here we're assuming that q mod 1 is > 1 / 2.
     Again, this should be inconsistent with the assumption
     that q - inject_Z (round q) == 1 / 2. *) 

  cut ((q - inject_Z (floor q) ?= 1 # 2) = Eq).
  rewrite H0. discriminate.
  apply Qeq_alt.
  pose proof (round_floor_or_ceiling q).
  elim H1; intro.

  rewrite H2 in H.
  assert (0 <= q - inject_Z (floor q)).
    apply Qplus_le_l with (z := inject_Z (floor q)). ring_simplify.
    apply floor_spec. auto with zarith.
  revert H. rewrite Qabs_pos. trivial. assumption.

  rewrite H2 in H.
  assert (q - inject_Z (ceiling q) <= 0).
    apply Qplus_le_l with (z := inject_Z (ceiling q)). ring_simplify.
    apply ceiling_spec. auto with zarith.
  revert H. rewrite Qabs_neg. intro.

  (* Clear out the irrelevant stuff. *)
  clear rounded H0 H1 H2 H3.

  (* Left with showing the following:
  q : Q
  H : - (q - inject_Z (ceiling q)) == 1 # 2
  ============================
   q - inject_Z (floor q) == 1 # 2
  *)

  assert (~ is_integer q). intro.
  assert (inject_Z (ceiling q) == q) by (apply ceiling_integer; assumption).
  rewrite H1 in H.
  ring_simplify in H.
  revert H. compute. discriminate.

  assert (ceiling q = floor q + 1)%Z by (apply floor_ceiling_gap; assumption).
  rewrite H1 in H.
  clear H0 H1.

  rewrite inject_Z_plus in H.
  replace (inject_Z 1) with 1 in H by reflexivity.
  assert (-(q - inject_Z (floor q)) == -(1 # 2)).
  ring_simplify in H.
  ring_simplify.
  apply Qplus_inj_r with (z := 1).
  ring_simplify. assumption.

  rewrite <- Qopp_involutive at 1.
  rewrite H0.  apply Qopp_involutive.

  apply Qplus_le_r with (z := inject_Z (ceiling q)).
  ring_simplify.
  apply ceiling_spec. auto with zarith.
Qed.


End floor_and_ceiling.
