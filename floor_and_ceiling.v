(* Definitions of floor : Q -> Z and ceiling : Q -> Z, and key results.

   Also defines is_integer. *)

Require Import ZArith.
Require Import QArith.
Require Import Qabs.

(* Helper lemmas that we'll need later in the module. *)

Lemma negate_iff : forall P Q, (P <-> Q)  ->  (~P <-> ~Q).
Proof.
  tauto.
Qed.

Open Scope Z.

Lemma Zle_sign_flip_l (a b : Z) : -a <= b -> -b <= a.
Proof.
  intro; apply Zplus_le_reg_r with (p := b - a); now ring_simplify.
Qed.

Lemma Zle_not_eq (a b : Z) : a <= b -> ~(a = b) -> a < b.
Proof.
  auto with zarith.
Qed.

Open Scope Q.

Notation "x <= y < z" := (x <= y /\ y < z) : Q_scope.

Lemma Qopp_le_mono (x y : Q) : x <= y  <->  -y <= -x.
Proof.
  intros; unfold Qopp; unfold Qle; simpl;
  split; intro; apply Z.opp_le_mono; now ring_simplify.
Qed.

Lemma Qopp_lt_mono (x y : Q) : x < y  <->  -y < -x.
Proof.
  intros; unfold Qopp; unfold Qlt; simpl;
  split; intro; apply Z.opp_lt_mono; now ring_simplify.
Qed.

Lemma Qlt_nge (x y : Q) : x < y <-> ~(y <= x).
  split; auto with qarith.
Qed.

Lemma Qle_not_eq (a b : Q) : a <= b -> ~(a == b) -> a < b.
Proof.
  auto with qarith.
Qed.

Lemma Qeq_le_incl (a b : Q) : a == b -> a <= b.
Proof.
  intro H; rewrite H; apply Qle_refl.
Qed.

Lemma Qabs_Zabs (x : Z) : Qabs (inject_Z x) == inject_Z (Z.abs x).
Proof.
  now unfold Qabs.
Qed.

(* The floor function can be defined in terms of the standard library
   / operator, which does Euclidean division. *)

Open Scope Z.

Definition floor (x : Q) : Z := (Qnum x / ' Qden x).

(* To prove the main specification theorem for floor, we first need
   to prove a corresponding theorem at integer level. *)

Lemma floor_spec_Z (a b n : Z) : 0 < b -> (n * b <= a  <->  n <= a / b).
Proof.
  intro; rewrite Z.mul_comm; split; intro;
    [ now apply Z.div_le_lower_bound |
    apply Z.le_trans with (m := b * (a / b));
      [apply Z.mul_le_mono_pos_l | apply Z.mul_div_le]; easy].
Qed.

(* Here's a trivially-equivalent variant based on < rather than <=. *)

Lemma floor_spec_Z_lt (a b n : Z) : (0 < b) -> (a < n * b  <->  a / b < n).
Proof.
  intro; repeat rewrite Z.lt_nge; apply negate_iff; now apply floor_spec_Z.
Qed.

(* Now we're in a position to give a lemma that complete characterises
   the floor function.  In fact, we'll give three distinct characterisations.

   To begin with, it's an adjoint to the inclusion of Z into Q.
 *)

Open Scope Q.

Lemma floor_spec (x : Q) (n : Z) : inject_Z n <= x  <->  (n <= floor x)%Z.
Proof.
  unfold Qle; rewrite Z.mul_1_r; apply floor_spec_Z; apply Pos2Z.is_pos.
Qed.

(* It's easier to prove that "floor" is a setoid morphism
   using "floor_spec" than using the definition directly. *)

Add Morphism floor : floor_morphism.
Proof.
  intros x y x_eq_y; apply Z.le_antisymm; apply floor_spec;
  [ rewrite <- x_eq_y | rewrite x_eq_y ]; apply floor_spec; apply Z.le_refl.
Qed.

(* Variant of the first characterisation based on < rather than <=. *)

Lemma floor_spec_lt (x : Q) (n : Z) : x < inject_Z n  <->  (floor x < n)%Z.
Proof.
  rewrite Z.lt_nge; rewrite Qlt_nge; apply negate_iff; apply floor_spec.
Qed.

(* The third characterisation describes floor x as the integer n
   satisfying n <= x < n + 1. *)

Lemma floor_spec_alt (x : Q) (n : Z) :
  n = floor x  <->  (inject_Z n <= x < inject_Z n + 1)%Q.
Proof.
  replace (inject_Z n + 1) with (inject_Z (n + 1)) by
    (now rewrite inject_Z_plus);
  split; intro;
  [
    split; [apply floor_spec | apply floor_spec_lt]; auto with zarith
  |
    apply Z.le_antisymm;
    [ apply floor_spec | apply Zlt_succ_le; apply floor_spec_lt]; easy
  ].
Qed.

Lemma floor_inject (n : Z) : floor (inject_Z n) = n.
Proof.
  apply Z.le_antisymm; [ rewrite Zle_Qle | ]; apply floor_spec;
  [apply Zle_refl | apply Qle_refl].
Qed.

Lemma floor_monotonic (q r : Q) : q <= r  ->  (floor q <= floor r)%Z.
Proof.
  intro; apply floor_spec; apply Qle_trans with (y := q);
  [apply floor_spec; apply Z.le_refl | easy].
Qed.

(* Define the ceiling function in terms of floor, and prove its characteristic
   properties. *)

Definition ceiling (x : Q) : Z := (-floor(-x))%Z.

Add Morphism ceiling : ceiling_morphism.
  intros x y x_eq_y; unfold ceiling; rewrite x_eq_y; reflexivity.
Qed.

Lemma ceiling_spec (x : Q) (n : Z) : x <= inject_Z n  <->  (ceiling x <= n)%Z.
Proof.
  split; intro; [
      apply Zle_sign_flip_l; apply floor_spec; rewrite inject_Z_opp;
        now rewrite <- Qopp_le_mono
    |
      rewrite Qopp_le_mono; rewrite <- inject_Z_opp; apply floor_spec;
        now apply Zle_sign_flip_l
    ].
Qed.


Lemma ceiling_spec_lt (x:Q) (n:Z) : inject_Z n < x  <->  (n < ceiling x)%Z.
Proof.
  rewrite Z.lt_nge; rewrite Qlt_nge; apply negate_iff; apply ceiling_spec.
Qed.


Lemma ceiling_spec_alt (x : Q) (n : Z) :
  n = ceiling x  <->  inject_Z n - 1 < x /\ x <= inject_Z n.
Proof.
  replace (inject_Z n - 1) with (inject_Z (n - 1)) by (
    unfold Z.sub; rewrite inject_Z_plus; auto);
  split; intro;
  [
    split; [apply ceiling_spec_lt | apply ceiling_spec]; auto with zarith
  |
    apply Z.le_antisymm;
    [ apply Z.lt_pred_le; apply ceiling_spec_lt | apply ceiling_spec]; tauto
  ].
Qed.


Lemma ceiling_inject (n : Z) : ceiling (inject_Z n) = n.
Proof.
  apply Z.le_antisymm; [ | rewrite Zle_Qle]; apply ceiling_spec;
  [auto with qarith | auto with zarith].
Qed.


Lemma ceiling_monotonic (q r : Q) : q <= r  ->  (ceiling q <= ceiling r)%Z.
Proof.
  intro; apply ceiling_spec; apply Qle_trans with (y := r);
  [ easy | apply ceiling_spec; apply Z.le_refl].
Qed.


Lemma neg_ceiling_is_floor_neg (q : Q) : (- ceiling q)%Z = floor (-q).
Proof.
  apply Z.opp_involutive.
Qed.

Lemma neg_floor_is_ceiling_neg (q : Q) : (- floor q)%Z = ceiling (-q).
Proof.
  unfold ceiling; now rewrite Qopp_opp.
Qed.


Lemma floor_ceiling_bound (q : Q) : (ceiling q <= floor q + 1)%Z.
Proof.
  apply ceiling_spec; apply Qlt_le_weak; apply floor_spec_lt;
  apply Zle_lt_succ; apply Z.le_refl.
Qed.

Lemma floor_le_ceiling (q : Q) : (floor q <= ceiling q)%Z.
Proof.
  rewrite Zle_Qle; apply Qle_trans with (y := q);
  [apply floor_spec | apply ceiling_spec]; apply Zle_refl.
Qed.


Definition is_integer (q : Q) : Prop :=
  exists n : Z, inject_Z n == q.

Add Morphism is_integer : is_integer_morphism.
Proof.
  unfold is_integer; split; intro H0; destruct H0 as [z H0]; exists z;
    now rewrite H0.
Qed.

Lemma is_integer_inject_Z (x : Z) : is_integer (inject_Z x).
Proof.
  now exists x.
Qed.

Lemma is_integer_neg (x : Q) : is_integer x -> is_integer (-x).
Proof.
  unfold is_integer; intro H; destruct H as [y H0]; exists (-y)%Z;
  rewrite inject_Z_opp; now rewrite H0.
Qed.

Lemma is_integer_add (x y : Q) :
  is_integer x -> is_integer y -> is_integer (x + y).
Proof.
  unfold is_integer; intros x_int y_int; destruct x_int as [x0 x_int];
  destruct y_int as [y0 y_int]; exists (x0 + y0)%Z; rewrite inject_Z_plus;
  rewrite x_int; now rewrite y_int.
Qed.

Lemma is_integer_sub (x y : Q) :
  is_integer x -> is_integer y -> is_integer (x - y).
Proof.
  intros; apply is_integer_add; [ | apply is_integer_neg]; easy.
Qed.

Lemma is_integer_mul (x y : Q) :
  is_integer x -> is_integer y -> is_integer (x * y).
Proof.
  unfold is_integer; intros x_int y_int; destruct x_int as [x0 x_int];
  destruct y_int as [y0 y_int]; exists (x0 * y0)%Z; rewrite inject_Z_mult;
  rewrite x_int; now rewrite y_int.
Qed.

Lemma floor_integer (q : Q) : is_integer q <-> inject_Z (floor q) == q.
Proof.
  unfold is_integer; split; intro H;
  [destruct H as [n H]; rewrite <- H; now rewrite floor_inject |
  now exists (floor q) ].
Qed.

Lemma integer_le_floor (x y : Q) :
  is_integer x -> x <= y -> x <= inject_Z (floor y).
Proof.
  unfold is_integer; intro H; destruct H as [m H]; rewrite <- H;
  intro; rewrite <- Zle_Qle; now apply floor_spec.
Qed.

Lemma integer_le_ceiling (x y : Q) :
  is_integer y -> x <= y -> inject_Z (ceiling x) <= y.
Proof.
  unfold is_integer; destruct 1 as [m H]; rewrite <- H; intro;
  rewrite <- Zle_Qle; now apply ceiling_spec.
Qed.


Lemma ceiling_integer (q : Q) : is_integer q <-> inject_Z (ceiling q) == q.
Proof.
  unfold is_integer; split; intro H;
  [destruct H as [n H]; rewrite <- H; now rewrite ceiling_inject |
  now exists (ceiling q)].
Qed.

(* As a corollary of the above characterization of is_integer in terms of an
   equality, is_integer is decidable. *)

Lemma is_integer_is_decidable (q : Q) : is_integer q  \/  ~is_integer q.
Proof.
  destruct (Qeq_dec (inject_Z (floor q)) q) as [equal | notequal];
  [left | right; contradict notequal]; now apply floor_integer.
Qed.


Lemma floor_eq_ceiling (q : Q) :
  (floor q = ceiling q)%Z -> is_integer q.
Proof.
  intro; apply floor_integer; apply Qle_antisym;
  [apply floor_spec | rewrite H ; apply ceiling_spec]; apply Zle_refl.
Qed.


Lemma floor_ceiling_gap (q : Q) :
  ~(is_integer q) -> (ceiling q = floor q + 1)%Z.
Proof.
  intro q_is_integer; apply Z.le_antisymm; [
  apply floor_ceiling_bound |
  apply Z.le_succ_l; apply Zle_not_eq; [ apply floor_le_ceiling |
  contradict q_is_integer; now apply floor_eq_ceiling]].
Qed.


Lemma floor_ceiling_gap_Q (q : Q) :
  ~is_integer q -> inject_Z (ceiling q) == inject_Z (floor q) + 1.
Proof.
  intro; replace 1 with (inject_Z 1) by reflexivity;
  rewrite <- inject_Z_plus; apply inject_Z_injective;
  now apply floor_ceiling_gap.
Qed.

(* Results about floor, ceiling and absolute value. *)

Lemma abs_floor_le (x : Q) (m : Z) :
  Qabs x <= inject_Z m  ->  (Z.abs (floor x) <= m)%Z.
Proof.
  intro abs_x_le_m; apply Z.abs_case; [
    solve_proper |
    (* Proving floor x <= m. *)
    rewrite Zle_Qle; apply Qle_trans with (y := x); [
      apply floor_spec, Zle_refl |
      now apply Qabs_Qle_condition ]
    |
    (* Proving - floor x <= m. *)
    rewrite neg_floor_is_ceiling_neg; apply ceiling_spec, Qabs_Qle_condition;
    now rewrite Qabs_opp
  ].
Qed.

Lemma abs_ceiling_le (x : Q) (m : Z) :
  Qabs x <= inject_Z m  ->  (Z.abs (ceiling x) <= m)%Z.
Proof.
  setoid_replace x with (- - x) by ring;
  rewrite Qabs_opp; rewrite <- neg_floor_is_ceiling_neg;
  rewrite Z.abs_opp; apply abs_floor_le.
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
  setoid_replace (inject_Z (floor q)) with (q - (1 # 2)) by (
    rewrite <- H; ring); ring.
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
    apply Qlt_le_weak; apply Qneg_le; apply Qplus_lt_l with (z := 1);
      now ring_simplify.
Qed.


Lemma round_floor_or_ceiling : forall q,
  round q = floor q  \/  round q = ceiling q.
Proof.
  intro q; unfold round; destruct (Qcompare (q - inject_Z (floor q)) (1 # 2));
  destruct (Z.even (floor q)); tauto.
Qed.


Lemma round_le_integer (n : Q) (q : Q) :
  is_integer n  ->  q <= n  ->  inject_Z (round q) <= n.
Proof.
  destruct (round_floor_or_ceiling q) as [H | H]; rewrite H; intros.
  - apply Qle_trans with (2 := H1).
    apply floor_spec. apply Z.le_refl.
  - now apply integer_le_ceiling.
Qed.

Lemma integer_le_round (n : Q) (q : Q) :
  is_integer n  ->  n <= q  -> n <= inject_Z (round q).
Proof.
  destruct (round_floor_or_ceiling q) as [H | H]; rewrite H; intros.
  - now apply integer_le_floor.
  - apply Qle_trans with (1 := H1); apply ceiling_spec, Z.le_refl.
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

Lemma Qabs_floor_le x y :
  is_integer y  ->  Qabs x <= y  ->  Qabs (inject_Z (floor x)) <= y.
Proof.
  destruct 1 as [m m_eq_y]; rewrite <- m_eq_y;
  rewrite Qabs_Zabs; rewrite <- Zle_Qle; apply abs_floor_le.
Qed.

Lemma Qabs_ceiling_le x y :
  is_integer y  ->  Qabs x <= y  ->  Qabs (inject_Z (ceiling x)) <= y.
Proof.
  destruct 1 as [m m_eq_y]; rewrite <- m_eq_y; 
  rewrite Qabs_Zabs; rewrite <- Zle_Qle; apply abs_ceiling_le.
Qed.

Lemma Qabs_round_le x y :
  is_integer y  ->  Qabs x <= y  ->  Qabs (inject_Z (round x)) <= y.
Proof.
  intros;
  destruct (round_floor_or_ceiling x) as [Hfloor | Hceiling].
  - rewrite Hfloor; now apply Qabs_floor_le.
  - rewrite Hceiling; now apply Qabs_ceiling_le.
Qed.