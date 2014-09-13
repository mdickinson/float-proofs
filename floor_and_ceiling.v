Section floor_and_ceiling.

Require Import ZArith.

Open Scope Z_scope.

Lemma floor_spec_Z : forall a b n,
    (0 < b) -> ((n * b <= a)%Z <-> (n <= a / b)%Z).
Proof.
(* Eliminate the integer division. *)
intros a b n b_is_positive. unfold Zdiv.

(* Introduce the facts we need about Euclidean division as hypotheses. *)
assert (b <> 0) as b_is_nonzero by auto with zarith.
pose proof (Z.div_eucl_eq a b b_is_nonzero) as a_eq_bqr. clear b_is_nonzero.
pose proof (Z.mod_pos_bound a b b_is_positive) as r_bounded.
unfold Z.modulo in r_bounded. elim r_bounded.
intros r_nonnegative r_less_than_b. clear r_bounded.

(* Introduce terms to eliminate the let constructs. *)
remember (Z.div_eucl a b) as qr.
rewrite (surjective_pairing qr) in *. clear Heqqr.
remember (fst qr) as q. remember (snd qr) as r. clear Heqq. clear Heqr.
clear qr. rewrite a_eq_bqr. clear a a_eq_bqr.

(* fix mismatch between b * q and n * b *)

(* Now split our double implication n * b <= a <-> n <= q into
   two pieces, and prove each piece separately. *)
split; intro H0.

(* Prove that n <= q, given n * b <= a. *)
assert (n < q + 1).
apply Zmult_lt_reg_r with (p := b). assumption.
apply Zle_lt_trans with (m := b * q + r). assumption.
replace ((q + 1) * b) with (b * q + b) by ring.
auto with zarith. auto with zarith.

apply Zle_trans with (m := q * b).
auto with zarith. rewrite Zmult_comm. auto with zarith.
Qed.


Require Import QArith.

(* Define the floor function, and prove its characteristic property. *)
Definition floor (x : Q) : Z := (Qnum x / ' Qden x)%Z.

(* Three distinct characterisations of the floor function. *)

Lemma floor_spec : forall (x:Q) (n:Z),
    inject_Z n <= x  <->  (n <= floor x)%Z.
Proof.
intros.
(* Unfold as far as a statement in Z. *)
unfold inject_Z. unfold floor. unfold Qle. simpl.
rewrite Z.mul_1_r.
generalize (Qnum x) as a. intro a.
generalize (Qden x) as b. intro b.
apply floor_spec_Z. auto with zarith.
Qed.

Lemma floor_spec_lt : forall (x:Q) (n:Z),
    x < inject_Z n  <->  (floor x < n)%Z.
Proof.
  intros x n.
  pose proof (floor_spec x n).
  assert (x < (inject_Z n) <-> not ((inject_Z n) <= x)) by (split; auto with qarith).
  assert ((floor x) < n <-> not (n <= (floor x)))%Z by (split; auto with zarith).
  tauto.
Qed.

Lemma floor_spec_alt : forall (x:Q) (n:Z),
    n = floor x  <->  inject_Z n <= x /\ x < inject_Z n + 1.
Proof.
  intros x n.
  assert (inject_Z n + 1 = inject_Z (n + 1)).
  rewrite inject_Z_plus. auto with qarith.
  rewrite H. clear H.

  split; intro.
    split. apply floor_spec. auto with zarith.
    apply floor_spec_lt. auto with zarith.

    elim H. intros.
    assert (n <= floor x)%Z by (apply floor_spec; assumption).
    assert (floor x < n + 1)%Z by (apply floor_spec_lt; assumption).
    omega.
Qed.


(* Define the ceiling function, and prove its characteristic property. *)
Definition ceiling (x : Q) : Z := (-floor(-x))%Z.

Lemma ceiling_spec : forall (x:Q) (n:Z),
    x <= inject_Z n  <->  (ceiling x <= n)%Z.
Proof.
intros. unfold ceiling.

assert (x <= inject_Z n <-> -inject_Z n <= -x).
generalize (inject_Z n) as y. intros. clear n.
unfold Qopp. unfold Qle. simpl.
generalize (Qnum x) as a. generalize (Zpos (Qden x)) as b.
generalize (Qnum y) as c. generalize (Zpos (Qden y)) as d.
intros.
assert (-c * b = -(c * b))%Z by apply Z.mul_opp_l. rewrite H. clear H.
assert (-a * d = -(a * d))%Z by apply Z.mul_opp_l. rewrite H. clear H.
generalize (a * d)%Z as ad. generalize (c * b)%Z as bc.
intros. split; auto with zarith. rewrite H. clear H.

assert (-floor(-x) <= n <-> -n <= floor(-x))%Z.
rewrite (eq_sym (Z.opp_involutive (floor (-x)))) at 2.
apply Z.opp_le_mono. rewrite H. clear H.
apply floor_spec.
Qed.

End floor_and_ceiling.
