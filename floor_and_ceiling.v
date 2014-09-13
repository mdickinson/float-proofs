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
clear qr.

(* fix mismatch between b * q and n * b *)
replace (b * q) with (q * b) in a_eq_bqr by auto with zarith.

(* Now split our double implication n * b <= a <-> n <= q into
   two pieces, and prove each piece separately. *)
split; intro H0.

(* Prove that n <= q, given n * b <= a. *)
assert (n < q + 1 -> n <= q) as H2 by auto with zarith. apply H2. clear H2.
assert (n * b < q * b + b) as H1 by auto with zarith.
replace (q * b + b) with ((q + 1) * b) in H1 by ring.
apply (Z.mul_lt_mono_pos_r _ _ _ b_is_positive). assumption.

(* Prove that n * b <= a, given n <= q. *)
rewrite a_eq_bqr. clear a_eq_bqr.
assert (q * b <= q * b + r). auto with zarith.
assert (n * b <= q * b). apply Z.mul_le_mono_pos_r. assumption. assumption.
auto with zarith.
Qed.

(* Defining property. *)

Require Import QArith.

(* Define the floor function, and prove its characteristic property. *)
Definition floor (x : Q) : Z := (Qnum x / ' Qden x)%Z.

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
