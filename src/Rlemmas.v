Require Import Rbase Reals ZArith QArith micromega.Lia micromega.Lra.

From BY Require Import Zpower_nat.

Import RinvImpl.

Local Open Scope R.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion IZR : Z >-> R.

Lemma neq_IZR (a b : Z) : IZR a <> IZR b -> a <> b.
Proof. intros H contra; apply H; apply f_equal; assumption. Qed.

Lemma IZR_neq (a b : Z) : a <> b -> IZR a <> IZR b.
Proof. intros H contra; apply H; apply eq_IZR; assumption. Qed.

Lemma Zpower_nat_IZR a b : IZR (a ^+ b) = a ^ b.
Proof. now rewrite pow_IZR, Zpower_nat_Z. Qed.

Hint Rewrite <- plus_IZR mult_IZR minus_IZR opp_IZR Zpower_nat_IZR : pull_izr.
Hint Rewrite plus_IZR mult_IZR minus_IZR opp_IZR Zpower_nat_IZR : push_izr.

Lemma inv0 : / 0 = 0.
  rewrite Rinv_def. destruct (Req_appart_dec 0 R0).
  - reflexivity.
  - destruct o; pose proof (Rlt_irrefl R0); contradiction. Qed.

Lemma Rinv_pos_nonneg c : 0 < c -> 0 < / c.
Proof.
  intros. replace (/ c) with (1 * (/ c)) by lra.
  apply Rlt_mult_inv_pos; lra. Qed.

Lemma Rinv_neg_nonpos c : c < 0 -> / c < 0.
Proof.
  intros. replace (/ c) with (-(1 * (/ (-c)))) by (rewrite <- Ropp_inv_permute; lra).
  replace 0 with (- 0) by lra. apply Ropp_lt_contravar. apply Rlt_mult_inv_pos; lra. Qed.

Lemma inv_pos c : 0 <= c -> 0 <= / c.
Proof.
  destruct (Req_dec c 0); [subst; rewrite inv0; lra|].
  intros; apply Rlt_le. pose proof Rinv_pos_nonneg c; lra. Qed.

Lemma inv_neg c : c <= 0 -> / c <= 0.
  destruct (Req_dec c 0); [subst; rewrite inv0; lra|].
  intros; apply Rlt_le. pose proof Rinv_neg_nonpos c. lra. Qed.

Lemma Rle_div_r a b c : 0 < c ->  a <= b / c <-> c * a <= b.
Proof.
  split; intros.
  - replace b with (c * (b / c)) by (field; lra).
    apply Rmult_le_compat_l; lra.
  - apply (Rmult_le_compat_r (/ c)) in H0.
    field_simplify in H0; lra.
    left. apply Rinv_pos_nonneg; assumption. Qed.

Lemma Rlt_div_r a b c : 0 < c ->  a < b / c <-> c * a < b.
Proof.
  split; intros.
  - replace b with (c * (b / c)) by (field; lra).
    apply Rmult_lt_compat_l; lra.
  - apply (Rmult_lt_compat_r (/ c)) in H0.
    field_simplify in H0; lra.
    apply Rinv_pos_nonneg; assumption. Qed.

Lemma Rle_div_l a b c : 0 < b -> a / b <= c <-> a <= b * c.
Proof.
  split; intros.
  - replace a with (b * (a / b)) by (field; lra).
    apply Rmult_le_compat_l; lra.
  - apply (Rmult_le_compat_r (/ b)) in H0.
    field_simplify in H0; lra.
    left. apply Rinv_pos_nonneg; assumption. Qed.

Lemma Rlt_div_l a b c : 0 < b -> a / b < c <-> a < b * c.
Proof.
  split; intros.
  - replace a with (b * (a / b)) by (field; lra).
    apply Rmult_lt_compat_l; lra.
  - apply (Rmult_lt_compat_r (/ b)) in H0.
    field_simplify in H0; lra.
    apply Rinv_pos_nonneg; assumption. Qed.

Lemma Rmult_le_compat_neg_r: forall r r1 r2 : R, r <= 0 -> r1 <= r2 -> r2 * r <= r1 * r.
Proof. intros; nra. Qed.

Lemma Rle_div_neg_r a b c : c < 0 ->  a <= b / c <-> b <= c * a.
Proof.
  split; intros.
  - replace b with (c * (b / c)) by (field; lra).
    apply Rmult_le_compat_neg_l; lra.
  - apply (Rmult_le_compat_neg_r (/ c)) in H0.
    field_simplify in H0; lra.
    left. apply Rinv_neg_nonpos; assumption. Qed.

Lemma Rle_div_neg_l a b c : b < 0 -> a / b <= c <-> b * c <= a.
Proof.
  split; intros.
  - replace a with (b * (a / b)) by (field; lra).
    apply Rmult_le_compat_neg_l; lra.
  - apply (Rmult_le_compat_neg_r (/ b)) in H0.
    field_simplify in H0; lra.
    left. apply Rinv_neg_nonpos; assumption. Qed.

Lemma eq_div a b c : c <> 0 -> a / c = b <-> a = b * c.
Proof. split; intros; subst; field; assumption. Qed.

Ltac lira :=
  lra +
  (autorewrite with push_izr; try apply lt_IZR; lra) +
  (autorewrite with push_izr; try apply le_IZR; lra) +
  (autorewrite with pull_izr;
       try match goal with
       | [ |- IZR _ < IZR _ ] => try apply IZR_lt
       | [ |- IZR _ <= IZR _ ] => try apply IZR_le
       | [ |- IZR _ <> IZR _ ] => try apply IZR_neq
       end; lia).

Lemma Rpower_inj x y z : 0 < x -> 0 < y -> z <> 0 -> Rpower x z = Rpower y z -> x = y.
Proof.
  intros ? ? ? H. apply (f_equal (fun a => Rpower a (/ z))) in H.
  rewrite !Rpower_mult, Rinv_r, !Rpower_1 in H by assumption. exact H. Qed.

Lemma pow_zero x n : x ^ n = 0 -> x = 0.
Proof.
  intros. induction n; simpl in H.
  - apply R1_neq_R0 in H; contradiction.
  - apply Rmult_integral in H as []; [|apply IHn]; assumption. Qed.

Lemma Rmult_neg x y : x * y < 0 -> (x < 0 /\ 0 < y) \/ (0 < x /\ y < 0).
Proof. intros; destruct (Rlt_dec x 0); destruct (Rlt_dec y 0); nra. Qed.

Lemma pow_gt_zero x n : (0 < n)%nat -> 0 < x ^ n -> x <> 0.
Proof.
  intros H1 H2 contra. rewrite contra in H2. rewrite pow_i in H2 by assumption. lra. Qed.

Lemma pow_lt_zero x n : x ^ n < 0 -> x < 0.
Proof. intros. induction n. simpl in H. lra.
       simpl in *; apply Rmult_neg in H as []; tauto. Qed.

Lemma pow_Rabs_inj x y n : (0 < n)%nat -> x ^ n = y ^ n -> Rabs x = Rabs y.
Proof.
  intros H1 H2.
  destruct (Req_dec y 0) as [H3|]; [|destruct (Req_dec x 0) as [H3|]];
    subst; rewrite ?pow_ne_zero in H2; try apply pow_zero in H2; try (symmetry in H2; apply pow_zero in H2);
      try (subst; reflexivity); try lia.
  apply (f_equal Rabs) in H2. rewrite <- !RPow_abs in H2.
  rewrite <- !Rpower_pow in H2 by (apply Rabs_pos_lt; assumption).
  apply Rpower_inj with (z:=INR n); try apply Rabs_pos_lt; try (apply not_0_INR; lia); assumption. Qed.

Lemma lt_pow (n : nat) a b (Hn : (0 < n)%nat) : a ^ n < b ^ n -> a < Rabs b.
Proof.
  destruct (Rlt_dec a 0) as [Ha|Ha]; intros.
  - eapply Rlt_le_trans. apply Ha. apply Rabs_pos.
  - assert (0 <= a ^ n) by (apply pow_le; lra).
    destruct (Req_EM_T b 0).
    + subst; rewrite pow_i in H; lira.
    + apply Rabs_no_R0 in n0.
      assert (0 < Rabs b) by (pose proof (Rabs_pos b); lra).
      rewrite <- (Rabs_pos_eq (b ^ _)), <- RPow_abs in H by lra.
      destruct (Req_dec 0 a).
      * subst. assumption.
      * rewrite <- (Rpower_1 a), <- Rpower_1 by lra.
        replace 1 with (n * / n) by (field; lira).
        rewrite <- !Rpower_mult. apply Rlt_Rpower_l; [apply Rinv_pos_nonneg; lira|].
        rewrite <- INR_IZR_INZ, !Rpower_pow by lra. split; [apply pow_lt|]; lra. Qed.

Lemma le_pow (n : nat) a b (Hn : (0 < n)%nat) : a ^ n <= b ^ n -> a <= Rabs b.
Proof.
  intros. destruct H.
  - apply lt_pow in H. lra. assumption.
  - apply pow_Rabs_inj in H. rewrite <- H. apply Rle_abs. lia. Qed.

Lemma mult_pow2 x : x * x = x ^ 2.
Proof. field. Qed.

Lemma pow_div a b n (Hb : b <> 0) : (a / b) ^ n = (a ^ n) / (b ^ n).
Proof. unfold Rdiv; rewrite Rpow_mult_distr, Rinv_pow; lra. Qed.

Lemma minus_add_distr a b c : a - (b + c) = a - b - c.
Proof. field. Qed.

Lemma minus_diag a : a - a = 0.
Proof. field. Qed.

Lemma Rabs_0 a : Rabs a = 0 -> a = 0.
Proof. unfold Rabs; destruct (Rcase_abs a); lra. Qed.

Lemma pow_maj_Rabs_lt x y (n : nat) (Hn : (0 < n)%nat) : Rabs y < x -> y ^ n < x ^ n.
Proof.
  intros. pose proof pow_maj_Rabs x y n ltac:(lra).
  destruct (Rle_lt_or_eq_dec _ _ H0); [assumption|].
  apply pow_Rabs_inj in e. rewrite e in H. pose proof Rle_abs x. lra. assumption. Qed.

Lemma div_pow_inv a b c (Ha : 0 < a) (Hbc : (b <= c)%nat) : a ^ b / a ^ c = / a ^ (c - b).
Proof.
  unfold Rdiv; rewrite <- !Rpower_pow, <- !Rpower_Ropp, <- Rpower_plus, minus_INR by assumption.
  apply f_equal2; lra. Qed.

Lemma div_pow a b c (Ha : 0 < a) (Hbc : (c <= b)%nat) : a ^ b / a ^ c = a ^ (b - c).
Proof.
  unfold Rdiv; rewrite <- !Rpower_pow, <- Rpower_Ropp, <- Rpower_plus, minus_INR by assumption; reflexivity. Qed.

Lemma inv_mul a b (Ha : a <> 0) (Hb : b <> 0) : / (a * b) = / a * / b.
Proof. field; auto. Qed.

Lemma div_0_r a : a / 0 = 0.
  now unfold Rdiv; rewrite inv0, Rmult_0_r. Qed.

Lemma div_0_l a : 0 / a = 0.
  now unfold Rdiv; rewrite Rmult_0_l. Qed.

Lemma div_pos_pos a b : 0 <= a -> 0 <= b -> 0 <= a / b.
Proof. destruct (Req_dec b 0); [subst; rewrite div_0_r; lra|].
       intros; unfold Rdiv; apply Rle_mult_inv_pos; lra. Qed.

Lemma div_neg_pos a b : a <= 0 -> b <= 0 -> 0 <= a / b.
Proof. destruct (Req_dec b 0); [subst; rewrite div_0_r; lra|].
       intros; unfold Rdiv; pose proof inv_neg b H1; nra. Qed.

Lemma div_pos_nonneg a b : (0 < a -> 0 < b -> 0 < a / b).
Proof. apply Rdiv_lt_0_compat. Qed.

Lemma div_neg_nonneg a b : (a < 0 -> b < 0 -> 0 < a / b).
Proof. intros Ha Hb. pose proof Rinv_neg_nonpos b Hb. unfold Rdiv. nra. Qed.

Lemma add_pos a b : 0 <= a -> 0 <= b -> 0 <= a + b.
Proof. lra. Qed.

Lemma mul_pos a b : 0 <= a -> 0 <= b -> 0 <= a * b.
Proof. nra. Qed.

Lemma sqr_inj a b : 0 <= a -> 0 <= b -> a ^ 2 = b ^ 2 -> a = b.
Proof. intros; now rewrite <- sqrt_pow2, <- H1, sqrt_pow2. Qed.

Lemma pow2_sqrt a : 0 <= a -> (sqrt a) ^ 2 = a.
Proof.
  intros. now rewrite <- Rsqr_pow2, Rsqr_sqrt. Qed.

Lemma sqrt32 : sqrt 32 = 4 * sqrt 2.
Proof.
  replace 32 with (4 ^ 2 * 2) by lra.
  rewrite sqrt_mult_alt.
  rewrite sqrt_pow2; lra. apply pow_le. lra. Qed.

Lemma Rle_div a b c : 0 <= c -> a <= b -> a / c <= b / c.
Proof.
  intros; apply Rmult_le_compat_r; [apply inv_pos|]; assumption. Qed.

Lemma Rlt_div a b c : 0 < c -> a < b -> a / c < b / c.
Proof.
  intros; apply Rmult_lt_compat_r; [apply Rinv_pos_nonneg|]; assumption. Qed.

Lemma sqrt2_bound :
  sqrt 2 < 99 / 70.
Proof.
  rewrite <- Rabs_pos_eq.
  apply lt_pow with (n:=2%nat). lia.
  rewrite pow2_sqrt. lra. lra. lra. Qed.
