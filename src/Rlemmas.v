Require Import Rbase Reals QArith micromega.Lia micromega.Lra.

Import RinvImpl.

Local Open Scope R.
Local Coercion INR : nat >-> R.

Lemma inv0 : / 0 = 0.
  rewrite Rinv_def.
  destruct (Req_appart_dec 0 R0). reflexivity.
  destruct o; pose proof (Rlt_irrefl R0); contradiction. Qed.

Lemma Rinv_pos_nonneg c : 0 < c -> 0 < / c.
Proof.
  intros. replace (/ c) with (1 * (/ c)) by lra.
  apply Rlt_mult_inv_pos; lra. Qed.

Lemma Rinv_neg_nonpos c : c < 0 -> / c < 0.
Proof.
  intros. replace (/ c) with (-(1 * (/ (-c)))).
  replace 0 with (- 0) by lra.
  apply Ropp_lt_contravar.
  apply Rlt_mult_inv_pos. lra. lra. rewrite <- Ropp_inv_permute. lra. lra. Qed.

Lemma inv_pos c : 0 <= c -> 0 <= / c.
Proof.
  destruct (Req_dec c 0); [subst; rewrite inv0; lra|].
  intros; apply Rlt_le. pose proof Rinv_pos_nonneg c. lra. Qed.

Lemma inv_neg c : c <= 0 -> / c <= 0.
  destruct (Req_dec c 0); [subst; rewrite inv0; lra|].
  intros; apply Rlt_le. pose proof Rinv_neg_nonpos c. lra. Qed.

Lemma Rle_div_r a b c : 0 < c ->  a <= b / c <-> c * a <= b.
Proof.
  split; intros.
  replace b with (c * (b / c)) by (field; lra).
  apply Rmult_le_compat_l; lra.
  apply (Rmult_le_compat_r (/ c)) in H0.
  field_simplify in H0; lra.
  left. apply Rinv_pos_nonneg; assumption. Qed.

Lemma Rle_div_l a b c : 0 < b -> a / b <= c <-> a <= b * c.
Proof.
  split; intros.
  replace a with (b * (a / b)) by (field; lra).
  apply Rmult_le_compat_l; lra.
  apply (Rmult_le_compat_r (/ b)) in H0.
  field_simplify in H0; lra.
  left. apply Rinv_pos_nonneg; assumption. Qed.

Lemma Rmult_le_compat_neg_r: forall r r1 r2 : R, r <= 0 -> r1 <= r2 -> r2 * r <= r1 * r.
Proof. intros. nra. Qed.

Lemma Rle_div_neg_r a b c : c < 0 ->  a <= b / c <-> b <= c * a.
Proof.
  split; intros.
  replace b with (c * (b / c)) by (field; lra).
  apply Rmult_le_compat_neg_l; lra.
  apply (Rmult_le_compat_neg_r (/ c)) in H0.
  field_simplify in H0; lra.
  left. apply Rinv_neg_nonpos; assumption. Qed.

Lemma Rle_div_neg_l a b c : b < 0 -> a / b <= c <-> b * c <= a.
Proof.
  split; intros.
  replace a with (b * (a / b)) by (field; lra).
  apply Rmult_le_compat_neg_l; lra.
  apply (Rmult_le_compat_neg_r (/ b)) in H0.
  field_simplify in H0; lra.
  left. apply Rinv_neg_nonpos; assumption. Qed.

Lemma eq_div a b c : c <> 0 -> a / c = b <-> a = b * c.
Proof.
  split; intros; subst; field; assumption. Qed.

Lemma le_pow (n : nat) a b (Hn : (0 < n)%nat) : a ^ n <= b ^ n -> a <= Rabs b.
Proof.
  destruct (Rle_lt_dec a 0) as [Ha|Ha]; intros.
  - eapply Rle_trans. apply Ha. apply Rabs_pos.
  - assert (0 < a ^ n) by (apply pow_lt; assumption).
    destruct (Req_EM_T b 0).
    + subst. rewrite pow_i in H. lra. lia.
    +
      apply lt_INR in Hn. replace (INR 0) with (IZR 0) in Hn by reflexivity.
      apply Rabs_no_R0 in n0.
      pose proof (Rabs_pos b).
      assert (0 < Rabs b) by lra.
      rewrite <- (Rabs_pos_eq (b ^ _)) in H by lra.
      rewrite <- RPow_abs in H.
      rewrite <- (Rpower_1 a), <- Rpower_1 by assumption.
      replace 1 with (n * / n) by (field; lra).
      rewrite <- !Rpower_mult.
      apply Rle_Rpower_l. apply Rlt_le, Rinv_pos_nonneg. lra.
      rewrite !Rpower_pow by lra. lra. Qed.

Lemma lt_pow (n : nat) a b (Hn : 0 < n) : a ^ n < b ^ n -> a < Rabs b.
Proof.
  destruct (Rlt_dec a 0) as [Ha|Ha]; intros.
  - eapply Rlt_le_trans. apply Ha. apply Rabs_pos.
  - assert (0 <= a ^ n) by (apply pow_le; lra).
    destruct (Req_EM_T b 0).
    + subst. rewrite pow_i in H. lra. apply INR_lt. replace (INR 0%nat) with 0 by reflexivity. assumption.
    + apply Rabs_no_R0 in n0.
      pose proof (Rabs_pos b).
      assert (0 < Rabs b) by lra.
      rewrite <- (Rabs_pos_eq (b ^ _)) in H by lra.
      rewrite <- RPow_abs in H.
      destruct (Req_dec 0 a).
      * subst. assumption.
      * rewrite <- (Rpower_1 a), <- Rpower_1 by lra.
        replace 1 with (n * / n) by (field; lra).
        rewrite <- !Rpower_mult.
        apply Rlt_Rpower_l. apply Rinv_pos_nonneg; assumption.
        rewrite !Rpower_pow by lra. split. apply pow_lt. lra.
        lra. Qed.

Lemma mult_pow2 x : x * x = x ^ 2.
Proof. field. Qed.

Lemma div_mul_inv x y : x / y = x * / y.
Proof. reflexivity. Qed.

Lemma pow_div a b n (Hb : b <> 0) : (a / b) ^ n = (a ^ n) / (b ^ n).
Proof. rewrite !div_mul_inv, Rpow_mult_distr, Rinv_pow; lra. Qed.

Lemma minus_add_distr a b c : a - (b + c) = a - b - c.
Proof. field. Qed.

Lemma minus_diag a : a - a = 0.
Proof. field. Qed.

Lemma Rabs_0 a : Rabs a = 0 -> a = 0.
Proof.
  intros. destruct (Rle_dec 0 a).
  apply Rabs_pos_eq in r. lra.
  apply Rnot_le_gt in n. rewrite Rabs_left in H. lra. lra. Qed.

Lemma pow_maj_Rabs_lt x y (n : nat) (Hn : (0 < n)%nat) : Rabs y < x -> y ^ n < x ^ n.
Proof.
  intros.
  pose proof pow_maj_Rabs x y n ltac:(lra).
  assert (Rabsy : 0 <= Rabs y) by (apply Rabs_pos).
  destruct (Rle_lt_or_eq_dec _ _ H0); [assumption|].
  destruct (Req_EM_T (Rabs y) 0).
  - apply Rabs_0 in e0. subst. rewrite Rabs_R0 in H.
    assert (x <> 0) by lra. apply (pow_nonzero _ n) in H1.
    rewrite pow_i in e. lra. assumption.
  - apply (f_equal Rabs) in e.
    rewrite <- !RPow_abs in e.
    rewrite (Rabs_pos_eq x) in e.
    apply (f_equal (fun a => Rpower a (/ n))) in e.
    rewrite <- !Rpower_pow in e.
    rewrite !Rpower_mult in e.
    rewrite Rinv_r in e.
    rewrite !Rpower_1 in e. lra.
    lra. lra. apply not_0_INR. lia.
    lra. lra. lra. Qed.

Lemma div_pow_inv a b c (Ha : 0 < a) (Hbc : (b <= c)%nat) : a ^ b / a ^ c = / a ^ (c - b).
Proof.
  rewrite <- !Rpower_pow, div_mul_inv, <- !Rpower_Ropp, <- Rpower_plus, minus_INR by assumption.
  apply f_equal2; lra. Qed.

Lemma div_pow a b c (Ha : 0 < a) (Hbc : (c <= b)%nat) : a ^ b / a ^ c = a ^ (b - c).
Proof.
  rewrite <- !Rpower_pow, div_mul_inv, <- Rpower_Ropp, <- Rpower_plus, minus_INR by assumption. reflexivity. Qed.

Lemma inv_mul a b (Ha : a <> 0) (Hb : b <> 0) : / (a * b) = / a * / b.
Proof. field; auto. Qed.

Lemma div_0_r a : a / 0 = 0.
  now unfold Rdiv; rewrite inv0, Rmult_0_r. Qed.
Lemma div_0_l a : 0 / a = 0.
  now unfold Rdiv; rewrite Rmult_0_l. Qed.

Lemma div_pos_pos a b : 0 <= a -> 0 <= b -> 0 <= a / b.
Proof. destruct (Req_dec b 0); [subst; rewrite div_0_r; lra|].
       intros; rewrite div_mul_inv; apply Rle_mult_inv_pos; lra. Qed.

Lemma div_neg_pos a b : a <= 0 -> b <= 0 -> 0 <= a / b.
Proof. destruct (Req_dec b 0); [subst; rewrite div_0_r; lra|].
       intros; rewrite div_mul_inv. pose proof inv_neg b H1. nra. Qed.

Lemma div_pos_nonneg a b : (0 < a -> 0 < b -> 0 < a / b).
Proof. apply Rdiv_lt_0_compat. Qed.

Lemma div_neg_nonneg a b : (a < 0 -> b < 0 -> 0 < a / b).
Proof. intros Ha Hb. pose proof Rinv_neg_nonpos b Hb. rewrite div_mul_inv. nra. Qed.

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
Proof. replace 32 with (4 ^ 2 * 2) by lra.
       rewrite sqrt_mult_alt.
       rewrite sqrt_pow2; lra. apply pow_le. lra. Qed.

Lemma inv_pos' c : 0 <= c -> 0 <= / c.
Proof.
  destruct (Req_dec c 0). rewrite H. rewrite inv0; lra.
  intros; apply Rlt_le; apply Rinv_pos_nonneg; lra. Qed.

Lemma Rle_div a b c : 0 <= c -> a <= b -> a / c <= b / c.
Proof. intros. apply Rmult_le_compat_r. apply inv_pos'. assumption. assumption. Qed.

Lemma Rlt_div a b c : 0 < c -> a < b -> a / c < b / c.
Proof.
  intros. apply Rmult_lt_compat_r. apply Rinv_pos_nonneg. assumption. assumption. Qed.
