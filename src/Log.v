Require Import Rbase Reals QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

From BY Require Import Rlemmas.

Local Open Scope R.
Local Coercion INR : nat >-> R.

Definition log n x := ln x / ln n.

Lemma ln_le_inc a b : 0 < a <= b -> ln a <= ln b.
Proof. intros [H0 H1]; apply Rle_lt_or_eq_dec in H1. destruct H1.
       - apply Rlt_le; apply ln_increasing; assumption.
       - subst; intros; apply Rle_refl. Qed.

Lemma ln_gt_0 n (ngt1 : 1 < n) : 0 < ln n.
Proof. replace 0 with (ln 1) by apply ln_1; apply (ln_increasing); lra. Qed.

Lemma ln_ge_0 n (ngt1 : 1 <= n) : 0 <= ln n.
Proof. rewrite <- ln_1; apply ln_le_inc; lra. Qed.

Lemma ln_neq_0 n (npos : 0 < n) (nneq1 : n <> 1) : ln n <> 0.
Proof.
  destruct (Rle_dec 1 n).
  - assert (1 < n) by lra; pose proof ln_gt_0 _ H; lra.
  - assert (ln n < 0) by (replace 0 with (ln 1) by apply ln_1; apply ln_increasing; lra). lra. Qed.

Lemma log_pow_id n x (npos : 0 < n) (nneq1 : n <> 1) : log n (n ^ x) = x.
Proof.
  unfold log. replace n with (exp (ln n)). rewrite <- Rpower_pow. unfold Rpower. rewrite !ln_exp.
  field. apply ln_neq_0; assumption. rewrite exp_ln; assumption. apply exp_ln; assumption. Qed.

Lemma ln_0 : ln 0 = 0.
Proof. unfold ln; destruct (Rlt_dec 0 0); [exfalso|]; lra. Qed.

Lemma ln_neg x (xneg : x <= 0) : ln x = 0.
Proof. unfold ln; destruct (Rlt_dec 0 x); [exfalso|]; lra. Qed.

Lemma log_1 n : log n 1 = 0.
Proof. unfold log; rewrite ln_1; lra. Qed.

Lemma log_n_n n (npos : 0 < n) (nneq1 : n <> 1) : log n n = 1.
Proof. unfold log; field; apply ln_neq_0; assumption. Qed.

Lemma log_neg n x (xneg : x <= 0) : log n x = 0.
Proof. unfold log; rewrite ln_neg; lra. Qed.

Lemma log_mult n a b (apos : 0 < a) (bpos : 0 < b) : log n (a * b) = log n a + log n b.
Proof. unfold log; rewrite ln_mult by assumption; lra. Qed.

Lemma log_inv n a (apos : 0 < a) : log n (/ a) = - log n a.
Proof. unfold log; rewrite ln_Rinv; lra. Qed.

Lemma log_div n a b (apos : 0 < a) (bpos : 0 < b) : log n (a / b) = log n a - log n b.
Proof. unfold Rdiv; rewrite log_mult, log_inv by (try apply Rinv_pos_nonneg; lra); lra. Qed.

Lemma log_pow n a b (apos : 0 < a) : log n (a ^ b) = b * log n a.
Proof.
  unfold log. rewrite <- Rpower_pow by assumption.
  unfold Rpower. rewrite !ln_exp; lra. Qed.

Lemma Rpower_log n x (xgt0 : 0 < x) (npos : 0 < n) (nneq1 : 1 <> n) : Rpower n (log n x) = x.
Proof.
  unfold log. replace n with (exp (ln n)).
  unfold Rpower. rewrite !ln_exp. field_simplify (ln x / ln n * ln n).
  apply exp_ln. assumption. apply ln_neq_0; lra. apply exp_ln; lra. Qed.

Lemma log_Rpower n x (npos : 0 < n) (nneq1 : 1 <> n) : log n (Rpower n x) = x.
Proof.
  unfold log, Rpower. rewrite ln_exp. field.
  intros contra. replace 0 with (ln 1) in contra by (apply ln_1).
  apply ln_inv in contra; lra. Qed.

Lemma log_inc n a b (nge1 : 1 <= n) :
  0 < a <= b -> log n a <= log n b.
Proof.
  unfold log. intros. apply Rle_div. apply ln_ge_0. assumption.
  apply ln_le_inc. assumption. Qed.

Lemma log_lt n a b (ngt1 : 1 < n) : 0 < a < b -> log n a < log n b.
Proof.
  intros H. unfold log. apply Rlt_div. apply ln_gt_0. assumption.
  apply ln_increasing; apply H. Qed.

Lemma exp_le_inv a b : exp a <= exp b -> a <= b.
Proof.
  intros H; destruct (Rle_lt_or_eq_dec _ _ H).
  - apply exp_lt_inv in r; lra.
  - apply exp_inv in e; lra. Qed.

Lemma Rpower_pos_nonneg a b : 0 < Rpower a b.
Proof. unfold Rpower. apply exp_pos. Qed.

Lemma Rpower_pos a b : 0 <= Rpower a b.
Proof. apply Rlt_le; apply Rpower_pos_nonneg. Qed.

Lemma Rpower_le_inv n a b (ngt1 : 1 < n) : Rpower n a <= Rpower n b -> a <= b.
Proof.
  intros; unfold Rpower in H; apply exp_le_inv in H.
  assert (0 < ln n) by (apply ln_gt_0; assumption); nra. Qed.

Lemma Rpower_lt_inv n a b (nge1 : 1 <= n) : Rpower n a < Rpower n b -> a < b.
Proof.
  intros; unfold Rpower in H; apply exp_lt_inv in H.
  assert (0 <= ln n) by (apply ln_ge_0; assumption); nra. Qed.

Lemma log_lower_bound n a b (ngt1 : 1 < n) :
  Rpower n a < b -> a < log n b.
Proof.
  intros. destruct (Rle_dec b 0).
  - pose proof Rpower_pos_nonneg n a. lra.
  - replace b with (Rpower n (log n b)) in H. apply Rpower_lt_inv in H; [assumption|].
    lra. apply Rpower_log; lra. Qed.

Lemma log_le_lower_bound n a b (ngt1 : 1 < n) :
  Rpower n a <= b -> a <= log n b.
Proof.
  intros; destruct (Rle_dec b 0).
  - pose proof Rpower_pos_nonneg n a; lra.
  - replace b with (Rpower n (log n b)) in H.
    apply Rpower_le_inv in H; assumption. apply Rpower_log; lra. Qed.

Lemma log_upper_bound n a b (a_nonneg : 0 < a) (ngt1 : 1 < n) :
  a < Rpower n b -> log n a < b.
Proof. intros; rewrite <- (log_Rpower n b) by lra; apply log_lt; lra. Qed.

Lemma log_le_upper_bound n a b (a_nonneg : 0 < a) (ngt1 : 1 < n) :
  a <= Rpower n b -> log n a <= b.
Proof. intros; rewrite <- (log_Rpower n b) by lra; apply log_inc; lra. Qed.

Lemma log_pos n a (ngt1 : 1 <= n):
  1 <= a -> 0 <= log n a.
Proof. intros; apply div_pos_pos; apply ln_ge_0; lra. Qed.
