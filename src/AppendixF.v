Require Import ZArith.
Require Import List Bool Znumtheory Decidable.
Require Import Rbase Reals QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

From BY Require Import Rlemmas Tactics Matrix SetoidRewrite AppendixE IZR Zpower_nat Zlemmas BigOp Spectral.

Local Open Scope mat_scope.
Local Open Scope R.

Local Coercion INR : nat >-> R.
Local Coercion IZR : Z >-> R.
Local Coercion Q2R : Q >-> R.

Lemma pow2_IZR (a : Z) : (a <> 0)%Z -> 1 <= a ^ 2.
Proof.
  intros.
  pose proof one_IZR_lt1 a.
  destruct (Rle_dec 1 a). nra.
  destruct (Rle_dec a (-1)). nra.
  exfalso. apply H. apply H0. nra. Qed.

Lemma neq_0_IZR a : IZR a <> 0 -> (a <> 0)%Z.
Proof. intros H contra. apply H. rewrite contra. reflexivity. Qed.

Lemma F6 (v1 v2 : Z) :
  [ IZR v1 ; IZR v2 ] <> v0 -> 1 <= vec_norm [ IZR v1 ; IZR v2 ].
Proof.
  intros vnon0.
  apply vnonzero in vnon0.
  unfold vec_norm. rewrite <- Rabs_pos_eq by apply sqrt_pos.
  apply (le_pow 2). simpl; lra.
  field_simplify.

  destruct vnon0 as [H|H]; apply neq_0_IZR in H; apply pow2_IZR in H.
  rewrite pow2_sqrt. nra. nra.
  rewrite pow2_sqrt. nra. nra. Qed.

 Theorem F12 (P : mat) (N : R) :
  let '(P11, P12, P21, P22) := P in
  let a := P11 ^ 2 + P12 ^ 2 in
  let b := P11 * P21 + P12 * P22 in
  let c := P11 * P21 + P12 * P22 in
  let d := P21 ^ 2 + P22 ^ 2 in
  mat_norm P <= N <-> (0 <= N)
                     /\ a + d <= 2 * N ^ 2
                     /\ (a - d) ^ 2 + 4 * b ^ 2 <= (2 * N ^ 2 - a - d) ^ 2.
Proof.
  pose proof (mat_norm_nonneg P).
  destruct P as [[[P11 P12] P21] P22]. unfold mat_norm. assert_pow; assert_sqrt.
  split; intros.
  assert (0 <= N) by lra.
  rewrite <- (Rabs_pos_eq (sqrt _)) in H10 by lra.
  apply (pow_maj_Rabs _ _ 2) in H10.

  rewrite <- Rsqr_pow2, Rsqr_sqrt in H10.
  repeat split. lra. lra.
  apply sqrt_le_0. lra. lra.

  rewrite <- (Rsqr_pow2 (_ - _ - _)). rewrite sqrt_Rsqr.
  nra. lra. lra.

  destruct H10 as [H11 [H12 H13]].

  apply sqrt_le_1 in H13.
  rewrite <- (Rsqr_pow2 (_ - _ - _)) in H13. rewrite sqrt_Rsqr in H13.
  replace N with (Rabs N) by (apply Rabs_pos_eq; assumption).
  apply le_pow with (n := 2%nat). replace (INR 2%nat) with 2 by reflexivity. lra.

  rewrite <- Rsqr_pow2, Rsqr_sqrt. lra. lra. lra. lra. lra. Qed.

Definition M (e : nat) (q : Z) := [ 0 , 1 / (2 ^ e) ; - 1 / (2 ^ e) , q / (2 ^ (2 * e)) ].

Theorem F16 e q (qodd : Z.odd q = true) (qbound : 1 <= q <= 2 ^ (S e) - 1) :
  mat_norm (M e q) < (1 + sqrt 2) / (2 ^ e).
Proof.
  assert (q < 2 * 2 ^ e). rewrite <- tech_pow_Rmult in qbound. lra.
  assert (2 ^ e <> 0) by (apply pow_nonzero; lra).
  unfold mat_norm. simpl.
  rewrite !Rmult_0_l, !Rplus_0_l, !Rmult_1_r. rewrite Nat.add_0_r.
  replace (e + e)%nat with (2 * e)%nat by ring.
  rewrite !mult_pow2. rewrite Rpow_mult_distr, !pow_div, pow1, <- !pow_mult.
  replace ((-1) ^ 2) with 1 by lra.
  replace (2 * e * 2)%nat with (e * 4)%nat by ring.

  field_simplify (1 / 2 ^ (e * 2) * (q ^ 2 / 2 ^ (e * 4))).

  assert (q ^ 2 / (2 ^ (e * 4)) < 4 / 2 ^ (e * 2)).

  assert (q ^ 2 < 4 * 2 ^ (e * 2)).
  replace (4 * 2 ^ (e * 2)) with ((2 * 2 ^ e) ^ 2).
  apply pow_maj_Rabs_lt. simpl. lia.
  rewrite Rabs_pos_eq. lra. lra.
  rewrite pow_mult, Rpow_mult_distr. lra.

  (* split. apply div_pos. nra. apply pow_lt. lra. *)
  replace (4 / 2 ^ (e * 2)) with ((4 * 2 ^ (e * 2)) / (2 ^ (e * 4))).

  rewrite !div_mul_inv. apply Rmult_lt_compat_r.
  apply Rinv_pos_nonneg. apply pow_lt. lra. assumption.

  replace (4 * 2 ^ (e * 2) / 2 ^ (e * 4)) with (4 * (2 ^ (e * 2) / 2 ^ (e * 4))) by (field; try apply pow_nonzero; lra).
  rewrite div_pow_inv.
  replace (e * 4 - e * 2)%nat with (e * 2)%nat by lia. field. apply pow_nonzero; lra. lra. nia.

  rewrite minus_add_distr, minus_diag, Rminus_0_l.
  assert (((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4)))) <= 32 / 2 ^ (e * 4)).

  assert ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 < (4 / 2 ^ (e * 2)) ^ 2).
  apply pow_maj_Rabs_lt. lia. rewrite Rabs_Ropp.
  rewrite Rabs_pos_eq. (* unfold Rlt_pos in H1. *)
  lra. apply Rle_div_r.
  apply pow_lt. lra. rewrite Rmult_0_r. apply pow_le. lra.

  assert (4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))) <= 16 / 2 ^ (e * 4)).
  rewrite div_mul_inv. rewrite inv_mul. rewrite (Rmult_comm (/ _)). rewrite <- (Rmult_assoc (q ^ 2)).
  rewrite <- (div_mul_inv _ (2 ^ (e * 4))).

  transitivity (4 * ((4 / 2 ^ (e * 2)) * / 2 ^ (e * 2))). nra.
  field_simplify. rewrite <- pow_mult.
  replace (e * 2 * 2)%nat with (e * 4)%nat by lia. lra.
  apply pow_nonzero; lra.
  apply pow_nonzero; lra.
  apply pow_nonzero; lra.
  apply pow_nonzero; lra.

  (* assert (((4 / 2 ^ (e * 2)) ^ 2) + 16 / 2 ^ (e * 4) = 32 / 2 ^ (e * 4)). *)
  assert ((4 / 2 ^ (e * 2)) ^ 2 = 16 / 2 ^ (e * 4)).
  field_simplify. rewrite <- pow_mult.
  replace (e * 2 * 2)%nat with (e * 4)%nat by lia. lra.
  apply pow_nonzero; lra.
  apply pow_nonzero; lra.
  nra.

  (* etransitivity. *)

  (* apply sqrt_lt_1_alt. *)
  (* split.  *)

  assert (sqrt
    ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + q ^ 2 / 2 ^ (e * 4)) +
              sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))))) / 2) <
  sqrt
    ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
              sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))))) / 2)).
  apply sqrt_lt_1_alt. split.
  apply div_pos.
  repeat apply add_pos; try apply div_pos; try apply pow_lt; try apply pow_le; try lra.
  apply sqrt_positivity.

  apply add_pos. apply pow2_ge_0.
  repeat apply mul_pos; try lra.

  try apply div_pos; try apply pow_lt; try apply pow_le; try lra.

  apply inv_pos. rewrite <- pow_add. apply pow_lt. lra. lra. lra.

  apply (Rlt_le_trans _ _ _ H3).

  assert
  (sqrt
    ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
              sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))))) / 2) <=
    sqrt
    ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
             sqrt (32 / 2 ^ (e * 4))) / 2)).

  apply sqrt_le_1_alt. apply Rle_div_r. lra.
  replace (2 *
  ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
            sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))))) / 2)) with
  ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
            sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4)))))) by lra.
  apply Rplus_le_compat_l.
  apply sqrt_le_1_alt. assumption.

  apply (Rle_trans _ _ _ H4).
  replace (1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)))
    with (6 / 2 ^ (e * 2)) by lra.

  right.
  apply sqr_inj. apply sqrt_positivity. apply div_pos. apply add_pos. apply div_pos. lra.
  apply pow_lt. lra. apply sqrt_positivity. apply div_pos. lra. apply pow_lt. lra. lra.
  apply div_pos. apply add_pos. lra. apply sqrt_positivity. lra. apply pow_lt. lra.
  rewrite pow2_sqrt.

  apply eq_div. lra. rewrite sqrt_div.
  rewrite <- (Rpower_sqrt (2 ^ _)).
  rewrite <- (Rpower_pow (_ * 4) _).
  rewrite Rpower_mult.
  replace ((e * 4)%nat * / 2) with (INR (e * 2)).
  rewrite Rpower_pow.
  rewrite sqrt32.
  rewrite pow_div. rewrite <- pow_mult.
  rewrite <- Rdiv_plus_distr.
  replace ((1 + sqrt 2) ^ 2 / 2 ^ (e * 2) * 2) with
      ((2 * (1 + sqrt 2) ^ 2) / 2 ^ (e * 2)).
  apply f_equal2. field_simplify. rewrite pow2_sqrt. field. lra. reflexivity.
  field. apply pow_nonzero. lra. apply pow_nonzero. lra. lra.

  rewrite !mult_INR. simpl. lra. lra. apply pow_lt. lra. lra. apply pow_lt. lra.
  apply div_pos. apply add_pos. apply div_pos. lra. apply pow_lt. lra. apply sqrt_positivity. apply div_pos.
  lra. apply pow_lt. lra. lra.

  split. apply pow_nonzero. lra. apply pow_nonzero. lra. apply pow_nonzero. lra. apply pow_nonzero.
  lra. apply pow_nonzero. lra. Qed.

Definition Qmin a b := if Qle_bool a b then a else b.
Definition Qmin_list l : Q :=
  match l with
  | nil => 0
  | h :: t => fold_right Qmin h t
  end.

Definition alpha_high w : Q := (633/1024)^(Z.of_nat w).

Definition alpha (w : nat) : Q :=
  match w with
  | 0%nat => 1 | 1%nat => 1 | 2%nat => 689491/2^20 | 3%nat => 779411/2^21
  | 4%nat => 880833/2^22 | 5%nat => 165219/2^20 | 6%nat => 97723/2^20 | 7%nat => 882313/2^24
  | 8%nat => 306733/2^23 | 9%nat => 92045/2^22 | 10%nat => 439213/2^25 | 11%nat => 281681/2^25
  | 12%nat => 689007/2^27 | 13%nat => 824303/2^28 | 14%nat => 257817/2^27 | 15%nat => 634229/2^29
  | 16%nat => 386245/2^29 | 17%nat => 942951/2^31 | 18%nat => 583433/2^31 | 19%nat => 713653/2^32
  | 20%nat => 432891/2^32 | 21%nat => 133569/2^31 | 22%nat => 328293/2^33 | 23%nat => 800421/2^35
  | 24%nat => 489233/2^35 | 25%nat => 604059/2^36 | 26%nat => 738889/2^37 | 27%nat => 112215/2^35
  | 28%nat => 276775/2^37 | 29%nat => 84973/2^36 | 30%nat => 829297/2^40 | 31%nat => 253443/2^39
  | 32%nat => 625405/2^41 | 33%nat => 95625/2^39 | 34%nat => 465055/2^42 | 35%nat => 286567/2^42
  | 36%nat => 175951/2^42 | 37%nat => 858637/2^45 | 38%nat => 65647/2^42 | 39%nat => 40469/2^42
  | 40%nat => 24751/2^42 | 41%nat => 240917/2^46 | 42%nat => 593411/2^48 | 43%nat => 364337/2^48
  | 44%nat => 889015/2^50 | 45%nat => 543791/2^50 | 46%nat => 41899/2^47 | 47%nat => 205005/2^50
  | 48%nat => 997791/2^53 | 49%nat => 307191/2^52 | 50%nat => 754423/2^54 | 51%nat => 57527/2^51
  | 52%nat => 281515/2^54 | 53%nat => 694073/2^56 | 54%nat => 212249/2^55 | 55%nat => 258273/2^56
  | 56%nat => 636093/2^58 | 57%nat => 781081/2^59 | 58%nat => 952959/2^60 | 59%nat => 291475/2^59
  | 60%nat => 718599/2^61 | 61%nat => 878997/2^62 | 62%nat => 534821/2^62 | 63%nat => 329285/2^62
  | 64%nat => 404341/2^63 | 65%nat => 986633/2^65 | 66%nat => 603553/2^65 | w => alpha_high w
  end.

Fixpoint alpha_aux w :=
  match w with
  | 0%nat => nil
  | S n => alpha_aux n ++ (alpha_high w / alpha w)%Q :: nil
  end.

Fixpoint beta_aux w :=
  (fix beta_fix j :=
      match j with
      | 0%nat => nil
      | S i => beta_fix i ++ (alpha (w + i) / alpha i)%Q :: nil
      end) 68%nat.

Definition beta w := Qmin_list (beta_aux w).

Fixpoint gamma_aux w e :=
  (fix gamma_fix k :=
     match k with
     | 0%nat => nil
     | S i => gamma_fix i ++ ((beta (w + i + e)%nat) * (2 ^ (Z.of_nat (i + e))) * 70 / 169)%Q :: nil
     end) 68%nat.

Definition gamma w e := Qmin_list (gamma_aux w e).


(* the following theorem is the conclusion of the computational theorems F22 and F21 *)


Notation big_mmult_rev := (fun n f => @big_op_rev _ mmult I f 0 n).
Notation big_sum_rev := (fun n f => @big_op_rev _ Nat.add 0%nat f 0 n).

Lemma big_sum_bound n f :
  (forall i, (i <= n)%nat -> (1 <= f i)%nat) -> (n <= big_sum_rev n f)%nat.
Proof.
  intros.

  induction n.
  unfold big_op_rev. simpl. lia.

  assert (forall i : nat, i <= n -> 1 <= f i)%nat. intros; apply H. lia.
  apply IHn in H0.

  rewrite big_op_rev_S_l.
  assert (1 <= f n)%nat. apply H. lia. lia. lia. Qed.


Theorem F24 (j : nat) (e : nat -> nat) (q : nat -> Z) (Hq : forall i, (i <= j)%nat -> (Z.odd (q i) = true) /\ (1 <= q i < 2 ^+ (S (e i)))%Z) :
  mat_norm (big_mmult_rev j (fun i => M (e i) (q i))) <= Qreals.Q2R (alpha (big_sum_rev j e)).
Proof. Admitted.

Section __.

  Context {R0 R1 : Z}.

  Notation R_ := (R_ R0 R1).

  Notation e i := (ord2 (R_ (S i))).
  Notation q i := (q (split2 (R_ i)) (R_ (S i))).
  Definition M_ i := M (e i) (q i).

  Lemma E2_cor i (HR0 : R0 <> 0%Z) (H : R_ (S i) <> 0%Z) :
    [ IZR (split2 (R_ (S i))) ; IZR (R_ (S (S i))) ] =
    M (e i) (q i) *v [ IZR (split2 (R_ i)) ; IZR (R_ (S i))].
  Proof.
    unfold M. rewrite E2. unfold vmult. apply f_equal2. field. apply pow_nonzero. lra.
    apply f_equal2. reflexivity. apply f_equal2.

    unfold div_2. field_simplify. apply f_equal2. reflexivity.

    rewrite Zpower_nat_IZR. rewrite <- pow_add. apply f_equal2. lra. lia. apply pow_nonzero. lra.
    split. apply IZR_neq. apply Zpower_nat_nonzero. lia. apply pow_nonzero. lra. reflexivity.  assumption. assumption. Qed.

  Lemma E2_cor2 j (R0_odd : Z.odd R0 = true) (H : R_ (S j) <> 0%Z) :
    [ IZR (split2 (R_ j)) ; IZR (R_ (S j)) ] =
    (big_mmult_rev j (fun i => M (e i) (q i))) *v [ IZR R0 ; IZR R1].
  Proof.
    assert (R0_nonzero : R0 <> 0%Z) by (apply odd_nonzero; assumption).
    induction j.
    - simpl. apply f_equal2.
      rewrite split2_odd. field. assumption.
      field.
    - rewrite big_op_rev_S_l. 
      rewrite mmult_vmult.
      rewrite <- IHj.
      rewrite E2_cor. reflexivity.
      assumption. apply R_nonzero_S. assumption. assumption. apply R_nonzero_S. assumption. assumption. lia. Qed.

  Ltac assert_norm :=
    repeat match goal with
           | [ |- context[mat_norm ?a] ] => match goal with
                                          | [ _ : 0 <= mat_norm a |- _ ] => fail 1
                                          | [ |- _ ] =>
                                            assert (0 <= mat_norm a) by (apply mat_norm_nonneg)
                                          end
           | [ |- context[vec_norm ?a] ] => match goal with
                                          | [ _ : 0 <= vec_norm a |- _ ] => fail 1
                                          | [ |- _ ] =>
                                            assert (0 <= vec_norm a) by (apply vec_norm_nonneg)
                                          end
           end.

  Theorem F25 j (R0_odd : Z.odd R0 = true) (H : R_ (S j) <> 0%Z) :
    vec_norm [ IZR (split2 (R_ j)) ; IZR (R_ (S j)) ] <=
    (alpha (big_sum_rev j (fun i => e i))) * vec_norm [ IZR R0 ; IZR R1 ].
  Proof.
    rewrite E2_cor2. rewrite mat_norm_vmult.
    epose proof F24 j (fun i => e i) (fun i => q i) _.
    assert_norm. nra. assumption. assumption.

    Unshelve.
    intros.
    split.
    apply q_spec.
    apply odd_split2.
    apply (R_nonzero _ _ (S j)).
    apply odd_nonzero. assumption. assumption. lia.
    apply (R_nonzero _ _ (S j)).
    apply odd_nonzero. assumption. assumption. lia.
    apply q_spec.
    apply odd_split2.
    apply (R_nonzero _ _ (S j)).
    apply odd_nonzero. assumption. assumption. lia.
    apply (R_nonzero _ _ (S j)).
    apply odd_nonzero. assumption. assumption. lia. Qed.

  Definition log n x := ln x / ln n.

  Lemma ln_le_inc a b : 0 < a <= b -> ln a <= ln b.
  Proof.
    destruct (Req_dec a b). subst. lra. intros. apply Rlt_le. apply ln_increasing.  lra. lra. Qed.

  Lemma ln_gt_0 n (ngt1 : 1 < n) : 0 < ln n.
  Proof. replace 0 with (ln 1) by apply ln_1. apply (ln_increasing). lra. assumption. Qed.

  Lemma ln_ge_0 n (ngt1 : 1 <= n) : 0 <= ln n.
  Proof. rewrite <- ln_1. apply ln_le_inc. lra. Qed.

  Lemma ln_neq_0 n (npos : 0 < n) (nneq1 : n <> 1) : ln n <> 0.
  Proof.
    destruct (Rle_dec 1 n).
    assert (1 < n). lra. pose proof ln_gt_0 _ H. lra.

    assert (ln n < 0). replace 0 with (ln 1) by apply ln_1.
    apply ln_increasing. assumption. lra. lra. Qed.

  Lemma log_pow_id n x (npos : 0 < n) (nneq1 : n <> 1) : log n (n ^ x) = x.
  Proof.
    unfold log. replace n with (exp (ln n)).
    rewrite <- Rpower_pow. unfold Rpower.
    rewrite !ln_exp. field. apply ln_neq_0.  assumption. assumption.
    rewrite exp_ln. assumption. assumption. apply exp_ln. lra. Qed.

  Lemma ln_0 : ln 0 = 0.
  Proof. unfold ln; destruct (Rlt_dec 0 0); [exfalso|]; lra. Qed.

  Lemma ln_neg x (xneg : x <= 0) : ln x = 0.
  Proof. unfold ln; destruct (Rlt_dec 0 x); [exfalso|]; lra. Qed.

  Lemma log_1 n : log n 1 = 0.
  Proof. unfold log. rewrite ln_1. lra. Qed.

  Lemma log_n_n n (npos : 0 < n) (nneq1 : n <> 1) : log n n = 1.
  Proof. unfold log. field. apply ln_neq_0; assumption. Qed.

  Lemma log_neg n x (xneg : x <= 0) : log n x = 0.
  Proof.
    unfold log. rewrite ln_neg. lra. assumption. Qed.

  Lemma log_mult n a b (apos : 0 < a) (bpos : 0 < b) : log n (a * b) = log n a + log n b.
  Proof.
    unfold log. rewrite ln_mult by assumption. lra. Qed.

  Lemma log_inv n a (apos : 0 < a) : log n (/ a) = - log n a.
  Proof. unfold log. rewrite ln_Rinv. lra. assumption. Qed.

  Lemma log_div n a b (apos : 0 < a) (bpos : 0 < b) : log n (a / b) = log n a - log n b.
  Proof. unfold Rdiv. rewrite log_mult, log_inv. lra. assumption. assumption. apply Rinv_pos_nonneg. assumption. Qed.

  Lemma log_pow n a b (apos : 0 < a) : log n (a ^ b) = b * log n a.
  Proof.
    unfold log. rewrite <- Rpower_pow. unfold Rpower.
    rewrite !ln_exp. lra. assumption. Qed.

  Lemma Rpower_log n x (xgt0 : 0 < x) (ngt1 : 1 < n) : Rpower n (log n x) = x.
  Proof.
    unfold log. replace n with (exp (ln n)).
    unfold Rpower.
    rewrite !ln_exp. field_simplify (ln x / ln n * ln n).
    apply exp_ln.  assumption. apply ln_neq_0. lra. lra. apply exp_ln. lra. Qed.

  Lemma log_inc n a b (nge1 : 1 <= n) :
    0 < a <= b -> log n a <= log n b.
  Proof.
    unfold log.
    intros. apply Rle_div. apply ln_ge_0. assumption.
    apply ln_le_inc.  lra. Qed.

  Notation log_1024_633 := (log (1024 / 633)).

  Lemma alpha67 i : (67 <= i)%nat -> alpha i = alpha_high i.
  Proof. do 67 (destruct i as [|i]; [lia|]). reflexivity. Qed.

  Theorem F25_cor j (R0_odd : Z.odd R0 = true) (H : R_ (S j) <> 0%Z)
    : (67 <= big_sum_rev j (fun i => e i))%nat -> big_sum_rev j (fun i => e i) <= log_1024_633 (vec_norm [ IZR R0 ; IZR R1 ]).
  Proof.
    intros ineq; pose proof F25 j R0_odd H as F25'.
    rewrite alpha67 in F25' by assumption. unfold alpha_high in F25'.

    assert (1 <= vec_norm [ IZR (split2 (R_ j)) ; IZR (R_ (S j))]).
    apply F6. apply vnonzero. right. apply not_0_IZR. assumption.
    pose proof Rle_trans _ _ _ H0 F25'.
    assert (0 < 1 <= ((633 / 1024) ^ Z.of_nat (big_sum_rev j (fun i : nat => e i)))%Q * vec_norm (IZR R0, IZR R1)).
    lra.
    assert (1 <= 1024/633). nra.
    eapply (log_inc _ _ _ H3) in H2.

    rewrite log_1 in H2.
    rewrite log_mult in H2. Locate "^".
    rewrite RMicromega.Q2RpowerRZ in H2.
    rewrite <- pow_powerRZ in H2.
    rewrite log_pow in H2.
    rewrite Q2R_div in H2.
    replace (633%Q / 1024%Q) with (/ (1024 / 633)) in H2.
    rewrite log_inv in H2.
    rewrite log_n_n in H2. lra. lra. lra. lra. lra. Lqa.lra.
    rewrite Q2R_div. lra. Lqa.lra.

    left. intros contra. apply Qeq_eqR in contra. rewrite Q2R_div in contra. lra. Lqa.lra.
    rewrite RMicromega.Q2RpowerRZ.
    rewrite <- pow_powerRZ. apply pow_lt. rewrite Q2R_div. lra. Lqa.lra.
    left. intros contra. apply Qeq_eqR in contra. rewrite Q2R_div in contra. lra. Lqa.lra.

    assert ((IZR R0 , IZR R1) <> v0).
    apply vnonzero. left. apply not_0_IZR.  apply odd_nonzero. assumption.
    apply vnonzero_norm in H4.
    pose proof (vec_norm_nonneg (IZR R0, IZR R1)). lra. Qed.

  Lemma IZR_INR_lt z n : (Z.to_nat z <= n)%nat -> IZR z <= INR n.
  Proof. intros. rewrite INR_IZR_INZ. apply IZR_le. lia. Qed.

  Theorem F26 j
          (R0_odd : Z.odd R0 = true)
          (R1_even : Z.even R1 = true)
          (Hj : (max 67 (Z.to_nat (up (log_1024_633 (vec_norm (IZR R0, IZR R1))))) <= j)%nat) :
    (R_ (S j)) = 0%Z.
  Proof.
    destruct (Z.eq_dec (R_ (S j)) 0%Z).
    assumption.

    pose proof F25_cor _ (R0_odd) n.

    assert (j <= big_sum_rev j (fun i => e i))%nat.
    apply big_sum_bound.
    intros. apply e_ge_1. apply odd_nonzero. assumption. assumption.

    assert (67 <= big_sum_rev j (fun i => e i))%nat. lia.

    apply H in H1.

    assert (log_1024_633 (vec_norm (IZR R0, IZR R1)) < j).
    eapply Rlt_le_trans.
    apply archimed. apply IZR_INR_lt.
    etransitivity. shelve. apply Hj.
    apply le_INR in H0. lra.
    Unshelve. apply Max.le_max_r. Qed.

  Theorem F26_cor
          (R0_odd : Z.odd R0 = true)
          (R1_even : Z.even R1 = true) :
    exists j, (R_ j) = 0%Z.
  Proof. exists (S (max 67 (Z.to_nat (up (log_1024_633 (vec_norm (IZR R0, IZR R1))))))); apply F26; auto. Qed.
  
  Theorem F26_cor2
          (R0_odd : Z.odd R0 = true)
          (R1_even : Z.even R1 = true) :
    exists j, R_ j <> 0%Z /\ R_ (S j) = 0%Z.
  Proof. apply min. apply odd_nonzero; assumption. apply F26_cor; assumption. Qed.
End __.
Notation log_1024_633 := (log (1024 / 633)).
