Require Import ZArith.
Require Import List Bool Znumtheory Decidable.
Require Import Rbase Reals QArith micromega.Lia micromega.Lra.

From BY Require Import Rlemmas Tactics Matrix SetoidRewrite.

Local Open Scope R.
Local Open Scope list_scope.

Local Coercion INR : nat >-> R.
Local Coercion IZR : Z >-> R.

Theorem F12 (P : matrix) (N : R) :
  let '(P11, P12, P21, P22) := P in
  let a := P11 ^ 2 + P12 ^ 2 in
  let b := P11 * P12 + P21 * P22 in
  let c := P11 * P12 + P21 * P22 in
  let d := P21 ^ 2 + P22 ^ 2 in  
  (norm P) <= N <-> (0 <= N)
                     /\ a + d <= 2 * N ^ 2
                     /\ (a - d) ^ 2 + 4 * b ^ 2 <= (2 * N ^ 2 - a - d) ^ 2.
Proof.
  pose proof (norm_nonneg P).
  destruct P as [[[P11 P12] P21] P22]. unfold norm. assert_pow; assert_sqrt.
  split; intros.
  assert (0 <= N) by lra.
  rewrite <- (Rabs_pos_eq (sqrt _)) in H10 by lra.
  apply (pow_maj_Rabs _ _ 2) in H10.

  rewrite <- Rsqr_pow2, Rsqr_sqrt in H10. 
  repeat split. lra. lra.
  apply sqrt_le_0. lra. lra. 
  
  rewrite <- (Rsqr_pow2 (_ - _ - _)). rewrite sqrt_Rsqr. lra. lra. lra.

  destruct H10 as [H11 [H12 H13]].

  apply sqrt_le_1 in H13. 
  rewrite <- (Rsqr_pow2 (_ - _ - _)) in H13. rewrite sqrt_Rsqr in H13.
  replace N with (Rabs N) by (apply Rabs_pos_eq; assumption).
  apply le_pow with (n := 2%nat). replace (INR 2%nat) with 2 by reflexivity. lra.

  rewrite <- Rsqr_pow2, Rsqr_sqrt. lra. lra. lra. lra. lra. Qed.

Definition M (e : nat) (q : Z) := [ 0 , 1 / (2 ^ e) ; - 1 / (2 ^ e) , q / (2 ^ (2 * e)) ].

Theorem F16 e q (qodd : Z.odd q = true) (qbound : 1 <= q <= 2 ^ (S e) - 1) :
  norm (M e q) < (1 + sqrt 2) / (2 ^ e).
Proof.
  assert (q < 2 * 2 ^ e). rewrite <- tech_pow_Rmult in qbound. lra. 
  assert (2 ^ e <> 0) by (apply pow_nonzero; lra).
  unfold norm. simpl.
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
  lra. apply Rle_div.
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
  
  apply sqrt_le_1_alt. apply Rle_div. lra.
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

Search _ (nat -> Z).

Import ListNotations.

Definition Qmin a b := if Qle_bool a b then a else b.
Definition Qmin_list l : Q :=
  match l with
  | [] => 0
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
  | 0%nat => []
  | S n => alpha_aux n ++ [alpha_high w / alpha w]%Q
  end.

Fixpoint beta_aux w :=
  (fix beta_fix j :=
      match j with
      | 0%nat => []
      | S i => beta_fix i ++ [alpha (w + i) / alpha i]%Q
      end) 68%nat.

Definition beta w := Qmin_list (beta_aux w).

Compute beta 50.

Fixpoint gamma_aux w e :=
  (fix gamma_fix k :=
     match k with
     | 0%nat => []
     | S i => gamma_fix i ++ [(beta (w + i + e)%nat) * (2 ^ (Z.of_nat (i + e))) * 70 / 169]%Q
     end) 68%nat.

Definition gamma w e := Qmin_list (gamma_aux w e).
Locate "+".

From mathcomp Require Import bigop.


(* the following theorem is the conclusion of the computational theorems F22 and F21 *)

Locate "\big".

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Theorem F24 (j : nat) (e : nat -> nat) (q : nat -> Z) (Hq : forall i, (Z.odd (q i) = true) /\ (1 <= q i <= 2 ^ ((e i) + 1) - 1)) :
  norm (\big[matmult / I]_(1 <= i < j) M (e i) (q i)) <= Qreals.Q2R (alpha (\big[Init.Nat.add / 0%nat]_(1 <= i < j) (e i))).
Proof. Admitted.
