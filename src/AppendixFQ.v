Require Import ZArith.
Require Import List Bool Znumtheory Decidable.
Require Import Rbase Reals QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

From BY Require Import Rlemmas Tactics Matrix SetoidRewrite AppendixE IZR Zpower_nat Zlemmas BigOp Spectral PadicVal Log InductionPrinciples BigOp AppendixF.

Definition alphaQ_high w : Q := (633/1024) ^ (Z.of_nat w).

Definition alphaQ (w : nat) : Q :=
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
  | 64%nat => 404341/2^63 | 65%nat => 986633/2^65 | 66%nat => 603553/2^65 | w => alphaQ_high w
  end.

Ltac for_each H :=
  match goal with
  | [ H: (?a <= ?b < ?c)%nat |- _ ] => destruct H as [ge lt];
                                  repeat
                                    let t := fresh in inversion ge as [eq|? t];
                                                      [subst; vm_compute; reflexivity|try lia; clear ge; rename t into ge]
  end.

Lemma alphaQ31 i : (31 <= i < 67)%nat -> ((alphaQ i) ^ 49 < 1 / (2 ^ ((34 * (Z.of_nat i) - 23))))%Q.
Proof. intros. Time for_each H. Qed.

Local Open Scope R.

Lemma Q2R_pow x n (H : (n <> 0)%nat) : (Q2R x) ^ n = Q2R (x ^ (Z.of_nat n)).
Proof. rewrite RMicromega.Q2RpowerRZ.
       rewrite pow_powerRZ. reflexivity. right. lia. Qed.

Lemma Q2R_pow' x n (H : (0 <= n)%Z) : (Q2R x) ^ (Z.abs_nat n) = Q2R (x ^ n).
Proof. rewrite RMicromega.Q2RpowerRZ.
       rewrite pow_powerRZ. rewrite Zabs2Nat.id_abs. rewrite Z.abs_eq. reflexivity. assumption. right. lia. Qed.

Lemma Q2R_2 : Q2R 2 = 2.
Proof. lra. Qed.

Lemma alpha_alphaQ w :
  alpha w = Q2R (alphaQ w).
Proof.
  unfold alpha, alphaQ.
  destruct w; try lra.
  destruct w; try lra.
  repeat (destruct w; [rewrite Q2R_div; [apply f_equal2|];
                       try lra; rewrite <- ?Q2R_pow', ?Q2R_2; try lia; try apply Qeq_bool_neq; try reflexivity|]).
  unfold alpha_high.
  unfold alphaQ_high.

  rewrite <- Q2R_pow.
  rewrite Q2R_div.

  replace (Q2R 633) with 633 by lra.
  replace (Q2R 1024) with 1024 by lra. reflexivity. apply Qeq_bool_neq. reflexivity. lia. Qed.

Local Open Scope R.

Ltac qia := unfold Qeq in *; simpl in *; nia.
Ltac qia_goal := unfold Qeq; simpl; nia.

Lemma Qinv_zero (a : Q) : a == 0 <-> / a == 0.
Proof.
  intros. unfold Qeq in *. simpl in *. unfold Qinv.
  destruct (Qnum a). simpl in *. nia. simpl in *. lia. simpl in *. lia. Qed.

Lemma Qpower_nonzero (a : Q) (b : Z) : ~ (a == 0) -> ~ (a ^ b == 0).
Proof.
  intros.
  intros contra.

  destruct b. qia.
  induction p; qia.
  induction p; simpl in *.
  apply Qinv_zero in contra.
  apply IHp.
  apply -> Qinv_zero. qia.

  apply Qinv_zero in contra.
  apply IHp.
  apply -> Qinv_zero. qia.

  apply H. apply Qinv_zero. assumption. Qed.

Lemma alpha31 i : (31 <= i < 67)%nat -> ((alpha i) ^ 49 < 1 / (2 ^ ((34 * i - 23)))).
Proof.
  intros.
  rewrite alpha_alphaQ.
  rewrite Q2R_pow.
  replace (Z.of_nat 49) with 49%Z by lia.
  replace 1 with (Q2R 1).
  replace 2 with (Q2R 2).
  rewrite Q2R_pow.
  rewrite <- Q2R_div.
  replace (Z.of_nat (34 * i - 23)) with (34 * (Z.of_nat i) - 23)%Z.
  apply Qlt_Rlt.
  apply alphaQ31. assumption.
  lia. apply Qpower_nonzero.
  apply Qeq_bool_neq. reflexivity. lia. lra. lra. lia. Qed.
