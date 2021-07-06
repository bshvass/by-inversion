Require Import ZArith micromega.Lia.
Require Import micromega.Lra.
Require Import micromega.Lqa.
Require Import List.
Require Import QArith.
Require Import Qpower.

From BY Require Import Rlemmas AppendixF Qmin_list ListLemmas.

Local Open Scope Q.

Definition alphaQ_high w : Q := (633/1024) ^ w.

Definition alphaQ (w : Z) : Q :=
  if (w <=? 66)%Z then
  match w with
  | 0%Z => 1 | 1%Z => 1 | 2%Z => 689491/2^20 | 3%Z => 779411/2^21
  | 4%Z => 880833/2^22 | 5%Z => 165219/2^20 | 6%Z => 97723/2^20 | 7%Z => 882313/2^24
  | 8%Z => 306733/2^23 | 9%Z => 92045/2^22 | 10%Z => 439213/2^25 | 11%Z => 281681/2^25
  | 12%Z => 689007/2^27 | 13%Z => 824303/2^28 | 14%Z => 257817/2^27 | 15%Z => 634229/2^29
  | 16%Z => 386245/2^29 | 17%Z => 942951/2^31 | 18%Z => 583433/2^31 | 19%Z => 713653/2^32
  | 20%Z => 432891/2^32 | 21%Z => 133569/2^31 | 22%Z => 328293/2^33 | 23%Z => 800421/2^35
  | 24%Z => 489233/2^35 | 25%Z => 604059/2^36 | 26%Z => 738889/2^37 | 27%Z => 112215/2^35
  | 28%Z => 276775/2^37 | 29%Z => 84973/2^36 | 30%Z => 829297/2^40 | 31%Z => 253443/2^39
  | 32%Z => 625405/2^41 | 33%Z => 95625/2^39 | 34%Z => 465055/2^42 | 35%Z => 286567/2^42
  | 36%Z => 175951/2^42 | 37%Z => 858637/2^45 | 38%Z => 65647/2^42 | 39%Z => 40469/2^42
  | 40%Z => 24751/2^42 | 41%Z => 240917/2^46 | 42%Z => 593411/2^48 | 43%Z => 364337/2^48
  | 44%Z => 889015/2^50 | 45%Z => 543791/2^50 | 46%Z => 41899/2^47 | 47%Z => 205005/2^50
  | 48%Z => 997791/2^53 | 49%Z => 307191/2^52 | 50%Z => 754423/2^54 | 51%Z => 57527/2^51
  | 52%Z => 281515/2^54 | 53%Z => 694073/2^56 | 54%Z => 212249/2^55 | 55%Z => 258273/2^56
  | 56%Z => 636093/2^58 | 57%Z => 781081/2^59 | 58%Z => 952959/2^60 | 59%Z => 291475/2^59
  | 60%Z => 718599/2^61 | 61%Z => 878997/2^62 | 62%Z => 534821/2^62 | 63%Z => 329285/2^62
  | 64%Z => 404341/2^63 | 65%Z => 986633/2^65 | 66%Z => 603553/2^65 | _ => 0 end
  else alphaQ_high w.

Definition alphaQ_nat_high (w : nat) : Q := (633/1024) ^ (Z.of_nat w).

Definition alphaQ_nat (w : nat) : Q :=
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
  | 64%nat => 404341/2^63 | 65%nat => 986633/2^65 | 66%nat => 603553/2^65 | _ => alphaQ_nat_high w
  end.


Definition alphaQ_high_Z w : Q := (633/1024) ^ w.

Lemma alphaQ_nat_pos w : 0 < alphaQ_nat w.
Proof. do 67 (destruct w as [|w]; simpl; try apply Qlt_shift_div_l; try lra).
       unfold alphaQ_nat_high. apply QExtra.Qpower_pos_lt.
       apply Qlt_shift_div_l; lra. Qed.

Definition alphaQ_quot w i :=
  (alphaQ_nat (w + i)%nat) / (alphaQ_nat i).

Definition betaQ_aux w n :=
  map_seq (alphaQ_quot w) 0%nat n.

Definition betaQ w := Qmin_list (betaQ_aux w 68%nat).

Definition betaQ_quot w j :=
  (betaQ (w + j)) * 2 ^ (Z.of_nat j) * 70 / 169.

Definition gammaQ_aux w e n :=
  map_seq (betaQ_quot w) e n.

Definition gammaQ w e := Qmin_list (gammaQ_aux w e 68%nat).

Lemma alphaQ_nat_67 w : (67 <= w)%nat -> alphaQ_nat w = alphaQ_nat_high w.
Proof. intros; repeat (destruct w; [lia|]). reflexivity. Qed.

Require Import OrdersEx.

Lemma alphaQ_min_list : Qmin_list (map_seq (fun j => ((633/1024) ^ (Z.of_nat j)) / alphaQ_nat j) 0 68%nat) == 633^5 / (2^30 * 165219).
Proof.
  vm_cast_no_check (@eq_refl Z ((Qnum (633 ^ 5 / (2 ^ 30 * 165219)) *
   Z_as_DT.pos (Qden (Qmin_list (map_seq (fun j : nat => ((633 / 1024) ^ Z.of_nat j / alphaQ_nat j)%Q) 0 68))))%Z)).
Qed.

Ltac for_each H :=
  match goal with
  | [ H: (?a <= ?b < ?c)%nat |- _ ] => destruct H as [ge lt];
                                  repeat
                                    let t := fresh in inversion ge as [eq|? t];
                                                      [subst; vm_compute; reflexivity|try lia; clear ge; rename t into ge]
  end.
Ltac for_each_new :=
  match goal with
  (* | [ H: (?a <= ?b < ?a)%Z |- _ ] => lia; clear H *)
  | [ H : (?a <= ?b < ?c)%Z |- _ ] => destruct (Z.eq_dec a b); subst; lia;
                                   assert (a + 1 <= b < c) by lia; clear H
  end.

Lemma alphaQ_alphaQ_nat w :
  alphaQ (Z.of_nat w) = alphaQ_nat w.
Proof.
  do 67 (destruct w; try reflexivity). cbn [alphaQ_nat].
  unfold alphaQ.
  replace (_ <=? 66)%Z with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity. Qed.

Lemma alphaQ_nat_alphaQ w : (0 <= w)%Z ->
  alphaQ w = alphaQ_nat (Z.to_nat w).
Proof.
  intros.
  replace w with (Z.of_nat (Z.to_nat w)).
  rewrite Z2Nat.id at 2 by assumption.
  apply alphaQ_alphaQ_nat.
  apply Z2Nat.id; assumption. Qed.

Lemma alphaQ31 i : (31 <= i < 67)%Z -> ((alphaQ i) ^ 49 < 1 / (2 ^ ((34 * i - 23))))%Q.
Proof.
  intros.

repeat match goal with
         | [ H: (?a <= ?b < ?a)%Z |- _ ] => fail 1
         | [ H : (?a <= ?b < ?c)%Z |- _ ] => destruct (Z.eq_dec a b) as [E|E]; [subst; reflexivity|
                                                                    let H2 := fresh in assert (H2 : (a + 1 <= b < c)%Z) by lia; clear E;
                                                                                       simpl in H2; clear H]
       end. lia.
Qed.

(* this should go somewhere else *)
Lemma Qmin_mul q x y : 0 <= q -> 0 <= x -> 0 <= y -> Qmin (q * x) (q * y) == q * Qmin x y.
Proof.
  intros. unfold Qmin. unfold GenericMinMax.gmin.
  destruct ((q * x) ?= (q * y)) eqn:E1;
    destruct (x ?= y) eqn:E2; try reflexivity.
  apply Qeq_alt in E1.
  apply Qgt_alt in E2. lra.

  apply Qlt_alt in E1.
  apply Qgt_alt in E2. nra.

  apply Qgt_alt in E1.
  apply Qeq_alt in E2. nra.

  apply Qgt_alt in E1.
  apply Qlt_alt in E2. nra.  Qed.


Require Import Rbase Reals Qreals micromega.Lra.

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
  alpha w = Q2R (alphaQ (Z.of_nat w)).
Proof.
  unfold alpha, alphaQ.
  destruct w; try (cbn; lra).
  destruct w; try (cbn; lra).
  repeat (destruct w; [cbn -[Qpower]; rewrite Q2R_div by (apply Qeq_bool_neq; reflexivity); apply f_equal2; [lra|
                                                                                                             rewrite <- ?Q2R_pow', ?Q2R_2 by lia; reflexivity]|]).
  replace (_ <=? 66)%Z with false by (symmetry; apply Z.leb_gt; lia).
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
  apply alphaQ31. lia.
  lia. apply Qpower_nonzero.
  apply Qeq_bool_neq. reflexivity. lia. lra. lra. lia. Qed.
