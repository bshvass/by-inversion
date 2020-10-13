From Coq Require Import ZArith micromega.Lia.

Local Open Scope Z.
Notation "a ^+ b" := (Zpower_nat a b) (at level 30).

Lemma mul_base_pull (a : Z) (b : nat) (H : (0 < b)%nat) :
  a ^+ b = a * a ^+ (b - 1).
Proof. destruct b; [lia|]; simpl; rewrite Nat.sub_0_r; reflexivity. Qed.

Lemma Zpower_nat_0_r a : a ^+ 0 = 1.
Proof. reflexivity. Qed.

Lemma Zpower_nat_1_r a : a ^+ 1 = a.
Proof. unfold Zpower_nat; simpl; lia. Qed.

Lemma Zpower_nat_nonzero a n : a <> 0 -> a ^+ n <> 0.
Proof. induction n; simpl; nia. Qed.

Lemma Zpower_nat_nonneg a n : 0 <= a -> 0 <= a ^+ n.
Proof. induction n.
       - simpl; nia.
       - intros; rewrite Zpower_nat_succ_r; nia. Qed.

Lemma Zpower_nat_pos_nonneg a n : 0 < a -> 0 < a ^+ n.
Proof. induction n.
       - simpl; nia.
       - intros; rewrite Zpower_nat_succ_r; nia. Qed.

Lemma Zpower_nat_gt1 a n : 1 < a -> 1 < a ^+ S n.
Proof. induction n.
       - simpl; nia.
       - intros; rewrite Zpower_nat_succ_r; nia. Qed.

Lemma Zpower_nat_mul_l a b : a * a ^+ b = a ^+ (S b).
Proof. apply Zpower_nat_succ_r. Qed.

Lemma Zpower_nat_mul_r a b : a ^+ b * a = a ^+ (S b).
Proof. rewrite Zpower_nat_succ_r; lia. Qed.

Lemma mul_nat_base_push a b : a * a ^+ b = a ^+ (b + 1).
Proof. now rewrite Nat.add_1_r, Zpower_nat_succ_r. Qed.

Lemma Zpower_nat_base_divide a n : (0 < n)%nat -> (a | a ^+ n).
Proof. intros; exists (a ^+ (n - 1)); rewrite Zpower_nat_mul_r; apply f_equal; lia. Qed.

Lemma Zpower_nat_divide a n m : (m <= n)%nat -> (a ^+ m | a ^+ n).
Proof. intros; exists (a ^+ (n - m)); rewrite <- Zpower_nat_is_exp; apply f_equal; lia. Qed.

Lemma Zpower_nat_mul a b c : (a * b) ^+ c = a ^+ c * b ^+ c.
Proof. induction c; [reflexivity|simpl; lia]. Qed.

Lemma Zpower_nat_log2 a : 0 < a -> 2 ^+ (Z.to_nat (Z.log2 a)) <= a.
Proof. rewrite Zpower_nat_Z, Z2Nat.id. apply Z.log2_spec. apply Z.log2_nonneg. Qed.

Lemma Zpower_nat_log2_up a : 1 < a -> a <= 2 ^+ (Z.to_nat (Z.log2_up a)).
Proof. rewrite Zpower_nat_Z, Z2Nat.id. apply Z.log2_up_spec. apply Z.log2_up_nonneg. Qed.
