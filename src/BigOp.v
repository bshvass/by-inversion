Require Import List Arith micromega.Lia.

From BY Require Import Matrix.

Local Open Scope mat_scope.

Lemma seq_snoc len : forall start, seq start (S len) = seq start len ++ ((start + len)%nat :: nil).
Proof.
  induction len; intros.
  { cbv [seq app]. rewrite Nat.add_0_r; reflexivity. }
  { remember (S len); simpl seq.
    rewrite (IHlen (S start)); subst; simpl seq.
    rewrite Nat.add_succ_r; reflexivity. }
Qed.

Definition big_mmult_rev n (f : nat -> mat) :=
  fold_right mmult I (map f (rev (seq 0 n))).

Lemma big_mmult_rev_S n f :
  big_mmult_rev (S n) f = f n * big_mmult_rev n f.
Proof. unfold big_mmult_rev; rewrite seq_snoc, rev_app_distr; reflexivity. Qed.

Definition big_sum_rev n f : nat :=
  fold_right (Nat.add) 0%nat (map f (rev (seq 0 n))).

Lemma big_sum_rev_S n f :
  big_sum_rev (S n) f = (f n + big_sum_rev n f)%nat.
Proof. unfold big_sum_rev; rewrite seq_snoc, rev_app_distr; reflexivity. Qed.

Lemma big_sum_bound1 n f :
  (forall i, i <= n -> 1 <= f i) -> n <= big_sum_rev n f.
Proof.
  intros.

  induction n.
  unfold big_sum_rev. simpl. lia.

  assert (forall i : nat, i <= n -> 1 <= f i). intros; apply H. lia.
  apply IHn in H0.

  rewrite big_sum_rev_S.
  assert (1 <= f n). apply H. lia. lia. Qed.
