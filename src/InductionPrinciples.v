From Coq Require Import Arith micromega.Lia.

Lemma strong_induction P : P 0 -> (forall n, (forall m, (m <= n) -> P m) -> P (S n)) -> forall k, P k.
Proof.
  intros; generalize (Nat.le_refl k); generalize k at -2.
  induction k; intros. apply le_n_0_eq in H; subst; assumption.
  destruct k0; [assumption|]. apply X0; intros. apply IHk; lia. Qed.

Lemma induction2 P : P 0%nat -> P 1%nat -> (forall n, P n -> P (S n) -> P (S (S n))) -> forall k, P k.
Proof.
  intros; induction k using strong_induction; [assumption | destruct k; try assumption].
  apply X1; apply X2; lia. Qed.

Lemma induction_at n (P : nat -> Prop) : P n -> (forall m, (n <= m)%nat -> (P m -> P (S m))) -> (forall m, (n <= m)%nat -> P m).
Proof.
  intros; induction m.
  - apply le_n_0_eq in H1; subst; assumption.
  - destruct (Nat.eq_dec (S m) n).
    + subst; assumption.
    + apply H0; [|apply IHm]; lia. Qed.

Lemma rev_1_ind P m : P m -> (forall k, (0 < k <= m)%nat -> P k -> P (Nat.pred k)) -> (forall k, (k <= m)%nat -> P k).
Proof.
  intros.
  assert { l : nat | (m - k)%nat = l }. eexists. reflexivity. destruct H0. generalize dependent k.
  induction x; intros.
  replace k with m by lia. assumption.
  destruct (S k =? m)%nat eqn:E2. apply Nat.eqb_eq in E2. replace k with (Nat.pred m) by lia. apply X0. lia. assumption.
  apply Nat.eqb_neq in E2.
  replace k with (Nat.pred (S k)) by lia. apply X0. lia.
  apply IHx. lia. lia. Qed.

Lemma rev_2_ind P m : P (S m) -> P m -> (forall k, (0 < k <= S m)%nat -> P k -> P (Nat.pred k) -> P (Nat.pred (Nat.pred k))) -> (forall k, (k <= (S m))%nat -> P k).
Proof.
  intros.

  assert { l : nat | ((S m) - k)%nat = l }. eexists. reflexivity. destruct H0. generalize dependent k.
  induction x using induction2; intros.
  - assert (k = S m) by lia. congruence.
  - assert (k = m) by lia. congruence.
  - destruct (Nat.eq_dec (S (S k)) (S m)).
    replace k with (Nat.pred (Nat.pred (S (S k)))) by lia. rewrite e0. apply X1. lia.
    assumption. assumption.

    replace k with (Nat.pred (Nat.pred (S (S k)))) by lia.
    apply X1. lia. apply IHx. lia. lia. apply IHx0. lia. lia. Qed.
