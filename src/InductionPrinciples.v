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
