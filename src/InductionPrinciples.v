From Coq Require Import Arith ZArith micromega.Lia.

Lemma strong_induction P : (forall n, (forall m, (m < n) -> P m) -> P n) -> forall k, P k.
Proof.
  intros; generalize (Nat.le_refl k); generalize k at -2.
  induction k; intros. apply X. lia. destruct k0. apply X. lia. apply X. intros. apply IHk. lia. Qed.

Lemma induction2 P : P 0%nat -> P 1%nat -> (forall n, P n -> P (S n) -> P (S (S n))) -> forall k, P k.
Proof.
  intros; induction k using strong_induction; [destruct k as [|k]; [assumption|destruct k]; [assumption|]].
  apply X1; apply X2; lia. Qed.

Lemma induction_at n (P : nat -> Prop) : P n -> (forall m, (n <= m)%nat -> (P m -> P (S m))) -> (forall m, (n <= m)%nat -> P m).
Proof.
  intros; induction m.
  - apply le_n_0_eq in H1; subst; assumption.
  - destruct (Nat.eq_dec (S m) n).
    + subst; assumption.
    + apply H0; [|apply IHm]; lia. Qed.

Lemma rev_1_ind m (P : nat -> Prop) : P m -> (forall k, (0 < k <= m)%nat -> P k -> P (Nat.pred k)) -> forall k, (k <= m)%nat -> P k.
Proof.
  intros.
  assert { l : nat | (m - k)%nat = l }. eexists. reflexivity. destruct H2. generalize dependent k.
  induction x; intros.
  replace k with m by lia. assumption.
  destruct (S k =? m)%nat eqn:E2. apply Nat.eqb_eq in E2. replace k with (Nat.pred m) by lia. apply H0. lia. assumption.
  apply Nat.eqb_neq in E2.
  replace k with (Nat.pred (S k)) by lia. apply H0. lia.
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

Local Open Scope Z.

Lemma strong_natlike_ind (P : Z -> Prop) : (forall x, (forall y, 0 <= y < x -> P y) -> P x) -> forall x : Z, 0 <= x -> P x.
Proof.
  intros Hind x. remember (Z.abs_nat x). revert x Heqn Hind.
  induction n using strong_induction; intros.
  apply Hind. intros; apply H with (m := Z.abs_nat y); try assumption; lia. Qed.

Lemma rev_1_natlike_ind (P : Z -> Prop) x : P x -> (forall y, (0 < y <= x) -> P y -> P (Z.pred y)) -> (forall y, (0 <= y) -> (y <= x) -> P y).
Proof.
  intros Px Hind y. remember (Z.abs_nat (x - y)). revert y x Heqn Hind Px.
  induction n; intros.
  - assert (x = y) by lia; subst; assumption.
  - destruct (Z.eq_dec x y); [subst; assumption|].
    replace y with (Z.pred (Z.succ y)) by lia.
    apply Hind; [lia|]; apply IHn with (x:=x); try assumption; lia. Qed.
