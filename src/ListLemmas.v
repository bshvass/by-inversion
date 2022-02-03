From Coq Require Export List.
From Coq Require Export Arith micromega.Lia.

Import ListNotations.

Fixpoint map_seq {A:Type} (f : nat -> A) start len :=
  match len with
  | 0%nat => nil
  | S len => f start :: (map_seq f (S start) len)
  end.

Lemma map_seq_spec {A:Type} (f : nat -> A) start len :
  map_seq f start len = map f (seq start len).
Proof.
  revert start; induction len; [reflexivity|].
  intros; cbn; rewrite IHlen. reflexivity. Qed.

Lemma map_seq_nonnil {A:Type} (f : nat -> A) n m : (0 < m)%nat -> map_seq f n m <> nil.
Proof. destruct m. lia. simpl. congruence. Qed.

Lemma map_seq_In {A:Type} (f : nat -> A) n m :
  forall i, (n <= i < n + m)%nat -> In (f i) (map_seq f n m).
Proof. rewrite map_seq_spec. intros; apply in_map; apply in_seq; assumption. Qed.

Lemma In_map_seq {A:Type} (f : nat -> A) n m x :
  In x (map_seq f n m) -> exists i, f i = x.
Proof. intros. rewrite map_seq_spec in H. apply in_map_iff in H as [i []]. exists i. assumption. Qed.

Lemma seq_snoc len : forall start, seq start (S len) = seq start len ++ [start + len].
Proof.
  induction len; intros.
  { cbv [seq app]. rewrite Nat.add_0_r; reflexivity. }
  { remember (S len); simpl seq.
    rewrite (IHlen (S start)); subst; simpl seq.
    rewrite Nat.add_succ_r; reflexivity. }
Qed.

Lemma map_seq_ext {A} (f g : nat -> A) (n m k : nat)
      (H : forall i : nat, n <= i < m + k -> f i = g (i + (m - n))%nat)
      (Hnm : n <= m) :
  map f (seq n k) = map g (seq m k).
Proof.
  generalize dependent m; generalize dependent n; induction k as [|k IHk]; intros; simpl.
  - reflexivity.
  - simpl; rewrite H by lia; replace (n + (m - n))%nat with m by lia.
    rewrite (IHk (S n) (S m)); [reflexivity| |lia].
    intros; rewrite Nat.sub_succ; apply H; lia. Qed.

Lemma cons_map_seq {A : Type} : forall len start (f : nat -> A), (f start) :: map_seq f (S start) len = map_seq f start (S len).
Proof. reflexivity. Qed.

Lemma map_seq_snoc {A : Type} : forall len start (f : nat -> A), map_seq f start (S len) = map_seq f start len ++ [f (start + len)%nat].
Proof.
  induction len; intros.
  { cbv [seq app]. rewrite Nat.add_0_r; reflexivity. }
  { remember (S len); simpl map_seq.
    rewrite (IHlen (S start)); subst; simpl seq.
    rewrite Nat.add_succ_r; reflexivity. }
Qed.
