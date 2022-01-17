From BY Require Export ListLemmas.
From BY Require Import Hierarchy.Definitions.
From stdpp Require Export list.

Section __.

  Context
    `{Setoid A}.

  Lemma map_seq_ext_equiv (f g : nat -> A) (n m k : nat)
        (Hequiv : forall i : nat, n <= i < m + k -> f i ≡ g (i + (m - n))%nat)
        (Hnm : n <= m) :
    map f (seq n k) ≡ map g (seq m k).
  Proof.
    generalize dependent m; generalize dependent n; induction k as [|k IHk]; intros; simpl.
    - reflexivity.
    - simpl; rewrite Hequiv by lia; replace (n + (m - n))%nat with m by lia.
      rewrite (IHk (S n) (S m)); [reflexivity| |lia].
      intros; rewrite Nat.sub_succ; apply Hequiv; lia. Qed.

  Global Instance rev_proper : Proper ((≡) ==> (≡)) (@rev A).
  Proof.
    do 2 red; induction x; intros; simpl.
    - inversion H1. reflexivity.
    - inversion H1. subst.
      simpl.
      rewrite (IHx k) .
      rewrite H4.
      reflexivity.
      assumption.
  Qed.

End __.
