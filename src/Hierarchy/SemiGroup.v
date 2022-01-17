Require Import Hierarchy.Definitions.
From stdpp Require Import list.

Section __.

  Context `{SemiGroup A}.
  Local Open Scope mag_scope.

  Local Instance : Magma A. sub_class_tac. Qed.

  Instance quot_sg (rel : relation A) `{!MagmaCongruence rel} `{subrelation A (≡) rel} : @SemiGroup _ rel _.
  Proof. repeat split; try apply _; cbv; intros; apply is_subrelation; eapply assoc; exact _. Qed.

  Global Instance fold_left_proper : Proper ((≡) ==> (≡) ==> (≡)) (fold_left (∘)).
  Proof.
    do 3 red. induction x; intros.
    - inversion H2.
      subst. assumption.
    - inversion H2; subst.
      simpl. apply IHx.
      assumption.
      rewrite H3, H6.
      reflexivity.
  Qed.

  Lemma fold_left_assoc (a b : A) ls :
    a ∘ (fold_left (∘) ls b) ≡ fold_left (∘) ls (a ∘ b).
  Proof.
    revert b; induction ls; intros b; simpl.
    - reflexivity.
    - rewrite IHls.
      rewrite (assoc (∘)).
      reflexivity.
  Qed.

End __.
