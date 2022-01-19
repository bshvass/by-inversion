Require Import Hierarchy.Definitions.
From stdpp Require Import list.

Section __.

  Context `{SemiGroup A}.
  Local Open Scope mag_scope.

  Local Instance : Magma A. sub_class_tac. Qed.

  Instance quot_sg (rel : relation A) `{!MagmaCongruence rel} `{subrelation A (≡) rel} : @SemiGroup _ rel _.
  Proof. repeat split; try apply _; cbv; intros; apply is_subrelation; eapply assoc; exact _. Qed.

End __.
