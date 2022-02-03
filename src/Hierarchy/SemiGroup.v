From BY.Hierarchy Require Import Definitions Magma.
From stdpp Require Import list.

Local Open Scope mag_scope.
Section SemiGroup.

  Local Open Scope mag_scope.
  Class SemiGroup A `{Equiv A, Op1 A} :=
    {
      sg_setoid :> Setoid A;
      sg_proper :> Proper ((≡) ==> (≡) ==> (≡)) (∘);
      sg_assoc :> Assoc (≡) (∘)
    }.

End SemiGroup.

Section __.

  Context `{SemiGroup A}.

  Local Instance : Magma A. sub_class_tac. Qed.

  Instance quot_sg (rel : relation A) `{!MagmaCongruence rel} `{subrelation A (≡) rel} : @SemiGroup _ rel _.
  Proof. repeat split; try apply _; cbv; intros; apply is_subrelation; eapply assoc; exact _. Qed.

End __.
