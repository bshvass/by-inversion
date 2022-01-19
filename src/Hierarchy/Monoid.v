From Coq Require Import Arith micromega.Lia.
From BY Require Import Hierarchy.Definitions Hierarchy.SemiGroup Hierarchy.List.

Section Monoid.

  Local Open Scope mag_scope.
  Local Open Scope mon_scope.

  Context
    `{Monoid A}.
  Global Instance : Magma A. sub_class_tac. Qed.
  Global Instance : SemiGroup A. sub_class_tac. Qed.

  Instance quot_mon (rel : relation A) `{!MagmaCongruence rel} `{subrelation A (≡) rel} : @Monoid _ rel _ _.
  repeat split; try apply _;
  cbv; intros; apply is_subrelation; (apply assoc; exact _) || (apply right_id; exact _) || (apply left_id; exact _). Qed.

End Monoid.
