From BY.Hierarchy Require Import Definitions.

Local Open Scope mag_scope.

Section Magma.

  Context `{Magma A}
          {rel : relation A}
          `{!MagmaCongruence rel}.

  Instance : @Magma _ rel _.
  Proof. repeat split; try apply _. Qed.

End Magma.
