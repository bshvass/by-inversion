Require Import Hierarchy.Definitions.

Section __.

Local Open Scope mag_scope.
Local Open Scope mon_scope.

Context
  `{CommutativeMonoid A}.

Global Instance : SemiGroup A.
Proof. repeat split; first [apply _ | exact _]. Qed.

End __.
