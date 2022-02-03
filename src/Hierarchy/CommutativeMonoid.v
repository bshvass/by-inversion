Require Export Hierarchy.Definitions.
Require Import Hierarchy.SemiGroup.

Local Open Scope mon_scope.

Section CommutativeMonoid.

  Class CommutativeMonoid A `{Equiv A, Op1 A, Id1 A} :=
    {
      cmon_setoid :> Setoid A;
      cmon_proper :> Proper ((≡) ==> (≡) ==> (≡)) (∘);
      cmon_assoc :> Assoc (≡) (∘);
      cmon_id_l :> LeftId (≡) ε (∘);
      cmon_id_r :> RightId (≡) ε (∘);
      cmon_comm :> Comm (≡) (∘)
    }.

End CommutativeMonoid.

Section __.

  Context
    `{CommutativeMonoid A}.

  Global Instance : SemiGroup A.
  Proof. repeat split; first [apply _ | exact _]. Qed.

End __.
