From BY.Hierarchy Require Import Definitions.

Local Open Scope mag_scope.

Section Magma.

  Local Open Scope mag_scope.
  Class Magma A `{Equiv A, Op1 A} :=
    {
      mag_setoid :> Setoid A;
      mag_proper :> Proper ((≡) ==> (≡) ==> (≡)) (∘)
    }.

  Class MagmaMorph {A} {B} (f : A -> B) `{Magma A, Magma B} :=
    {
      mag_morph_setoid_morph :> SetoidMorph f;
      mag_morph_op : forall x y, f (x ∘ y) = f x ∘ f y
    }.

  Class MagmaCongruence `{Magma A} (rel : relation A) :=
    {
      mag_cong_equiv :> Equivalence rel;
      mag_cong_proper :> Proper (rel ==> rel ==> rel) (∘)
    }.
End Magma.

Section Magma.

  Context `{Magma A}
          {rel : relation A}
          `{!MagmaCongruence rel}.

  Instance : @Magma _ rel _.
  Proof. repeat split; try apply _. Qed.

End Magma.
