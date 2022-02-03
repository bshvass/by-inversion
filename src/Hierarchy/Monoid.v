From Coq Require Import Arith micromega.Lia.
From BY.Hierarchy Require Export Definitions.
From BY.Hierarchy Require Import Magma.

Local Open Scope mon_scope.

Section Monoid.

  Class Monoid A `{Equiv A, Op1 A, Id1 A} :=
    {
      mon_sg :> Setoid A;
      mon_proper :> Proper ((≡) ==> (≡) ==> (≡)) (∘);
      mon_assoc :> Assoc (≡) (∘);
      mon_id_l :> LeftId (≡) ε (∘);
      mon_id_r :> RightId (≡) ε (∘)
    }.

  Class MonoidMorph {A} {B} (f : A -> B) `{Monoid A, Monoid B} :=
    {
      mon_morph_mag_morph :> SetoidMorph f;
      mon_morph_op : forall x y, f (x ∘ y) = f x ∘ f y;
      mon_morph_id : f ε = ε
    }.

  Context
    `{Monoid A}.
  Global Instance : Magma A. sub_class_tac. Qed.

  Instance quot_mon (rel : relation A) `{!MagmaCongruence rel} `{subrelation A (≡) rel} : @Monoid _ rel _ _.
  repeat split; try apply _;
  cbv; intros; apply is_subrelation; (apply assoc; exact _) || (apply right_id; exact _) || (apply left_id; exact _). Qed.

End Monoid.
