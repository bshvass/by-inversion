Require Export AAC_tactics.AAC.
Require Import Hierarchy.Definitions.

Section __.
  Context
    `{e : Equiv A}
    `{@Assoc A e f}
    `{@Comm A A e f}
    `{@LeftId A e a f}
    `{@RightId A e a f}.

  Global Instance : AAC.Associative (≡) f := assoc _.
  Global Instance : AAC.Commutative (≡) f := comm _.
  Global Instance : AAC.Unit (≡) f a := {| law_neutral_left := left_id _ _ ;
                                           law_neutral_right := right_id _ _ |}.
End __.
