From stdpp Require Export base.

Global Generalizable All Variables.

Class ModEquiv A B := modequiv : A -> relation B.
Notation "a ≃ b 'md' p" := ((@equiv _ (modequiv p)) a b) (at level 90).
Notation "(≃ p )" := (modequiv p) (only parsing).
Infix "a ≄ b 'md' p" := (complement (modequiv p) a b) (at level 70) : type_scope.

Class Setoid A `{Equiv A} := setoid :> Equivalence (≡).
Class SetoidMorph {A} {B} (f : A -> B) `{Equiv A, Equiv B} :=
  {
    setmor_dom : Setoid A;
    setmor_cod : Setoid B;
    setmor_proper :> Proper ((≡) ==> (≡)) f
  }.

Class Congruence {A} (rel : relation A) (op : A -> A -> A) :=
  {
    cong_equiv :> Equivalence rel;
    cong_proper :> Proper (rel ==> rel ==> rel) op
  }.
Class LeftInv {A} (rel : relation A)
      (a : A)
      (f : A -> A)
      (g : A -> A -> A) :=
  left_inv : forall x, rel (g (f x) x) a.
Class RightInv {A} (rel : relation A)
      (a : A)
      (f : A -> A)
      (g : A -> A -> A) :=
  right_inv : forall x, rel (g x (f x)) a.

Class LeftDistr {A} (rel : relation A) (f : A -> A -> A) (g : A -> A -> A) :=
  left_distr : forall x y z, rel (f x (g y z)) (g (f x y) (f x z)).
Class RightDistr {A} (rel : relation A) (f : A -> A -> A) (g : A -> A -> A) :=
  right_distr : forall x y z, rel (f (g x y) z) (g (f x z) (f y z)).

Class LeftActDistr {A B} (rel : relation A) (f : B -> A -> A) (g : A -> A -> A) :=
  left_act_distr : forall x y z, rel (f x (g y z)) (g (f x y) (f x z)).
Class RightActDistr {A B} (rel : relation A) (f : A -> B -> A) (g : A -> A -> A) :=
  right_act_distr : forall x y z, rel (f (g x y) z) (g (f x z) (f y z)).

Class LeftActExch {A B} (rel : relation A) (f : B -> A -> A) (g : B -> B -> B) (h : A -> A -> A) :=
  left_act_exch : forall x y z, rel (f (g x y) z) (h (f x z) (f y z)).
Class RightActExch {A B} (rel : relation A) (f : A -> B -> A) (g : B -> B -> B) (h : A -> A -> A) :=
  right_act_exch : forall x y z, rel (f x (g y z)) (h (f x y) (f x z)).

Class LeftActAssoc {A B} (rel : relation A) (f : B -> A -> A) (g : B -> B -> B) :=
  left_act_assoc : forall x y z, rel (f (g x y) z) (f x (f y z)).
Class RightActAssoc {A B} (rel : relation A) (f : A -> B -> A) (g : B -> B -> B) :=
  right_act_assoc : forall x y z, rel (f x (g y z)) (f (f x y) z).

Class LeftActId {A B} (rel : relation A) (b : B) (f : B -> A -> A) :=
  left_act_id : forall x, rel (f b x) x.
Class RightActId {A B} (rel : relation A) (b : B) (f : A -> B -> A) :=
  right_act_id : forall x, rel (f x b) x.

Class LeftCancel {A} (rel : relation A) (f : A -> A -> A) :=
  left_cancel : forall x y z, rel (f x y) (f x z) -> rel y z.
Class RightCancel {A} (rel : relation A) (f : A -> A -> A) :=
  right_cancel : forall x y z, rel (f x y) (f z y) -> rel x z.
Class ZeroRule2 {A} (rel : relation A) (a : A) (f : A -> A -> A) :=
  zero_rule2 : forall x y, not (rel x a) -> not (rel y a) -> not (rel (f x y) a).
Class ZeroRule1 {A} (rel : relation A) (a : A) (f : A -> A -> A) :=
  zero_rule1 : forall x y, rel (f x y) a -> rel x a \/ rel y a.

Class Id1 A := id1 : A.
Class Id2 A := id2 : A.

Instance id2_id1 `{i : Id2 A} : Id1 A := i.

Class Op1 A := op1 : A -> A -> A.
Class Op2 A := op2 : A -> A -> A.

Instance op2_op1 `{f : Op2 A} : Op1 A := f.

Class Inv1 A := inv1 : A -> A.
Class Inv2 A := inv2 : A -> A.

Instance inv2_inv1 `{f : Inv2 A} : Inv1 A := f.

Class LeftAct A B := left_act : B -> A -> A.
Class RightAct A B := right_act : A -> B -> A.


Global Arguments left_inv {_ _} _ _ _ {_} _ : assert.
Global Arguments right_inv {_ _} _ _ _ {_} _ : assert.
Global Arguments left_distr {_ _} _ _ {_} _ _ _ : assert.
Global Arguments right_distr {_ _} _ _ {_} _ _ _ : assert.
Global Arguments left_act_id {_ _ _} _ _ {_} _ : assert.
Global Arguments right_act_id {_ _ _} _ _ {_} _ : assert.
Global Arguments left_act_distr {_ _ _} _ _ {_} _ _ _ : assert.
Global Arguments right_act_distr {_ _ _} _ _ {_} _ _ _ : assert.
Global Arguments left_act_assoc {_ _ _} _ _ {_} _ _ _ : assert.
Global Arguments right_act_assoc {_ _ _} _ _ {_} _ _ _ : assert.
Global Arguments left_act_exch {_ _ _} _ _ _ {_} _ _ _ : assert.
Global Arguments right_act_exch {_ _ _} _ _ _ {_} _ _ _ : assert.

Global Arguments zero_rule2 {_ _} _ _ {_} _ _ _ _ _ : assert.
Global Arguments zero_rule1 {_ _} _ _ {_} _ _ _ : assert.

Global Arguments op1 {_ _} _ _ : assert.
Global Arguments op2 {_ _} _ _ : assert.
Global Arguments id1 {_ _} : assert.
Global Arguments id2 {_ _} : assert.
Global Arguments inv1 {_ _} _ : assert.
Global Arguments inv2 {_ _} _ : assert.

Global Arguments left_act {_ _ _} _ _ : assert.
Global Arguments right_act {_ _ _} _ _ : assert.

Typeclasses Transparent Id1 Id2 Op1 Op2 Inv1 Inv2 LeftAct RightAct.

Declare Scope mag_scope.
Delimit Scope mag_scope with MA.

Infix "∘" := op1 (left associativity, at level 40) : mag_scope.
Notation "( x ∘.)" := (op1 x) (only parsing, at level 0) : mag_scope.
Notation "(.∘ x )" := (fun y => op1 _ x) (only parsing, at level 0) : mag_scope.
Notation "(∘)" := op1 (only parsing) : mag_scope.

Declare Scope mon_scope.
Delimit Scope mon_scope with MO.

Infix "∘" := op1 (left associativity, at level 40) : mon_scope.
Notation "( x ∘.)" := (op1 x) (only parsing, at level 0) : mon_scope.
Notation "(.∘ x )" := (fun y => op1 _ x) (only parsing, at level 0) : mon_scope.
Notation "(∘)" := op1 (only parsing) : mon_scope.
Notation "'ε'" := id1 : mon_scope.

Declare Scope grp_scope.
Delimit Scope grp_scope with G.

Infix "∘" := op1 (left associativity, at level 40) : grp_scope.
Notation "( x ∘.)" := (op1 x) (only parsing, at level 0) : grp_scope.
Notation "(.∘ x )" := (fun y => op1 _ x) (only parsing, at level 0) : grp_scope.
Notation "(∘)" := op1 (only parsing) : grp_scope.
Notation "'ε'" := id1 : grp_scope.
Notation "x ⁻¹" := (inv1 x) (at level 1) : grp_scope.
Notation "(⁻¹)" := inv1 (only parsing) : grp_scope.
(* Notation "x / y" := (op1 x (grp_inv y)) : grp_scope. *)

Declare Scope ab_grp_scope.
Delimit Scope ab_grp_scope with AG.

Infix "+" := op1 (left associativity, at level 50) : ab_grp_scope.
Notation "(+)" := op1 (only parsing) : ab_grp_scope.
Notation "( x +.)" := (op1 x) (only parsing, at level 0) : ab_grp_scope.
Notation "(.+ x )" := (fun y => op1 _ x) (only parsing, at level 0) : ab_grp_scope.
Notation "0" := id1 : ab_grp_scope.
Notation "- x" := (inv1 x) : ab_grp_scope.
Notation "(-)" := inv1 (only parsing) : ab_grp_scope.
Notation "x - y" := (op1 x (inv1 y)) : ab_grp_scope.

Declare Scope sr_scope.
Delimit Scope sr_scope with SR.

Infix "+" := op1 (left associativity, at level 50) : sr_scope.
Notation "(+)" := op1 (only parsing) : sr_scope.
Notation "( x +.)" := (op1 x) (only parsing, at level 0) : sr_scope.
Notation "(.+ x )" := (fun y => op1 _ x) (only parsing, at level 0) : sr_scope.
Infix "*" := op2 (left associativity, at level 40) : sr_scope.
Notation "[*]" := op2 (only parsing) : sr_scope.
Notation "( x *.)" := (op2 x) (only parsing, at level 0) : sr_scope.
Notation "(.* x )" := (fun y => op2 _ x) (only parsing, at level 0) : sr_scope.

Declare Scope ring_scope.
Delimit Scope ring_scope with RI.

Infix "+" := op1 (left associativity, at level 50) : ring_scope.
Notation "(+)" := op1 (only parsing) : ring_scope.
Notation "( x +.)" := (op1 x) (only parsing, at level 0) : ring_scope.
Notation "(.+ x )" := (fun y => op1 _ x) (only parsing, at level 0) : ring_scope.
Infix "*" := op2 (left associativity, at level 40) : ring_scope.
Notation "[*]" := op2 (only parsing) : ring_scope.
Notation "( x *.)" := (op2 x) (only parsing, at level 0) : ring_scope.
Notation "(.* x )" := (fun y => op2 _ x) (only parsing, at level 0) : ring_scope.
Notation "x - y" := (op1 x (inv1 y)) : ring_scope.
Notation "- x" := (inv1 x) : ring_scope.
Notation "(-)" := inv1 (only parsing) : ring_scope.
Notation "x / y" := (op2 x (inv2 y)) : ring_scope.
Notation "(/)" := inv2 (only parsing) : ring_scope.
Notation "0" := id1 : ring_scope.
Notation "1" := id2 : ring_scope.

Declare Scope lmod_scope.
Delimit Scope lmod_scope with LM.

Notation "(⋅)" := left_act (only parsing) : lmod_scope.
Notation "a ⋅ b" := (left_act a b) (at level 30) : lmod_scope.

Declare Scope rmod_scope.
Delimit Scope rmod_scope with RM.

Notation "(⋅)" := right_act (only parsing) : rmod_scope.
Notation "a ⋅ b" := (right_act a b) (at level 30) : rmod_scope.

Ltac sub_class_tac := split; exact _ || sub_class_tac.
