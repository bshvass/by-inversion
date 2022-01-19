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

Declare Scope mag_scope.
Declare Scope mon_scope.
Declare Scope grp_scope.
Declare Scope ab_grp_scope.
Declare Scope sr_scope.
Declare Scope ring_scope.
Declare Scope lmod_scope.
Declare Scope rmod_scope.

Delimit Scope mag_scope with MA.
Delimit Scope mon_scope with MO.
Delimit Scope grp_scope with G.
Delimit Scope ab_grp_scope with AG.
Delimit Scope sr_scope with SR.
Delimit Scope ring_scope with RI.
Delimit Scope lmod_scope with LM.
Delimit Scope rmod_scope with RM.

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

Infix "∘" := op1 (left associativity, at level 40) : mag_scope.
Notation "( x ∘.)" := (op1 x) (only parsing, at level 0) : mag_scope.
Notation "(.∘ x )" := (fun y => op1 _ x) (only parsing, at level 0) : mag_scope.
Notation "(∘)" := op1 (only parsing) : mag_scope.

Notation "'ε'" := id1 : mon_scope.

Notation "x ⁻¹" := (inv1 x) (at level 1) : grp_scope.
Notation "(⁻¹)" := inv1 (only parsing) : grp_scope.
(* Notation "x / y" := (op1 x (grp_inv y)) : grp_scope. *)

Infix "+" := op1 (left associativity, at level 50) : ab_grp_scope.
Notation "(+)" := op1 (only parsing) : ab_grp_scope.
Notation "( x +.)" := (op1 x) (only parsing, at level 0) : ab_grp_scope.
Notation "(.+ x )" := (fun y => op1 _ x) (only parsing, at level 0) : ab_grp_scope.
Notation "0" := id1 : ab_grp_scope.
Notation "- x" := (inv1 x) : ab_grp_scope.
Notation "(-)" := inv1 (only parsing) : ab_grp_scope.
Notation "x - y" := (op1 x (inv1 y)) : ab_grp_scope.

Infix "+" := op1 (left associativity, at level 50) : sr_scope.
Notation "(+)" := op1 (only parsing) : sr_scope.
Notation "( x +.)" := (op1 x) (only parsing, at level 0) : sr_scope.
Notation "(.+ x )" := (fun y => op1 _ x) (only parsing, at level 0) : sr_scope.
Infix "*" := op2 (left associativity, at level 40) : sr_scope.
Notation "[*]" := op2 (only parsing) : sr_scope.
Notation "( x *.)" := (op2 x) (only parsing, at level 0) : sr_scope.
Notation "(.* x )" := (fun y => op2 _ x) (only parsing, at level 0) : sr_scope.

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

Notation "(⋅)" := left_act (only parsing) : lmod_scope.
Notation "(⋅)" := right_act (only parsing) : rmod_scope.
Notation "a ⋅ b" := (left_act a b) (at level 30) : lmod_scope.
Notation "a ⋅ b" := (right_act a b) (at level 30) : rmod_scope.
(* Infix "⋅" := left_act (at level 30) : lmodule_scope. *)
(* Infix "⋅" := right_act : rmodule_scope. *)

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

Section SemiGroup.

  Local Open Scope mag_scope.
  Class SemiGroup A `{Equiv A, Op1 A} :=
    {
      sg_setoid :> Setoid A;
      sg_proper :> Proper ((≡) ==> (≡) ==> (≡)) (∘);
      sg_assoc :> Assoc (≡) (∘)
    }.

End SemiGroup.

Section Monoid.
  Local Open Scope mag_scope.
  Local Open Scope mon_scope.

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

End Monoid.

Section CommutativeMonoid.
  Local Open Scope mag_scope.
  Local Open Scope mon_scope.

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

Section Group.
  Local Open Scope mag_scope.
  Local Open Scope mon_scope.
  Local Open Scope grp_scope.

  Class Group A `{Equiv A, Op1 A, Id1 A, Inv1 A} :=
    {
      grp_setoid :> Setoid A;
      grp_op_proper :> Proper ((≡) ==> (≡) ==> (≡)) (∘);
      grp_inv_proper :> Proper ((≡) ==> (≡)) ((⁻¹));
      grp_assoc :> Assoc (≡) (∘);
      grp_id_l :> LeftId (≡) ε (∘);
      grp_id_r :> RightId (≡) ε (∘);
      grp_inv_l :> LeftInv (≡) ε (⁻¹) (∘);
      grp_inv_r :> RightInv (≡) ε (⁻¹) (∘)
    }.

  Class GrpCongruence `{Group A} (rel : relation A) :=
    {
      grp_cong_equiv :> Equivalence rel;
      grp_cong_op_proper :> Proper (rel ==> rel ==> rel) (∘);
      grp_cong_inv_proper :> Proper (rel ==> rel) (⁻¹)
    }.

End Group.

Section AbelianGroup.

  Local Open Scope ab_grp_scope.

  Class AbelianGroup A `{Equiv A, Op1 A, Id1 A, Inv1 A} :=
    {
      ab_grp_setoid :> Setoid A;
      ab_grp_proper :> Proper ((≡) ==> (≡) ==> (≡)) (+);
      ab_grp_inv_proper :> Proper ((≡) ==> (≡)) (-);
      ab_grp_assoc :> Assoc (≡) (+);
      ab_grp_comm :> Comm (≡) (+);
      ab_grp_id_l :> LeftId (≡) 0 (+);
      ab_grp_id_r :> RightId (≡) 0 (+);
      ab_grp_inv_l :> LeftInv (≡) 0 (-) (+);
      ab_grp_inv_r :> RightInv (≡) 0 (-) (+)
    }.

End AbelianGroup.

Section SemiRing.

  Local Open Scope mag_scope.
  Local Open Scope sr_scope.

  Class SemiRing A `{Equiv A, Op1 A, Op2 A} :=
    {
      sr_mag1 :> @Magma _ _ (∘);
      sr_mag2 :> @Magma _ _ [*];
      sr_distr_l :> LeftDistr (≡) [*] (∘);
      sr_distr_r :> RightDistr (≡) [*] (∘)
    }.

End SemiRing.

Section Ring.
  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  (* Local Open Scope ab_grp_scope. *)

  Class Ring A `{Equiv A, Op1 A, Op2 A, Id1 A, Id2 A, Inv1 A} :=
    {
      ring_ab_grp :> @AbelianGroup _ _ (+) 0 (-);
      ring_mon :> @Monoid _ _ [*] 1;
      ring_distr_l :> LeftDistr (≡) [*] (+);
      ring_distr_r :> RightDistr (≡) [*] (+)
    }.

  Class RingCongruence `{Ring A} (rel : relation A) :=
    {
      ring_cong_equiv :> Equivalence rel;
      ring_cong_op1_proper :> Proper (rel ==> rel ==> rel) (+);
      ring_cong_op2_proper :> Proper (rel ==> rel ==> rel) [*];
      ring_cong_inv_proper :> Proper (rel ==> rel) (-)
    }.
End Ring.

Section CommutativeRing.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  (* Local Open Scope ab_grp_scope. *)

  Class CommutativeRing A `{Equiv A, Op1 A, Op2 A, Id1 A, Id2 A, Inv1 A} :=
    {
      cring_ab_grp :> @AbelianGroup _ _ (+) 0 (-);
      cring_mon :> @CommutativeMonoid _ _ [*] 1;
      cring_distr_l :> LeftDistr (≡) [*] (+);
      cring_distr_r :> RightDistr (≡) [*] (+);
    }.

End CommutativeRing.

Section IntegralDomain.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  (* Local Open Scope ab_grp_scope. *)

  Class IntegralDomain A `{Equiv A, Op1 A, Op2 A, Id1 A, Id2 A, Inv1 A} :=
    {
      dom_ab_grp :> @AbelianGroup _ _ (+) 0 (-);
      dom_mon :> @CommutativeMonoid _ _ [*] 1;
      dom_distr_l :> LeftDistr (≡) [*] (+);
      dom_distr_r :> RightDistr (≡) [*] (+);
      dom_non_trivial : 0 ≢ 1;
      dom_zero_rule :> ZeroRule1 (≡) 0 [*]
    }.

End IntegralDomain.

Section LeftModule.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope ab_grp_scope.
  Local Open Scope lmod_scope.

  Class LeftModule A B `{Equiv A, Op1 A, Id1 A, Inv1 A, Equiv B, Op1 B, Op2 B, Id1 B, Id2 B, Inv1 B, LeftAct A B} :=
    {
      lmod_abgroup :> AbelianGroup A;
      lmod_cring :> Ring B;
      lmod_proper :> Proper ((≡) ==> (≡) ==> (≡)) (⋅);
      lmod_distr_l :> LeftActDistr (≡) (⋅) (+)%AG;
      lmod_exch_l :> LeftActExch (≡) (⋅) (+)%SR (+)%AG;
      lmod_act_assoc :> LeftActAssoc (≡) (⋅) [*];
      lmod_left_id :> LeftActId (≡) 1 (⋅)
    }.
End LeftModule.

Section LeftAlgebra.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope lmod_scope.

  Class LeftAlgebra A B `{Equiv A, Op1 A, Op2 A, Id1 A, Id2 A, Inv1 A, Equiv B, Op1 B, Op2 B, Id1 B, Id2 B, Inv1 B, LeftAct A B} :=
    {
      lalg_ring :> Ring A;
      lalg_cring :> Ring B;
      lalg_proper :> Proper ((≡) ==> (≡) ==> (≡)) (⋅);
      lalg_distr_l :> LeftActDistr (≡) (⋅) (+);
      lalg_exch_l :> LeftActExch (≡) (⋅) (+) (+);
      lalg_act_assoc :> LeftActAssoc (≡) (⋅) [*];
      lalg_left_id :> LeftActId (≡) 1 (⋅)
    }.

End LeftAlgebra.

Ltac sub_class_tac := split; exact _ || sub_class_tac.

(* Module Subrelation. *)
(*   Context {A} *)
(*           `{Setoid A} *)
(*           `{cong : relation A}. *)

(*   Infix "∼" := cong (at level 70). *)
(*   Notation "(∼)" := cong (only parsing). *)

(*   Context `{subrelation A (=) (∼)}. *)

(*   Global Instance : Reflexive (∼). *)
(*   Proof. now red; intros; apply is_subrelation. Defined. *)
(*   Global Instance : Symmetric (∼). *)
(*   Proof. red; intros; apply is_subrelation. *)
(*          symmetry. *)

(*   Goal forall a b, a = b -> a ∼ b. intros ? ?. apply is_subrelation. pose proof @is_subrelation A. intros. pose proof subrelation. subrelation_tac.  auto. *)

(*                              `{subrelation e11 e12}. *)
