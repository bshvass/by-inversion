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

Class MonId A := mon_id : A.
Class AbGrpId A := ab_grp_id : A.
Class RingId1 A := ring_id1 : A.
Class RingId2 A := ring_id2 : A.

Instance ab_grp_id_mon_id `{i : AbGrpId A} : MonId A := i.
Instance ring_id1_mon_id `{i : RingId1 A} : MonId A := i.
Instance ring_id2_mon_id `{i : RingId2 A} : MonId A := i.

Class MagOp A := mag_op : A -> A -> A.
Class AbGrpOp A := abgrp_op : A -> A -> A.
Class SrOp1 A := sr_op1 : A -> A -> A.
Class SrOp2 A := sr_op2 : A -> A -> A.

Instance ab_grp_op_mag_op `{f : AbGrpOp A} : MagOp A := f.
Instance sr_op1_mag_op `{f : SrOp1 A} : MagOp A := f.
Instance sr_op2_mag_op `{f : SrOp2 A} : MagOp A := f.

Class GrpInv A := grp_inv : A -> A.
Class AbGrpOpp A := abgrp_opp :> GrpInv A.
Class RingInv1 A := ring_inv1 :> GrpInv A.
Class RingInv2 A := ring_inv2 :> GrpInv A.

Class LeftAct A B := left_act : B -> A -> A.
Class RightAct A B := right_act : A -> B -> A.
Notation "2" := nat.
Notation "7" := nat.
Check 2.
Check 2.
Declare Scope mag_scope.
Declare Scope mon_scope.
Declare Scope grp_scope.
Declare Scope abgrp_scope.
Declare Scope sr_scope.
Declare Scope ring_scope.
Declare Scope lmod_scope.
Declare Scope rmod_scope.

Delimit Scope mag_scope with MA.
Delimit Scope mon_scope with MO.
Delimit Scope grp_scope with G.
Delimit Scope abgrp_scope with AG.
Delimit Scope sr_scope with SR.
Delimit Scope ring_scope with R.
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

Global Arguments mag_op {_ _} _ _ : assert.
Global Arguments mon_id {_ _} : assert.
Global Arguments grp_inv {_ _} _ : assert.
Global Arguments abgrp_op {_ _} _ _ : assert.
Global Arguments ab_grp_id {_ _} : assert.
Global Arguments abgrp_opp {_ _} _ : assert.
Global Arguments sr_op1 {_ _} _ _ : assert.
Global Arguments sr_op2 {_ _} _ _ : assert.

Global Arguments ring_inv1 {_ _} _ : assert.
Global Arguments ring_inv2 {_ _} _ : assert.
Global Arguments ring_id1 {_ _} : assert.
Global Arguments ring_id1 {A _} : assert.
Global Arguments ring_id2 {_ _} : assert.

Global Arguments left_act {_ _ _} _ _ : assert.
Global Arguments right_act {_ _ _} _ _ : assert.

Typeclasses Transparent MagOp MonId GrpInv SrOp1 SrOp2 RingId1 RingId2 RingInv1 RingInv2 AbGrpOp AbGrpId AbGrpOpp LeftAct RightAct.

Infix "∘" := mag_op (left associativity, at level 40)  : mag_scope.
Notation "( x ∘.)" := (mag_op x) (only parsing, at level 0) : mag_scope.
Notation "(.∘ x )" := (fun y => mag_op _ x) (only parsing, at level 0) : mag_scope.
Notation "(∘)" := mag_op (only parsing) : mag_scope.

Notation "'ε'" := mon_id : mon_scope.

Notation "x ⁻¹" := (grp_inv x) (at level 1) : grp_scope.
Notation "(⁻¹)" := grp_inv (only parsing) : grp_scope.
(* Notation "x / y" := (mag_op x (grp_inv y)) : grp_scope. *)

Infix "+" := abgrp_op (left associativity, at level 50) : abgrp_scope.
Notation "(+)" := abgrp_op (only parsing) : abgrp_scope.
Notation "( x +.)" := (mag_op x) (only parsing, at level 0) : abgrp_scope.
Notation "(.+ x )" := (fun y => mag_op _ x) (only parsing, at level 0) : abgrp_scope.
Notation "0" := ab_grp_id : abgrp_scope.
Notation "- x" := (abgrp_opp x) : abgrp_scope.
Notation "(-)" := abgrp_opp (only parsing) : abgrp_scope.
Notation "x - y" := (abgrp_op x (abgrp_opp y)) : abgrp_scope.

Infix "+" := sr_op1 (left associativity, at level 50) : sr_scope.
Notation "(+)" := sr_op1 (only parsing) : sr_scope.
Infix "*" := sr_op2 (left associativity, at level 40) : sr_scope.
Notation "[*]" := sr_op2 (only parsing) : sr_scope.

Notation "x - y" := (sr_op1 x (ring_inv1 y)) : ring_scope.
Notation "- x" := (ring_inv1 x) : ring_scope.
Notation "(-)" := ring_inv1 (only parsing) : ring_scope.
Notation "x / y" := (sr_op2 x (ring_inv2 y)) : ring_scope.
Notation "(/)" := ring_inv2 (only parsing) : ring_scope.
Notation "0" := ring_id1 : ring_scope.
Notation "1" := ring_id2 : ring_scope.

Notation "(⋅)" := left_act (only parsing) : lmod_scope.
Notation "(⋅)" := right_act (only parsing) : rmod_scope.
Notation "a ⋅ b" := (left_act a%R%SR b%AG) (at level 30) : lmod_scope.
Notation "a ⋅ b" := (right_act a b) (at level 30) : rmod_scope.
(* Infix "⋅" := left_act (at level 30) : lmodule_scope. *)
(* Infix "⋅" := right_act : rmodule_scope. *)

Section Magma.

  Local Open Scope mag_scope.
  Class Magma A `{Equiv A, MagOp A} :=
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
  Class SemiGroup A `{Equiv A, MagOp A} :=
    {
      sg_setoid :> Setoid A;
      sg_proper :> Proper ((≡) ==> (≡) ==> (≡)) (∘);
      sg_assoc :> Assoc (≡) (∘)
    }.

End SemiGroup.

Section Monoid.
  Local Open Scope mag_scope.
  Local Open Scope mon_scope.

  Class Monoid A `{Equiv A, MagOp A, MonId A} :=
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

  Class CommutativeMonoid A `{Equiv A, MagOp A, MonId A} :=
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

  Class Group A `{Equiv A, MagOp A, MonId A, GrpInv A} :=
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

  Local Open Scope abgrp_scope.

  Class AbelianGroup A `{Equiv A, AbGrpOp A, AbGrpId A, AbGrpOpp A} :=
    {
      abgrp_setoid :> Setoid A;
      abgrp_proper :> Proper ((≡) ==> (≡) ==> (≡)) (+);
      abgrp_inv_proper :> Proper ((≡) ==> (≡)) (-);
      abgrp_assoc :> Assoc (≡) (+);
      abgrp_comm :> Comm (≡) (+);
      abgrp_id_l :> LeftId (≡) 0 (+);
      abgrp_id_r :> RightId (≡) 0 (+);
      abgrp_inv_l :> LeftInv (≡) 0 (-) (+);
      abgrp_inv_r :> RightInv (≡) 0 (-) (+)
    }.

End AbelianGroup.

Section SemiRing.

  Local Open Scope mag_scope.
  Local Open Scope sr_scope.

  Class SemiRing A `{Equiv A, MagOp A, SrOp2 A} :=
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
  (* Local Open Scope abgrp_scope. *)

  Class Ring A `{Equiv A, SrOp1 A, SrOp2 A, RingId1 A, RingId2 A, RingInv1 A} :=
    {
      ring_abgrp :> @AbelianGroup _ _ (+) 0 (-);
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
  (* Local Open Scope abgrp_scope. *)

  Class CommutativeRing A `{Equiv A, SrOp1 A, SrOp2 A, RingId1 A, RingId2 A, RingInv1 A} :=
    {
      cring_abgrp :> @AbelianGroup _ _ (+) 0 (-);
      cring_mon :> @CommutativeMonoid _ _ [*] 1;
      cring_distr_l :> LeftDistr (≡) [*] (+);
      cring_distr_r :> RightDistr (≡) [*] (+);
    }.

End CommutativeRing.

Section IntegralDomain.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  (* Local Open Scope abgrp_scope. *)

  Class IntegralDomain A `{Equiv A, SrOp1 A, SrOp2 A, RingId1 A, RingId2 A, RingInv1 A} :=
    {
      dom_abgrp :> @AbelianGroup _ _ (+) 0 (-);
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
  Local Open Scope abgrp_scope.
  Local Open Scope lmod_scope.

  Class LeftModule A B `{Equiv A, AbGrpOp A, AbGrpId A, AbGrpOpp A, Equiv B, SrOp1 B, SrOp2 B, RingId1 B, RingId2 B, RingInv1 B, LeftAct A B} :=
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

  Class LeftAlgebra A B `{Equiv A, SrOp1 A, SrOp2 A, RingId1 A, RingId2 A, RingInv1 A, Equiv B, SrOp1 B, SrOp2 B, RingId1 B, RingId2 B, RingInv1 B, LeftAct A B} :=
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
