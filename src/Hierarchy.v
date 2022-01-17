(* Require Import ZArith. *)
(* Require Export Coq.Classes.RelationClasses. *)
(* Require Export Coq.Relations.Relations. *)
(* Require Import Coq.Classes.Morphisms. *)

(* Open Scope Z. *)

(* Context {equiv : relation Z} *)
(*         {equiv_Eq : Equivalence equiv} *)
(*         {P : Z -> Z -> Prop}. *)
(*         (* {P_Proper : Proper (equiv ==> equiv ==> iff) P}. *) *)

(* Goal forall x y, equiv x y -> P y y -> P (y + x - y) (x + y - y). *)
(*   intros. *)

(*   ring_simplify. *)
(*   ring_simplify (y + x - y). *)
(*   rewrite H. *)
(*   assumption. *)

(* Goal  *)

Require Import AAC_tactics.AAC.
From stdpp Require Export base.
(* From stdpp Require Import option options. *)
(* Require Export Coq.Classes.RelationClasses. *)
(* Require Export Coq.Relations.Relations. *)
(* Require Import Coq.Classes.Morphisms. *)

(* From BY Require Import ListLemmas. *)
(* Context *)
(*   {A : Type} *)
(*   {f : A -> A} *)
(*   {equiv : relation A} *)
(*   `{Equivalence A equiv} *)
(*   {f_proper : Proper (equiv ==> equiv) f}.   *)

(* Goal forall (x y : A), x = y -> f x = f y. *)
(*   intros. *)
(*   apply f_equal. *)
(*   assumption. Qed. *)

(* Goal forall (x y : A), equiv x y -> equiv (f x) (f y). *)
(*   intros. *)
(*   f_equiv. *)
(*   fail apply f_equal. *)
(*   assumption. *)


(* Class Monoid_op A := monoid_op : A -> A -> A. *)
(* Class Monoid_id A := monoid_id : A. *)
(* Class Monoid_inv A := monoid_inv : A -> A. *)

(* Typeclasses Transparent Monoid_op Monoid_id Monoid_inv. *)
Global Generalizable All Variables.
(* Generalizable Variables A B C D E F G. *)
(* Global Set Automatic Introduction. *)
Require Import ZArith.
(* Check Equiv Z. *)
Class ModEquiv A B := modequiv :> A -> relation B.
(* Global Instance ModEquivEquiv `{ModEquiv A B} (a : A) : Equiv B := modequiv a. *)
(* About ModEquivEquiv. *)
(* Class Sub A := sub :> A -> Prop. *)

(* Definition In {A} (P : Sub A) x := P x. *)

Locate "≡".

(* Infix "=" := equiv : type_scope. *)
(* Notation "(=)" := equiv (only parsing). *)
(* Infix "<>" := (complement equiv) : type_scope. *)
Notation "a ≃ b 'md' p" := ((@equiv _ (modequiv p)) a b) (at level 90).
(* Infix "∼" := rel (at level 70) : type_scope. *)
Notation "(≃ p )" := (modequiv p) (only parsing).
Infix "a ≄ b 'md' p" := (complement (modequiv p) a b) (at level 70) : type_scope.
(* Notation "x ∈ P" := (In P x) (at level 70). *)
Check equiv.
Check Equivalence.

Class Setoid A `{Equiv A} := setoid :> Equivalence (≡).
(* Class Suboid A `{Setoid A} (P : Sub A) := sub_proper :> Proper ((=) ==> iff) (In P). *)

Class SetoidMorph {A} {B} (f : A -> B) `{Equiv A, Equiv B} :=
  {
    setmor_dom : Setoid A;
    setmor_cod : Setoid B;
    setmor_proper :> Proper ((≡) ==> (≡)) f
  }.

(* Class BinOp A B C := bin_op : A -> B -> C. *)
(* Class BinId A := bin_id : A. *)
(* Class BinInv A B := bin_inv : A -> B. *)

(* Typeclasses Transparent BinOp BinId BinInv *)
(* Typeclasses Transparent (* Equiv *) ModEquiv. (* Rel. *) *)

(* Declare Scope bin_scope. *)

(* Infix "∘" := bin_op (at level 60) : bin_scope. *)
(* Notation "(∘)" := bin_op (only parsing) : bin_scope. *)
(* Notation "'ε'" := bin_id : bin_scope. *)
(* Notation "x ⁻" := (bin_inv x) (at level 1) : bin_scope. *)
(* Notation "(⁻)" := bin_inv (only parsing) : bin_scope. *)

Section BinOp.

  Class Congruence {A} (rel : relation A) (op : A -> A -> A) :=
    {
      cong_equiv :> Equivalence rel;
      cong_proper :> Proper (rel ==> rel ==> rel) op
    }.
(*   (* Check Assoc. *) *)

(*   Class Associative {A} {B} {C} {D} {E} {F} `{Equiv F} *)
(*         (bcd : B -> C -> D) *)
(*         (adf : A -> D -> F) *)
(*         (abe : A -> B -> E) *)
(*         (ecf : E -> C -> F) := *)
(*     associative : forall x y z, adf x (bcd y z) = ecf (abe x y) z. *)
(*   Class Commutative {A} {B} {C} `{Equiv C} *)
(*         (abc : A -> B -> C) *)
(*         (bac : B -> A -> C) := *)
(*     commutative : forall x y, abc x y = bac y x. *)
(*   Class LeftIdentity {A} {B} `{Equiv A} *)
(*         (baa : B -> A -> A) *)
(*         (b : B) := *)
(*     left_identity : forall x, baa b x = x. *)
(*   Class RightIdentity {A} {B} `{Equiv A} *)
(*         (aba : A -> B -> A) *)
(*         (b : B) := *)
(*     right_identity : forall x, aba x b  = x. *)
  (* Class LeftInv {A} {B} `{Equiv C} *)
  (*       (abc : A -> B -> C) *)
  (*       (ba : B -> A) *)
  (*       (c : C) := *)
  (*   left_inverse : forall x, abc (ba x) x = c. *)
  (* Class RightInv {A} {B} `{Equiv C} *)
  (*       (abc : A -> B -> C) *)
  (*       (ab : A -> B) *)
  (*       (c : C) := *)
  (*   right_inverse : forall x, abc x (ab x) = c. *)
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
(*   Class LeftDistributive {A} {B} {C} {D} {E} {F} {G} `{Equiv G} *)
(*         (adg : A -> D -> G) *)
(*         (bcd : B -> C -> D) *)
(*         (abe : A -> B -> E) *)
(*         (acf : A -> C -> F) *)
(*         (efg : E -> F -> G) := *)
(*     left_distributive : forall x y z, adg x (bcd y z) = efg (abe x y) (acf x z). *)
(*   Class RightDistributive {A} {B} {C} {D} {E} {F} {G} `{Equiv G} *)
(*         (abd : A -> B -> D) *)
(*         (dcg : D -> C -> G) *)
(*         (ace : A -> C -> E) *)
(*         (bcf : B -> C -> F) *)
(*         (efg : E -> F -> G) := *)
  (*     right_distributive : forall x y z, dcg (abd x y) z = efg (ace x z) (bcf y z). *)
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
  (*   Class ZeroRule {A} {B} {C} `{Equiv A, Equiv B, Equiv C} *)
(*         (abc : A -> B -> C) *)
(*         (a : A) *)
(*         (b : B) *)
(*         (c : C) := *)
  (*     zero_rule : forall x y, x <> a -> y <> b -> abc x y <> c. *)
  Class LeftCancel {A} (rel : relation A) (f : A -> A -> A) :=
    left_cancel : forall x y z, rel (f x y) (f x z) -> rel y z.
  Class RightCancel {A} (rel : relation A) (f : A -> A -> A) :=
    right_cancel : forall x y z, rel (f x y) (f z y) -> rel x z.
  Class ZeroRule2 {A} (rel : relation A) (a : A) (f : A -> A -> A) :=
    zero_rule2 : forall x y, not (rel x a) -> not (rel y a) -> not (rel (f x y) a).
  Class ZeroRule1 {A} (rel : relation A) (a : A) (f : A -> A -> A) :=
    zero_rule1 : forall x y, rel (f x y) a -> rel x a \/ rel y a.
(*   Class Closed {A} (P : A -> Prop) (op : A -> A -> A) := *)
(*     closed : forall x y, P x -> P y -> P (op x y). *)

End BinOp.

Section AAC.
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
End AAC.

Class MagOp A := mag_op : A -> A -> A.
Class MonId A := mon_id : A.
Class GrpInv A := grp_inv : A -> A.
Class AbGrpOp A := abgrp_op :> MagOp A.
Class AbGrpId A := abgrp_id :> MonId A.
Class AbGrpOpp A := abgrp_opp :> GrpInv A.
Class SrOp1 A := sr_op1 :> MagOp A.
Class SrOp2 A := sr_op2 :> MagOp A.
Class RingInv1 A := ring_inv1 :> GrpInv A.
Class RingInv2 A := ring_inv2 :> GrpInv A.
Class RingId1 A := ring_id1 :> MonId A.
Class RingId2 A := ring_id2 :> MonId A.

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

(* Global Arguments equiv /. *)
(* Global Arguments modequiv /. *)
Global Arguments complement /.

Global Arguments mag_op {!_ _} _ _ : assert.
Global Arguments mon_id {!_ _} : assert.
Global Arguments grp_inv {! _ _} _ : assert.
Global Arguments abgrp_op {!_ _} _ _ : assert.
Global Arguments abgrp_id {!_ _} : assert.
Global Arguments abgrp_opp {! _ _} _ : assert.
Global Arguments sr_op1 {!_ _} _ _ : assert.
Global Arguments sr_op2 {!_ _} _ _ : assert.

Global Arguments ring_inv1 {! _ _} _ : assert.
Global Arguments ring_inv2 {! _ _} _ : assert.
Global Arguments ring_id1 {!_ _} : assert.
Global Arguments ring_id2 {!_ _} : assert.

Typeclasses Transparent MagOp MonId GrpInv SrOp1 SrOp2 RingId1 RingId2 RingInv1 RingInv2 AbGrpOp AbGrpId AbGrpOpp.

Declare Scope mag_scope.
Declare Scope mon_scope.
Declare Scope grp_scope.
Declare Scope abgrp_scope.
Declare Scope sr_scope.
Declare Scope ring_scope.
Delimit Scope sr_scope with sr.
Delimit Scope ring_scope with ring.

Infix "∘" := mag_op (left associativity, at level 40)  : mag_scope.
(* Notation "( x ∘)" := (mag_op x) (only parsing, at level 70) : mag_scope. *)
(* Notation "(∘ x )" := (fun y => mag_op _ x) (only parsing, at level 70) : mag_scope. *)
Notation "(∘)" := mag_op (only parsing) : mag_scope.

Notation "'ε'" := mon_id : mon_scope.

Notation "x ⁻¹" := (grp_inv x) (at level 1) : grp_scope.
Notation "(⁻¹)" := grp_inv (only parsing) : grp_scope.
(* Notation "x / y" := (mag_op x (grp_inv y)) : grp_scope. *)

Infix "+" := abgrp_op (left associativity, at level 50) : abgrp_scope.
Notation "(+)" := abgrp_op (only parsing) : abgrp_scope.
(* Notation "( x +)" := (mag_op x) (only parsing, at level 70) : abgrp_scope. *)
(* Notation "(+ x )" := (fun y => mag_op _ x) (only parsing, at level 70) : abgrp_scope. *)
Notation "0" := abgrp_id : abgrp_scope.
Notation "- x" := (abgrp_opp x) : abgrp_scope.
Notation "(-)" := abgrp_opp (only parsing) : abgrp_scope.
Notation "x - y" := (abgrp_op x (abgrp_opp y)) : abgrp_scope.

(* Infix "+" := sr_op1 (left associativity, at level 50) : sr_scope. *)
(* Notation "(+)" := sr_op1 (only parsing) : sr_scope. *)
Infix "*" := sr_op2 (left associativity, at level 40) : sr_scope.
Notation "[*]" := sr_op2 (only parsing) : sr_scope.

Notation "x - y" := (sr_op1 x (ring_inv1 y)) : ring_scope.
Notation "- x" := (ring_inv1 x) : ring_scope.
Notation "(-)" := ring_inv1 (only parsing) : ring_scope.
Notation "x / y" := (sr_op2 x (ring_inv2 y)) : ring_scope.
Notation "(/)" := ring_inv2 (only parsing) : ring_scope.
Notation "0" := ring_id1 : ring_scope.
Notation "1" := ring_id2 : ring_scope.

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
  Local Open Scope abgrp_scope.

  Class Ring A `{Equiv A, AbGrpOp A, SrOp2 A, AbGrpId A, RingId2 A, AbGrpOpp A} :=
    {
      ring_abgrp :> @AbelianGroup _ _ (+) 0 (-);
      ring_mon :> @Monoid _ _ [*] 1;
      ring_distr_l :> LeftDistr (≡) [*] (+);
      ring_distr_r :> RightDistr (≡) [*] (+)
    }.
End Ring.

Section CommutativeRing.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope abgrp_scope.

  Class CommutativeRing A `{Equiv A, AbGrpOp A, SrOp2 A, AbGrpId A, RingId2 A, AbGrpOpp A} :=
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
  Local Open Scope abgrp_scope.

  Class IntegralDomain A `{Equiv A, AbGrpOp A, SrOp2 A, AbGrpId A, RingId2 A, AbGrpOpp A} :=
    {
      dom_abgrp :> @AbelianGroup _ _ (+) 0 (-);
      dom_mon :> @CommutativeMonoid _ _ [*] 1;
      dom_distr_l :> LeftDistr (≡) [*] (+);
      dom_distr_r :> RightDistr (≡) [*] (+);
      dom_non_trivial : 0 ≢ 1;
      dom_zero_rule :> ZeroRule1 (≡) 0 [*]
    }.

End IntegralDomain.

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


Section Magma.

  Local Open Scope mag_scope.

  Class MagCongruence `{Magma A} (rel : relation A) :=
    {
      mag_cong_equiv :> Equivalence rel;
      mag_cong_proper :> Proper (rel ==> rel ==> rel) (∘)
    }.

  Context `{Magma A}
          {rel : relation A}
          `{!MagCongruence rel}.

  Instance : @Magma _ rel _.
  Proof. repeat split; try apply _. Qed.

End Magma.

Ltac substructure := repeat split; try apply _.

Section SemiGroup.

  Local Open Scope mag_scope.
  Context `{SemiGroup A}.

  Global Instance : Magma A.
  Proof. repeat split; apply _. Qed.

  Context
    {rel : relation A}
    `{!MagCongruence rel}
    `{subrelation A (≡) rel}.

  Instance quot_sg : @SemiGroup _ rel _.
  repeat split; try apply _.
  cbv; intros; apply is_subrelation. eapply assoc; exact _. Qed.

End SemiGroup.

Require Import List.
Require Import ZArith.
Require Import Znumtheory.
Require Import Coq.micromega.Lia.

Section __.
  Context `{Setoid A}.
  Import ListNotations.

  Inductive list_equiv : Equiv (list A) :=
  | nil_eq : list_equiv [] []
  | cons_eq a l b k : a = b -> list_equiv l k -> list_equiv (a :: l) (b :: k).
  Global Existing Instance list_equiv.
  Global Instance : @Reflexive (list A) (=).
  Proof.
    red; induction x.
    - constructor.
    - now constructor.
  Qed.
  Global Instance : @Symmetric (list A) (=).
  Proof.
    red; induction x; intros.
    - inversion H1. constructor.
    - inversion H1. subst.
      constructor.
      symmetry. assumption.
      apply IHx. assumption.
  Qed.
  Global Instance : @Transitive (list A) (=).
  Proof.
    red; induction x; intros.
    - inversion H1. subst. assumption.
    - inversion H1. subst.
      inversion H2. subst.
      constructor.
      etransitivity; eassumption.
      eapply IHx; eassumption.
  Qed.
  Global Instance : Setoid (list A).
  Proof. repeat split; apply _. Qed.

  Global Instance : Proper ((=) ==> (=) ==> (=)) (@cons A).
  Proof. do 3 red; intros; constructor; assumption. Qed.
  Global Instance : Proper ((=) ==> (=) ==> (=)) (@app A).
  Proof.
    do 3 red; induction x; intros.
    - now inversion H1; subst.
    - inversion H1; subst. simpl. f_equiv. assumption. apply IHx. assumption. assumption.
  Qed.
  Global Instance : Proper ((=) ==> (=)) (@rev A).
  Proof.
    do 3 red; induction x; intros.
    - inversion H1. constructor.
    - inversion H1; subst. simpl. f_equiv.
      apply IHx. assumption. rewrite H4. reflexivity.
  Qed.
End __.

Section __.
  Context `{SemiGroup A}.

  Local Open Scope mag_scope.

  Global Instance fold_left_proper (f : A -> A -> A) `{!Proper ((=) ==> (=) ==> (=)) f} :
    Proper ((=) ==> (=) ==> (=)) (fold_left f).
  Proof.
    do 3 red.
    induction x; intros.
    - inversion H2. subst. auto.
    - inversion H2. subst. simpl.
      rewrite IHx. reflexivity.
      assumption. rewrite H3. rewrite H6. reflexivity.
  Qed.

  Lemma fold_left_assoc (a b : A) ls :
     a ∘ (fold_left (∘) ls b) = fold_left (∘) ls (a ∘ b).
  Proof.
    revert b; induction ls; intros b; simpl.
    - reflexivity.
    - rewrite IHls. rewrite associative. reflexivity.
  Qed.
End __.

Section Monoid.

  Local Open Scope mag_scope.
  Local Open Scope mon_scope.
  Local Open Scope nat_scope.

  Context
    `{Monoid A}.

  Global Instance : SemiGroup A.
  Proof. repeat split; first [apply _ | exact _]. Qed.

  Context
    {rel : relation A}
    `{!MagCongruence rel}
    `{subrelation A (≡) rel}.

  Instance quot_mon : @Monoid _ rel _ _.
  repeat split; try apply _;
  cbv; intros; apply is_subrelation; (apply assoc; exact _) || (apply right_id; exact _) || (apply left_id; exact _). Qed.

  Context (f : nat -> A).

  Definition big_op_list (l : list nat) f := fold_left (∘) (map f l) ε.
  Definition big_op f n m := big_op_list (seq n (m - n)) f.
  Definition big_op_rev f n m := big_op_list (rev (seq n (m - n))) f.

  Hint Unfold big_op big_op_rev big_op_list : bigop.

  Lemma big_op_S_r n m (nltm : n <= m) :
    big_op f n (S m) = big_op f n m ∘ f m.
  Proof. unfold big_op, big_op_list.
         now rewrite Nat.sub_succ_l, seq_snoc, map_app, fold_left_app, <- le_plus_minus. Qed.

  Lemma big_op_S_l n m (nltm : n <= m) :
    big_op f n (S m) = f n ∘ big_op f (S n) (S m).
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, fold_left_assoc; auto.
         simpl. rewrite mon_id_l, mon_id_r. reflexivity. Qed.

  Lemma big_op_rev_S_r n m (nltm : n <= m) :
    big_op_rev f n (S m) = big_op_rev f (S n) (S m) ∘ f n.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l by auto; simpl; rewrite map_app, fold_left_app. reflexivity. Qed.

  Lemma big_op_rev_S_l n m (nltm : n <= m) :
    big_op_rev f n (S m) = f m ∘ big_op_rev f n m.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, rev_app_distr, fold_left_assoc, <- le_plus_minus, (mon_id_r (f m)) by auto; simpl;
           rewrite (mon_id_l (f m)); auto. reflexivity. Qed.

  Lemma big_op_rev_nil n m (mltn : m <= n) :
    big_op_rev f n m = ε.
  Proof. unfold big_op_rev; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_nil n m (mltn : m <= n) :
    big_op f n m = ε.
  Proof. unfold big_op; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_split n m k (nmk : n <= m <= k) :
    (big_op f n m) ∘ (big_op f m k) = big_op f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n ≡ 0); assert (m ≡ 0); subst; try lia. rewrite big_op_nil, mon_id_l. reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_nil (S k)), mon_id_r. reflexivity. lia.
      + rewrite big_op_S_r, associative, IHk, <- big_op_S_r by lia. reflexivity. Qed.

  Lemma big_op_rev_split n m k (nmk : n <= m <= k) :
    (big_op_rev f m k) ∘ (big_op_rev f n m) = big_op_rev f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n ≡ 0); assert (m ≡ 0); try lia; subst. rewrite big_op_rev_nil, mon_id_l. reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_rev_nil (S k)), mon_id_l. reflexivity. lia.
      + rewrite big_op_rev_S_l, <- associative, IHk, <- big_op_rev_S_l by lia. reflexivity. Qed.

  Lemma map_seq_ext (g : nat -> A) (n m k : nat) :
        (forall i : nat, n <= i < m + k -> f i = g (i + (m - n))%nat) ->
        n <= m ->
    map f (seq n k) = map g (seq m k).
  Proof.
    generalize dependent m; generalize dependent n. induction k as [|k IHk]; intros; simpl.
    - reflexivity.
    - rewrite H6 by lia; replace (n + (m - n))%nat with m by lia.
      rewrite (IHk (S n) (S m)); [reflexivity| |lia].
      intros; rewrite Nat.sub_succ; apply H6; lia. Qed.

  Lemma big_op_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op f n m = big_op g (n + k) (m + k).
  Proof.
    intros. unfold big_op, big_op_list.
    apply fold_left_proper.
    apply _.
    replace (m + k - (n + k)) with (m - n) by lia.
    apply map_seq_ext. intros. rewrite H6. f_equiv. lia. lia. reflexivity. Qed.

  Lemma big_op_rev_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op_rev f n m = big_op_rev g (n + k) (m + k).
  Proof.
    intros. unfold big_op_rev, big_op_list. apply fold_left_proper; [apply _| |reflexivity].
    rewrite !map_rev. replace (m + k - (n + k)) with (m - n) by lia.
    f_equiv. apply map_seq_ext; intros. rewrite H6. f_equiv. lia. lia. Qed.
End Monoid.

Section CommutativeMonoid.
  Local Open Scope mag_scope.
  Local Open Scope mon_scope.

  Context
    `{CommutativeMonoid A}.

  Global Instance : SemiGroup A.
  Proof. repeat split; first [apply _ | exact _]. Qed.

End CommutativeMonoid.

Require Import Coq.Classes.SetoidTactics.

Section Group.
  Local Open Scope mag_scope.
  Local Open Scope mon_scope.
  Local Open Scope grp_scope.

  Class GrpCongruence `{Group A} (rel : relation A) :=
    {
      grp_cong_equiv :> Equivalence rel;
      grp_cong_op_proper :> Proper (rel ==> rel ==> rel) (∘);
      grp_cong_inv_proper :> Proper (rel ==> rel) (⁻¹)
    }.

  Context `{Group A}.

  Global Instance : Monoid A.
  Proof. repeat split; first [apply _ | exact _]. Qed.

  Hint Rewrite (@assoc _ (≡) (∘)) using (apply _; exact _): group_simplify.
  Hint Rewrite (@left_id _ (≡)) (@right_id _ (≡)) (@left_inv _ (≡)) (@right_inv _ (≡)) using (apply _; exact _): group_cancellation.

  Ltac group_simplify :=
    rewrite_strat
      (try bottomup (hints group_simplify));
    (try bottomup (choice (hints group_cancellation) <- (@assoc _ (≡)))).
  Ltac group_simplify_in H :=
    rewrite_strat
      (try bottomup (hints group_simplify));
    (try bottomup (choice (hints group_cancellation) <- assoc)) in H.
  Ltac group := group_simplify; try apply _;  easy.

  Context
    {rel : relation A}.

  Instance quot_grp `{!GrpCongruence rel} `{subrelation A (≡) rel} : @Group _ rel _ _ _.
  Proof.
    repeat split; try apply _;
      red; intros; apply is_subrelation.
    - apply assoc. exact _.
    - apply left_id. exact _.
    - apply right_id. exact _.
    - apply left_inv. exact _.
    - apply right_inv. exact _.
  Qed.
  Check quot_grp.

  Lemma grp_op_inj_l : forall x y z, x ∘ y ≡ x ∘ z -> y ≡ z.
  Proof.
    intros.
    setoid_replace y with (x⁻¹ ∘ (x ∘ y)) by group.
    rewrite H4.
    group.
  Qed.

  Lemma grp_op_inj_r : forall x y z, y ∘ x ≡ z ∘ x -> y ≡ z.
  Proof.
    intros.
    setoid_replace y with (y ∘ x ∘ x⁻¹) by group.
    rewrite H4.
    group.
  Qed.

  Lemma grp_inv_unique_r : forall x y : A, x ∘ y ≡ ε -> y ≡ x⁻¹.
  Proof.
    intros.
    apply (grp_op_inj_l x).
    group.
  Qed.

  Lemma grp_inv_unique_l : forall x y : A, y ∘ x ≡ ε -> y ≡ x⁻¹.
  Proof.
    intros.
    apply (grp_op_inj_r x).
    group.
  Qed.

  Lemma grp_op_inv : forall x y, (x ∘ y)⁻¹ ≡ y⁻¹ ∘ x⁻¹.
    intros.
    symmetry.
    apply grp_inv_unique_r.
    group.
  Qed.

  Lemma grp_inv_inv : forall x, (x ⁻¹) ⁻¹ ≡ x.
  Proof.
    intros.
    symmetry.
    apply grp_inv_unique_r.
    group.
  Qed.

  Hint Rewrite grp_op_inv grp_inv_inv using apply _: group_cancellation.

  (* Class Subgroup (P : Sub A) := *)
  (*   { *)
  (*     subgrp_suboid :> Suboid A P; *)
  (*     subgrp_id : ε ∈ P; *)
  (*     subgrp_inv : forall x, x ∈ P -> x⁻¹ ∈ P; *)
  (*     subgrp_closed : forall x y, x ∈ P -> y ∈ P -> x ∘ y ∈ P *)
  (*   }. *)

  (* Lemma subgrp_inv_if `{@Subgroup P} : forall x, x ⁻¹ ∈ P -> x ∈ P. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite <- grp_inv_inv. *)
  (*   apply subgrp_inv. *)
  (*   assumption. *)
  (* Qed. *)

  (* Class NormalSubgroup (P : Sub A) := *)
  (*   { *)
  (*     nsubgrp_subgrp :> Subgroup P; *)
  (*     nsubgrp_normal : forall x y, x ∈ P -> y ∘ x ∘ y⁻¹ ∈ P *)
  (*   }. *)

  (* Lemma nsubgrp_normal_if `{@NormalSubgroup P} : forall x y, y ∘ x ∘ y⁻¹ ∈ P -> x ∈ P. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply nsubgrp_normal with (y0:=y⁻¹) in H5. *)
  (*   group_simplify_in H5. *)
  (*   assumption. *)
  (* Qed. *)

  (* Instance nsubgrp_rel `{@NormalSubgroup P} : Rel A := (fun x y : A => x ∘ y ⁻¹ ∈ P). *)

  (* Instance nsubgrp_rel_cong `{@NormalSubgroup P} : Congruence (∘). *)
  (* Proof. *)
  (* split; [repeat split; red; intros|];unfold rel, nsubgrp_rel in *. *)
  (* - rewrite right_inverse. *)
  (*   apply subgrp_id. *)
  (* - setoid_replace (y ∘ x ⁻¹) with ((x ∘ y ⁻¹) ⁻¹) by group. *)
  (*   apply subgrp_inv. *)
  (*   assumption. *)
  (* - setoid_replace (x ∘ z ⁻¹) with ((x ∘ y ⁻¹) ∘ (y ∘ z ⁻¹)) by group. *)
  (*   apply subgrp_closed; assumption. *)
  (* - do 3 red; intros. *)
  (*   setoid_replace (x ∘ x0 ∘ (y ∘ y0) ⁻¹) with (y ∘ ((y ⁻¹ ∘ x) ∘ (x0 ∘ y0 ⁻¹)) ∘ y ⁻¹) by group. *)
  (*   apply nsubgrp_normal. *)
  (*   apply subgrp_closed. *)
  (*   apply nsubgrp_normal_if with (y1:=y). *)
  (*   group_simplify. *)
  (*   assumption. *)
  (*   assumption. *)
  (* Qed. *)

  (* Lemma inv_unique_r : forall x y, x ∘ y ≡ ε -> y ≡ x⁻¹. *)
  (* Proof. *)
  (*   intros. *)


  (*   apply (f_equal (monoid_op (monoid_inv x))) in H3. *)
  (*   rewrite grp_assoc, grp_inv_l, grp_id_l, grp_id_r in H3. *)
  (*   assumption. *)
  (* Qed. *)

  (* Lemma inv_unique_l : forall x y, y ∘ x = id -> y = x⁻. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply (f_equal (fun a => a ∘ x⁻)) in H3. *)
  (*   rewrite <- mon_assoc, grp_inv_r, mon_id_r, mon_id_l in H3. *)
  (*   assumption. *)
  (* Qed. *)

  (* Lemma grp_r_inj : forall x y z, x ∘ y = x ∘ z -> y = z. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply (f_equal (fun y => x⁻ ∘ y)) in H3. *)
  (*   rewrite grp_assoc, grp_inv_l in H3. *)
  (*   rewrite grp_assoc, grp_inv_l in H3. *)
  (*   rewrite !grp_id_l in H3. assumption. *)
  (* Qed. *)

  (* Lemma grp_l_inj : forall y x z, x ∘ y = z ∘ y -> x = z. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply (f_equal (fun x => x ∘ y⁻)) in H3. *)
  (*   rewrite <- grp_assoc, grp_inv_r in H3. *)
  (*   rewrite <- grp_assoc, grp_inv_r in H3. *)
  (*   rewrite !grp_id_r in H3. assumption. *)
  (* Qed. *)

  (* Lemma inv_op : forall x y, (x ∘ y)⁻ = y⁻ ∘ x⁻. *)
  (* Proof. *)
  (*   intros. symmetry. *)
  (*   apply inv_unique_r. *)
  (*   rewrite grp_assoc. *)
  (*   rewrite <- (grp_assoc x y _). *)
  (*   rewrite grp_inv_r. *)
  (*   rewrite grp_id_r. *)
  (*   rewrite grp_inv_r. *)
  (*   reflexivity. *)
  (* Qed. *)

  Lemma id_inv : ε⁻¹ ≡ ε.
  Proof.
    apply (grp_op_inj_l ε).
    group.
  Qed.

  Hint Rewrite id_inv using apply _ : group_cancellation.

  (* Lemma inv_invol : forall x, x⁻⁻ = x. *)
  (* Proof. *)
  (*   intros. symmetry; apply inv_unique_r. apply grp_inv_l. *)
  (* Qed. *)

  Lemma inv_inj : forall x y, x⁻¹ ≡ y⁻¹ -> x ≡ y.
  Proof.
    intros.
    rewrite <- grp_inv_inv.
    rewrite H4.
    group.
  Qed.

  Lemma inv_id : forall x, x⁻¹ ≡ ε -> x ≡ ε.
  Proof.
    intros.
    rewrite <- grp_inv_inv.
    rewrite H4.
    group.
  Qed.

End Group.

Section AbelianGroup.

  Context `{G : AbelianGroup A}.
  Local Open Scope abgrp_scope.

  Global Instance abgrp_grp : Group A. repeat split; apply _. Qed.
  Global Instance abgrp_cmon : CommutativeMonoid A. repeat split; apply _. Qed.
  Existing Instance abgrp_grp.

  Hint Rewrite (@assoc _ (≡) (+)) using (apply _; exact _): group_simplify.
  Hint Rewrite (@left_id _ (≡)) (@right_id _ (≡)) (@left_inv _ (≡)) (@right_inv _ (≡)) using (apply _; exact _): group_cancellation.
  Hint Rewrite grp_op_inv grp_inv_inv using apply _: group_cancellation.

  Ltac group_simplify :=
    rewrite_strat
      (try bottomup (hints group_simplify));
    (try bottomup (choice (hints group_cancellation) <- (assoc (+)))).
  Ltac group_simplify_in H :=
    rewrite_strat
      (try bottomup (hints group_simplify));
    (try bottomup (choice (hints group_cancellation) <- (assoc (+)))) in H.
  Ltac group := group_simplify; try apply _;  easy.


  (* Hint Rewrite (assoc (+)) using apply _: group_simplify. *)
  (* Hint Rewrite (@left_id _ (≡)) (@right_id _ (≡)) left_inv right_inv using apply _: group_cancellation. *)

  (* Ltac group_simplify := *)
  (*   rewrite_strat *)
  (*     (try bottomup (hints group_simplify)); *)
  (*   (try bottomup (choice (hints group_cancellation) <- assoc)). *)
  (* Ltac group_simplify_in H := *)
  (*   rewrite_strat *)
  (*     (try bottomup (hints group_simplify)); *)
  (*   (try bottomup (choice (hints group_cancellation) <- assoc)) in H. *)
  (* Ltac group := group_simplify; try apply _; easy. *)
  Ltac abgrp_normalize :=
    group_simplify; aac_normalise.

  (* Hint Rewrite (@left_id _ (≡)) (@right_id _ (≡)) left_inv right_inv using apply _: abgrp_rewrite. *)

  (* Ltac abgrp_simplify := *)
  (*     repeat match goal with *)
  (*     | [ |- context [ ?a + ?b ] ] => progress let H := fresh in eassert (H : a + b ≡ _) by (abgrp_normalize; reflexivity); setoid_rewrite H; clear H *)
  (*     | [ |- context [ ?a - ?b ] ] => progress let H := fresh in eassert (H : a - b ≡ _) by (abgrp_normalize; reflexivity); setoid_rewrite H; clear H *)
  (*     | [ |- context [ - ?a ] ] => progress let H := fresh in eassert (H : - a ≡ _) by (abgrp_normalize; reflexivity); setoid_rewrite H; clear H *)
  (*     end. *)

  Ltac abgrp := abgrp_normalize; easy.


  (* Instance subgrp_ab_normal `{Subgroup A} : NormalSubgroup P. *)
  (*   intros; split; intros. *)
  (*   - assumption. *)
  (*   - assert ((y + x - y) = x). aac_rewrite left_inverse.   abgrp_simplify. *)
  (* Qed. *)

  Definition abgrp_add_0_r : forall x, x + 0 ≡ x := right_id 0 (+).

  Definition opp_0 : forall x, - x ≡ 0 -> x ≡ 0 := inv_id.
  Definition opp_unique_l : forall x y : A, y + x ≡ 0 -> y ≡ - x := grp_inv_unique_l.
  Definition opp_unique_r : forall x y : A, x + y ≡ 0 -> y ≡ - x := grp_inv_unique_r.
  Definition opp_inj : forall x y, - x ≡ - y -> x ≡ y := inv_inj.

End AbelianGroup.

Require Import Coq.setoid_ring.Ring.

Section SemiRing.
  Local Open Scope sr_scope.
  Local Open Scope mag_scope.

  Class SemiRingCongruence `{SemiRing A} (rel : relation A) :=
    {
      sr_cong_equiv :> Equivalence rel;
      sr_cong_op1_proper :> Proper (rel ==> rel ==> rel) (∘);
      sr_cong_op2_proper :> Proper (rel ==> rel ==> rel) [*];
    }.

  Context `{SemiRing A}.

  Instance quot_sr `{!SemiRingCongruence rel} `{subrelation A (≡) rel} : @SemiRing _ rel _ _.
  Proof.
    repeat split; try apply _;
      red; intros; apply is_subrelation.
    - apply (left_distr [*] (∘)).
    - apply (right_distr [*] (∘)).
  Qed.

End SemiRing.
(* From stdpp Require Import options. *)
(* From stdpp Require Import option. *)

Section Ring.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope abgrp_scope.

  Context
    `{Ring A}.

  Class RingCongruence (rel : relation A) :=
    {
      ring_cong_equiv :> Equivalence rel;
      ring_cong_op1_proper :> Proper (rel ==> rel ==> rel) (+);
      ring_cong_op2_proper :> Proper (rel ==> rel ==> rel) [*];
      ring_cong_inv_proper :> Proper (rel ==> rel) (-)
    }.

  (* Instance : @AbelianGroup A _ (+) 0 (-) := _. *)
  (* Instance : @Group A _ (+) 0 (-) := _. *)

  (* split. *)
  (* repeat split; try apply _; try exact _. exact _. *)

  (* Global Instance mul_1_r : @RightId _ _ ring_op 1 := right_identity. *)
  (* Global Instance mul_1_l : @LeftIdentity _ _ ring_op 1 := left_identity. *)

  (* Global Instance mul_assoc : @Associative _ ring_op := associative. *)

  (* Global Instance mul_add_distr_l : LeftDistributive := left_distributive. *)
  (* Global Instance mul_add_distr_r : RightDistributive := right_distributive. *)

  Lemma mul_0_r : forall x : A, x * 0 ≡ 0.
  Proof.
    intros.
    setoid_replace (x * 0) with (x * 0 + 0) by (symmetry; apply (right_id 0 (+))).
    setoid_replace 0 with (x * 0 - x * 0) at 3 by (symmetry; apply (right_inv 0 (-) (+))).
    setoid_rewrite (assoc (+)).
    setoid_rewrite <- (left_distr [*] (+)).
    setoid_rewrite (left_id 0 (+)).
    apply (right_inv 0 (-) (+)).
  Qed.

  Lemma mul_0_l : forall x, 0 * x ≡ 0.
  Proof.
    intros.
    setoid_replace (0 * x) with (0 * x + 0) by (symmetry; apply (right_id 0 (+))).
    setoid_replace 0 with (0 * x - 0 * x) at 3 by (symmetry; apply (right_inv 0 (-) (+))).
    setoid_rewrite (assoc (+)).
    setoid_rewrite <- (right_distr [*] (+)).
    setoid_rewrite (left_id 0 (+)).
    apply (right_inv 0 (-) (+)).
  Qed.

  Definition ring_opp_unique_l : forall x y : A, y + x ≡ 0 -> y ≡ - x := grp_inv_unique_l.

  Lemma opp_mul_l : forall x y, - (x * y) ≡ - x * y.
  Proof.
    intros. symmetry.
    apply ring_opp_unique_l.
    rewrite <- (right_distr [*] (+)).
    setoid_rewrite (left_inv 0 (-) (+)).
    apply mul_0_l.
  Qed.

  Lemma opp_mul_r : forall x y, - (x * y) ≡ x * - y.
  Proof.
    intros. symmetry.
    apply ring_opp_unique_l.
    rewrite <- (left_distr [*] (+)).
    setoid_rewrite (left_inv 0 (-) (+)).
    apply mul_0_r.
  Qed.

End Ring.

Section CommutativeRing.

  Context
    {A : Type}
    `{CommutativeRing A}.
  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope abgrp_scope.

  Global Instance : Ring A.
  Proof. repeat split; apply _. Qed.

  Ltac solve_tc :=
    first [ apply reflexivity | apply assoc | apply comm | apply right_id | apply left_id | apply right_inv | apply left_inv | apply left_distr | apply right_distr ]; exact _.

  Instance quot_cring (rel : relation A) `{!RingCongruence rel} `{subrelation A (≡) rel} : @CommutativeRing _ rel _ _ _ _ _.
  Proof.
    repeat split; try apply _;
      red; intros; apply is_subrelation; solve_tc.
  Qed.

  Lemma cring_ring_theory : @ring_theory A 0 1 (+) [*] (fun x y : A => x - y) (-) (≡).
  Proof.
    split; intros; try solve_tc.
  Qed.
  (* Set Printing All. *)
  Add Ring cring_is_ring : cring_ring_theory.
  Check cring_ring_theory.

  (* Existing Instance abgrp_grp. *)

  (* Class Ideal := *)
  (*   { *)
  (*     ideal_subgroup :> Subgroup; *)
  (*     ideal_closed : forall x y, x ∈ P -> y * x ∈ P *)
  (*   }. *)

  (* Existing Instance subgrp_ab_normal. *)
  (* Existing Instance nsubgrp_rel. *)

  (* Instance ideal_nsubgrp `{Ideal} : NormalSubgroup P. *)


  (* Instance ideal_rel `{Ideal} : Rel A := (fun x y : A => x - y ∈ P). *)

  Tactic Notation "replace" constr(T1) "with" constr(T2) "by" tactic3(tac) :=
    let H := fresh in
    assert (H : T1 = T2) by tac; rewrite H || rewrite <- H; clear H.

  (* Global Instance ideal_rel_op1_cong `{Ideal} : Congruence (+) := nsubgrp_rel_cong. *)
  (* Global Instance ideal_rel_op2_cong `{Ideal} : Congruence [*]. *)
  (* split. *)
  (* - apply _. *)
  (* - do 3 red; intros. *)
  (*   cbv -[sr_op1 sr_op2 ring_inv1 In]. *)
  (*   replace (x * x0 - y * y0) with ((x0 * (x - y)) + (y * (x0 - y0))) by ring. *)
  (*   apply subgrp_closed. *)
  (*   apply ideal_closed. assumption. *)
  (*   apply ideal_closed. assumption. *)
  (* Qed. *)

  Definition div a b := exists k, k * a ≡ b.
  Definition mul a b := div b a.

  Infix "|" := div (at level 70).

  Global Instance div_equiv_ModEquiv : ModEquiv A A := fun a => (fun b c => a | b - c).
  Global Arguments div_equiv_ModEquiv /.

  Global Instance : forall a, subrelation (≡) (≃a).
  Proof.
    repeat red; intros. exists 0. rewrite H6. ring.
  Qed.

  Global Instance : forall a, Reflexive (≃a).
  Proof.
    repeat red; intros; exists 0; ring.
  Qed.

  Global Instance : forall a, Symmetric (≃a).
  Proof.
    repeat red; intros.
    destruct H6 as [z].
    exists (- z).
    setoid_replace (- z * a) with (- (z * a)) by ring.
    rewrite H6.
    ring.
  Qed.
  Global Instance : forall a, Transitive (≃a).
  Proof.
    repeat red; intros.
    destruct H6 as [z0], H7 as [z1].
    exists (z0 + z1).
    rewrite (right_distr [*] (+)).
    rewrite H6, H7.
    ring.
  Qed.

  Global Instance : forall a, Equivalence (≃ a).
  Proof. split; apply _. Qed.

  Global Instance : forall a, Proper ((≃a) ==> (≃a) ==> (≃a)) (+).
  Proof.
    repeat red; intros.
    destruct H6 as [z0], H7 as [z1].
    exists (z0 + z1).
    rewrite (right_distr [*] (+)).
    rewrite H6, H7.
    ring.
  Qed.

  Global Instance : forall a, Proper ((≃a) ==> (≃a) ==> (≃a)) [*].
  Proof.
    repeat red; intros.
    destruct H6 as [z0 Hz], H7 as [w0 Hw].
    exists (y0 * z0 + x * w0).
    rewrite (right_distr [*] (+)).
    rewrite <- !(assoc [*]).
    rewrite Hz, Hw.
    ring.
  Qed.

  Global Instance : forall a, Proper ((≃a) ==> (≃a)) (-).
  Proof.
    repeat red; intros.
    destruct H6 as [z0].
    exists (- z0).
    setoid_replace (- z0 * a) with (- (z0 * a)) by ring.
    rewrite H6.
    ring.
  Qed.

  Global Instance : forall a, RingCongruence (≃a).
  Proof. split; apply _. Qed.

  Instance : forall a, @CommutativeRing A (≃a) _ _ _ _ _ := fun a => quot_cring (≃a).

  (* Add Ring cring_ring_theory *)

  (* Instance principal_ideal (a : A) : Ideal (mul a). *)
  (* repeat split; intros; unfold In, mul, div, mon_id, grp_inv, mag_op in *. *)
  (* - setoid_rewrite <- H6; assumption. *)
  (* - setoid_rewrite H6. assumption. *)
  (* - exists 0. ring. *)
  (* - destruct H6 as [k]. exists (- k). *)
  (*   rewrite <- H6. ring. *)
  (* - destruct H6 as [kx]. *)
  (*   destruct H7 as [ky]. *)
  (*   exists (kx + ky). *)
  (*   rewrite <- H6, <- H7. *)
  (*   ring. *)
  (* - destruct H6. *)
  (*   exists (y * x0). rewrite <- H6. *)
  (*   ring. *)
  (* Qed. *)

End CommutativeRing.
Notation "⟨ a ⟩" := (mul a).


Section IntegralDomain.

  Context `{IntegralDomain A}.

  Global Instance domain_cring : CommutativeRing A.
  Proof. repeat split; apply _. Qed.

End IntegralDomain.


Section __.
  Context (A : Type).
  Global Instance eq_Equiv : Equiv A | 10 := eq.
  Global Arguments eq_Equiv !_ /.
  Global Instance : @Setoid A eq_Equiv. constructor; congruence. Defined.

  Global Instance : Setoid A. constructor; congruence. Defined.
End __.



Section Z.

  (* Local Open Scope abgrp_scope. *)

  (* Instance : MagOp Z := Z.add. *)
  (* Instance : MonId Z := 0%Z. *)
  (* Instance : GrpInv Z := Z.opp. *)

  (* Instance : RightIdentity (+) 0 := Z.add_0_r. *)
  (* Instance : LeftIdentity (+) 0 := Z.add_0_l. *)
  (* Instance : Associative (+) (+) (+) (+) := Z.add_assoc. *)
  (* Instance : Commutative (+) (+) := Z.add_comm. *)
  (* Instance : LeftInverse (+) (-) 0 := Z.add_opp_diag_l. *)
  (* Instance : RightInverse (+) (-) 0 := Z.add_opp_diag_r. *)

  (* Instance : AbelianGroup Z. repeat (split; try apply _). Qed. *)

  Instance : AbGrpOp Z := Z.add.
  Instance : SrOp2 Z := Z.mul.
  Instance : AbGrpId Z := Z0.
  Instance : RingId2 Z := 1%Z.
  Instance : AbGrpOpp Z := Z.opp.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope abgrp_scope.

  Instance : RightId (=) 0 (+) := Z.add_0_r.
  Instance : LeftId (=) 0 (+) := Z.add_0_l.
  Instance : RightId (=) 1 [*] := Z.mul_1_r.
  Instance : LeftId (=) 1 [*] := Z.mul_1_l.
  Instance : Assoc (=) (+) := Z.add_assoc.
  Instance : Comm (=) (+) := Z.add_comm.
  Instance : Assoc (=) [*] := Z.mul_assoc.
  Instance : Comm (=) [*] := Z.mul_comm.
  Instance : LeftInv (=) 0 (-) (+) := Z.add_opp_diag_l.
  Instance : RightInv (=) 0 (-) (+) := Z.add_opp_diag_r.
  Instance : LeftDistr (=) [*] (+) := Z.mul_add_distr_l.
  Instance : RightDistr (=) [*] (+) := Z.mul_add_distr_r.
  Instance : ZeroRule1 (=) 0 [*]. repeat red; intros. cbv -[Z.mul] in *; lia. Qed.

(* Check quot. *)
(* Check SemiGroup.A. *)
(* Import SemiGroup. *)

(* Check quot. *)

(* Print quot. *)

(* Print Instances SemiGroup. *)
  (* Set Typeclasses Debug. *)
  Instance : IntegralDomain Z. repeat (split; try apply _). cbv; lia. Qed.

  Context (p : Z) (pprime : prime p).

  (* Instance : Ideal  := principal_ideal p. *)
  (* Existing Instance I. *)
  (* Existing Instance subgrp_ab_normal. *)
  (* Existing Instance nsubgrp_rel. *)
  (* Existing Instance nsubgrp_rel_cong. *)
  Check ModEquiv.
  Print Instances IntegralDomain.
  Print Instances CommutativeRing.
  Check (_ : CommutativeRing Z).
  Print Instances Equiv.
  Print Instances Ring.
  (* Add Ring cring_is_ring : cring_ring_theory. *)
  Print Rings.

  (* Instance : (subrelation eq (≃p)). *)
  (* Admitted. *)
  Check (≃p).
  (* Check quot_cring (≃p). *)
  Instance q : @CommutativeRing Z (≃p) _ _ _ _ _ | 0 := quot_cring (≃p).
  (* Set Printing All. Check q. *)
  (* Check @modequiv Z Z (@aModEquiv_instance_0 Z (eq_Equiv Z) SrOp1_instance_0 SrOp2_instance_0 RingInv1_instance_0) p. *)
  Typeclasses Transparent equiv.

  Add Ring cring_is_ring : (@cring_ring_theory Z (≃p) _ _ _ _ _ _).

  Print Rings.
  Print Instances CommutativeRing.

  Tactic Notation "replace" constr(T1) "with" constr(T2) "by" tactic3(tac) :=
    let H := fresh in
    assert (H : T1 = T2) by tac; rewrite H || rewrite <- H; clear H.
  Check modequiv p.
  (* Instance : Proper (eq ==> eq ==> flip impl) (≃p). *)
  (* do 3 red. intros. *)
  (* red. red. subst. auto. Qed. *)
  (* Check Equiv Z. *)
  (* Check (modequiv p). *)
  (* Admitted. *)
  (* Instance : Reflexive (≃p). *)
  (* Admitted. *)
  (* Check ring_theory. *)
  (* Lemma t : ring_theory 0 1 (+) [*] (fun a b : Z => a - b) (-) (≃p). *)
  (* Admitted. *)
  (* Add Ring tt : t. *)
  (* Print Instances Ring. *)
  (* Add Ring cring_is_ring : (@cring_ring_theory Z (@modequiv Z Z (@ModEquiv_instance_0 Z (eq_Equiv Z) SrOp1_instance_0 SrOp2_instance_0 RingInv1_instance_0) p) (+) [*] 0 1 (-) _). *)
  (* Check (@cring_ring_theory Z (@modequiv Z Z (@ModEquiv_instance_0 Z (eq_Equiv Z) SrOp1_instance_0 SrOp2_instance_0 RingInv1_instance_0) p) (+) [*] 0 1 (-) q). *)
  (* Set Printing All. *)
  (* Set Printing All. *)
  Add Ring cring_ring : (@cring_ring_theory Z (≃p) _ _ _ _ _ _).
  Print Rings.
  Locate "~".
  Locate "mod".
  Goal forall a b : Z, (a + b) ≃ (b + a) md p.
    intros. ring.
  Qed.

  Goal forall a, 1 + 1 ≃ 2 md a.
    reflexivity.
  Qed.
  (* Instance : SemiRing := Zp. *)

  (* Print Instances SemiRing. *)

  (* Print Instances Ideal. *)

End Z.

(* eauto. intuition. firstorder. constructor. simpl. cbn. Set Printing All. lia. congruence. Defined. *)

(* Section __. *)
(*   Context *)
(*     `{Setoid A} *)
(*     `. *)


(* End __. *)

(* Section __. *)
(*   Context *)
(*     `{Setoid A} *)
(*     `(AbGrpOp A, RngOp A, AbGrpId A, RngId A, AbGrpOpp A). *)




(* End __. *)

Print CommutativeRing.


From stdpp Require Import list.

Section __.
  Context
    `{SemiGroup A}.

  (* Infix "∘" := opA (at level 50). *)
  Local Open Scope mag_scope.

  Global Instance fold_left_proper : Proper ((≡) ==> (≡) ==> (≡)) (fold_left (∘)).
  Proof.
    do 3 red. induction x; intros.
    - inversion H2.
      subst. assumption.
    - inversion H2; subst.
      simpl. apply IHx.
      assumption.
      rewrite H3, H6.
      reflexivity.
  Qed.

  Lemma fold_left_assoc (a b : A) ls :
    a ∘ (fold_left (∘) ls b) ≡ fold_left (∘) ls (a ∘ b).
  Proof.
    revert b; induction ls; intros b; simpl.
    - reflexivity.
    - rewrite IHls.
      rewrite (assoc (∘)).
      reflexivity.
  Qed.
End __.

(* Declare Scope monoid_scope. *)

(* Infix "∘" := monoid_op (at level 50) : monoid_scope. *)
(* Notation "'id'" := monoid_id : monoid_scope. *)
(* Notation "x ⁻" := (monoid_inv x) (at level 1) : monoid_scope. *)

From BY Require Import ListLemmas.

Section List.

  Context
    `{Setoid A}.

  Lemma map_seq_ext_equiv (f g : nat -> A) (n m k : nat)
        (Hequiv : forall i : nat, n <= i < m + k -> f i ≡ g (i + (m - n))%nat)
        (Hnm : n <= m) :
    map f (seq n k) ≡ map g (seq m k).
  Proof.
    generalize dependent m; generalize dependent n; induction k as [|k IHk]; intros; simpl.
    - reflexivity.
    - simpl; rewrite Hequiv by lia; replace (n + (m - n))%nat with m by lia.
      rewrite (IHk (S n) (S m)); [reflexivity| |lia].
      intros; rewrite Nat.sub_succ; apply Hequiv; lia. Qed.

  Global Instance rev_proper : Proper ((≡) ==> (≡)) (@rev A).
  Proof.
    do 2 red; induction x; intros; simpl.
    - inversion H1. reflexivity.
    - inversion H1. subst.
      simpl.
      rewrite (IHx k) .
      rewrite H4.
      reflexivity.
      assumption.
  Qed.

End List.

Section Monoid.
  Context
    `{Monoid}.
  Open Scope mag_scope.
  Open Scope mon_scope.

  (* Global Instance mon_id_r : RightIdentity := right_identity. *)
  (* Global Instance mon_id_l : LeftIdentity := left_identity. *)

  (* Global Instance mon_assoc : Associative := associative. *)

  Context
    (f : nat -> A).

  Definition big_op_list (l : list nat) f := fold_left (∘) (map f l) ε.
  Definition big_op f n m := big_op_list (seq n (m - n)) f.
  Definition big_op_rev f n m := big_op_list (rev (seq n (m - n))) f.

  Hint Unfold big_op big_op_rev big_op_list : bigop.

  Lemma big_op_S_r n m (nltm : n <= m) :
    big_op f n (S m) = big_op f n m ∘ f m.
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, map_app, fold_left_app, <- le_plus_minus; auto. Qed.

  Lemma big_op_S_l n m (nltm : n <= m) :
    big_op f n (S m) ≡ f n ∘ big_op f (S n) (S m).
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, fold_left_assoc. auto.
         simpl. rewrite mon_id_r, mon_id_l.
         auto. assumption. Qed.

  Lemma big_op_rev_S_r n m (nltm : n <= m) :
    big_op_rev f n (S m) = big_op_rev f (S n) (S m) ∘ f n.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l by auto; simpl; rewrite map_app, fold_left_app. reflexivity. Qed.

  Lemma big_op_rev_S_l n m (nltm : n <= m) :
    big_op_rev f n (S m) ≡ f m ∘ big_op_rev f n m.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, rev_app_distr, fold_left_assoc, <- le_plus_minus, (right_id ε (∘)) by auto; simpl;
           rewrite (left_id ε (∘)); auto. Qed.

  Lemma big_op_rev_nil n m (mltn : m <= n) :
    big_op_rev f n m = ε.
  Proof. unfold big_op_rev; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_nil n m (mltn : m <= n) :
    big_op f n m = ε.
  Proof. unfold big_op; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_split n m k (nmk : n <= m <= k) :
    (big_op f n m) ∘ (big_op f m k) ≡ big_op f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n = 0); assert (m = 0); subst; try lia. rewrite big_op_nil, (left_id ε (∘)). reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_nil (S k)), (right_id ε (∘)). reflexivity. lia.
      + rewrite big_op_S_r, (assoc (∘)), IHk, <- big_op_S_r by lia. reflexivity. Qed.

  Lemma big_op_rev_split n m k (nmk : n <= m <= k) :
    (big_op_rev f m k) ∘ (big_op_rev f n m) ≡ big_op_rev f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n = 0); assert (m = 0); try lia; subst. rewrite big_op_rev_nil, (left_id ε (∘)). reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_rev_nil (S k)), (left_id ε (∘)). reflexivity. lia.
      + rewrite big_op_rev_S_l, <- (assoc (∘)), IHk, <- big_op_rev_S_l by lia. reflexivity. Qed.

  Lemma big_op_shift g n m k :
    (forall i, f i ≡ g (i + k)) ->
    big_op f n m ≡ big_op g (n + k) (m + k).
  Proof.
    intros. unfold big_op, big_op_list. f_equiv.
    replace (m + k - (n + k)) with (m - n) by lia.
    apply map_seq_ext_equiv; intros. rewrite H3.
    replace (i + (n + k - n)) with (i + k) by lia.
    reflexivity. lia. Qed.

  Lemma big_op_rev_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op_rev f n m ≡ big_op_rev g (n + k) (m + k).
  Proof.
    intros. unfold big_op_rev, big_op_list. f_equiv.
    rewrite !map_rev. replace (m + k - (n + k)) with (m - n) by lia.

    f_equiv. apply map_seq_ext_equiv. intros.
    rewrite H3.
    replace (i + (n + k - n)) with (i + k) by lia.
    reflexivity. lia.
  Qed.
End Monoid.

(* Section Group. *)
(*   Context *)
(*     `{Group A}. *)

(*   Open Scope mag_scope. *)
(*   Open Scope mon_scope. *)
(*   Open Scope grp_scope. *)

(*   (* Global Instance grp_inv_r : RightInverse := right_inverse. *) *)
(*   (* Global Instance grp_inv_l : LeftInverse := left_inverse. *) *)

(*   (* Global Instance grp_id_r : RightIdentity := right_identity. *) *)
(*   (* Global Instance grp_id_l : LeftIdentity := left_identity. *) *)

(*   (* Global Instance grp_assoc : Associative := associative. *) *)


(* End Group. *)

(* Section AbelianGroup. *)

(*   Context *)
(*     `{abelian_group}. *)

(*   Open Scope group_scope. *)

(*   Definition opp_unique_r : forall x y, x + y = 0 -> y = -x := inv_unique_r. *)
(*   Definition opp_unique_l : forall x y, y + x = 0 -> y = -x := inv_unique_l. *)

(*   Definition opp_invol : forall x, - (- x) = x := inv_invol. *)

(*   Definition opp_0 : forall x, - x = 0 -> x = 0 := inv_id. *)
(*   Definition opp0 : - 0 = 0 := id_inv. *)

(*   Definition opp_inj : forall x y, - x = - y -> x = y := inv_inj. *)

(*   Global Instance add_0_r : @RightIdentity _ _ abelian_group_op 0 := right_identity. *)
(*   Global Instance add_0_l : @LeftIdentity _ _ abelian_group_op 0 := left_identity. *)

(*   Global Instance add_assoc : @Associative _ abelian_group_op := associative. *)
(*   Global Instance add_comm : @Commutative  _ abelian_group_op := commutative. *)

(*   Global Instance add_opp_r : @RightInverse _ abelian_group_op 0 abelian_group_opp := right_inverse. *)
(*   Global Instance add_opp_l : @LeftInverse _ abelian_group_op 0 abelian_group_opp := left_inverse. *)



(* End AbelianGroup. *)

Section Ring.

End Ring.

(* Section CommutativeRing. *)
(*   Context *)
(*     `{CommutativeRing}. *)

(*   (* Global Instance mul_comm : @Commutative _ ring_op := commutative. *) *)

(*   Open Scope _scope. *)
(*   Open Scope ring_scope. *)

(*   Lemma ring_ring_theory : @ring_theory A 0 1 abelian_group_op ring_op  (fun x y => x + (- y)) abelian_group_opp eq. *)
(*   Proof. *)
(*     split; intros. *)
(*     - apply add_0_l. *)
(*     - apply add_comm. *)
(*     - apply add_assoc. *)
(*     - apply mul_1_l. *)
(*     - apply mul_comm. *)
(*     - apply mul_assoc. *)
(*     - apply mul_add_distr_r. *)
(*     - reflexivity. *)
(*     - apply add_opp_r. *)
(*   Qed. *)

(*   Add Ring commutative_ring_is_ring : ring_ring_theory. *)

(*   Example ex1 : forall x y, x + y = y + x. *)
(*   Proof. intros. ring. Qed. *)

(*   Example ex2 : forall x, 0 + x = x. *)
(*   Proof. intros. ring. Qed. *)

(*   Example ex3 : forall x, 1 * x = x. *)
(*   Proof. intros. ring. Qed. *)
(* End CommutativeRing. *)

Section __.
  Context
    {A : Type}.

  Class decidable P :=
    dec : {P} + {~ P}.
End __.
Notation decidable_rel r := (forall x y, decidable (r x y)).

Section IntegralDomain.
  Context
    `{IntegralDomain}.

  Add Ring integral_domain_ring : cring_ring_theory.


  Open Scope sr_scope.
  Open Scope ring_scope.
  Open Scope abgrp_scope.

  (* Global Instance integral_domain_zero_rule2 : ZeroRule2 (≡) 0 [*]. *)
  (* Proof. *)
  (*   intros ? ? contra. apply (zero_rule1 9 [*]) in contra. destruct contra; contradiction. *)
  (* Qed. *)

  Lemma mul_r_inj : forall x y z : A, y ≢ 0 -> x * y ≡ z * y -> x ≡ z.
  Proof.
    intros.
    assert ((x - z) * y ≡ 0).
    rewrite (right_distr [*] (+)), H7.
    ring.
    apply (zero_rule1 0 [*]) in H8.
    destruct H8.
    - apply ring_opp_unique_l in H8. rewrite H8. ring.
    - contradiction.
  Qed.

  Lemma mul_l_inj : forall x y z : A, x ≢ 0 -> x * y ≡ x * z -> y ≡ z.
  Proof.
    intros.
    eapply mul_r_inj.
    exact H6.
    rewrite (comm [*]), H7.
    ring.
  Qed.

End IntegralDomain.

Class LeftAct A B := left_act :> B -> A -> A.
Class RightAct A B := right_act :> A -> B -> A.

Typeclasses Transparent LeftAct RightAct.

Declare Scope lmodule_scope.
Declare Scope rmodule_scope.

Delimit Scope sr_scope with SR.
Delimit Scope ring_scope with R.
Delimit Scope abgrp_scope with AG.

Notation "a ⋅ b" := (left_act a b) (at level 30) : lmodule_scope.
Notation "a ⋅ b" := (right_act a b) (at level 30) : rmodule_scope.
(* Infix "⋅" := left_act (at level 30) : lmodule_scope. *)
(* Infix "⋅" := right_act : rmodule_scope. *)
Notation "(⋅)" := left_act (only parsing) :lmodule_scope.

Global Arguments left_act {!_ !_ _} _ _ : assert.
Global Arguments right_act {!_ !_ _} _ _ : assert.

Notation "(⋅)" := right_act (only parsing) :rmodule_scope.

Section __.
  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope abgrp_scope.
  Local Open Scope lmodule_scope.
  Class LeftModule A B `{Equiv A, AbGrpOp A, AbGrpId A, AbGrpOpp A, Equiv B, AbGrpOp B, SrOp2 B, AbGrpId B, RingId2 B, AbGrpOpp B, LeftAct A B} :=
    {
      lmod_abgroup :> AbelianGroup A;
      lmod_cring :> Ring B;
      lmod_proper :> Proper ((≡) ==> (≡) ==> (≡)) (⋅);
      lmod_distr_l :> LeftActDistr (≡) (⋅) (+);
      lmod_exch_l :> LeftActExch (≡) (⋅) (+) (+);
      lmod_act_assoc :> LeftActAssoc (≡) (⋅) [*];
      lmod_left_id :> LeftActId (≡) 1 (⋅)
    }.
End __.

Section __.
  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope lmodule_scope.
  Local Open Scope abgrp_scope.
  Class LeftAlgebra A B `{Equiv A, AbGrpOp A, SrOp2 A, AbGrpId A, RingId2 A, AbGrpOpp A, Equiv B, AbGrpOp B, SrOp2 B, AbGrpId B, RingId2 B, AbGrpOpp B, LeftAct A B} :=
    {
      lalg_ring :> Ring A;
      lalg_cring :> Ring B;
      lalg_proper :> Proper ((≡) ==> (≡) ==> (≡)) (⋅);
      lalg_distr_l :> LeftActDistr (≡) (⋅) (+);
      lalg_exch_l :> LeftActExch (≡) (⋅) (+) (+);
      lalg_act_assoc :> LeftActAssoc (≡) (⋅) [*];
      lalg_left_id :> LeftActId (≡) 1 (⋅)
    }.
End __.

Section ModuleTheory.
  Context
    `{LeftModule A B}.

  Open Scope sr_scope.
  Open Scope ring_scope.
  Open Scope abgrp_scope.
  Open Scope lmodule_scope.
  Close Scope nat.

  Definition act_1_l : forall v, 1 ⋅ v ≡ v := left_act_id 1 (⋅).

  Lemma act_0_r : forall x : B, x ⋅ 0 ≡ 0.
  Proof.
    intros.
    setoid_replace (x ⋅ 0) with (x ⋅ 0 + 0)
      by (symmetry; apply (right_id 0 (+))).
    (* symmetry. apply (right_id 0 (+)). *)
      (* by (apply (right_inv 0 (+))). add_0_r). *)
    setoid_replace (0 : A) with (x ⋅ 0 - x ⋅ 0) at 3 4
      by (symmetry; apply (right_inv 0 (-) (+))).
    rewrite (assoc (+)).
    rewrite <- (left_act_distr (⋅) (+)).
    rewrite (left_id 0 (+)).
    reflexivity.
  Qed.

  Lemma act_0_l : forall x : A, 0 ⋅ x ≡ 0.
    intros.
    setoid_replace (0 ⋅ x) with (0 ⋅ x + 0)
      by (symmetry; apply (right_id 0 (+))).
    setoid_replace (0 : A) with (0 ⋅ x - 0 ⋅ x)
      by (symmetry; apply (right_inv 0 (-) (+))).
    rewrite (assoc (+)).
    rewrite <- (left_act_exch (⋅) (+) (+)).
    rewrite (left_id 0 (+)).
    reflexivity.
  Qed.

  Lemma opp_act : forall (x : B) (y : A), - x ⋅ y ≡ (- x) ⋅ y.
    intros. symmetry.
    apply grp_inv_unique_r.
    rewrite <- (left_act_exch (⋅) (+) (+)).
    setoid_rewrite (right_inv 0 (-) (+)).
    apply act_0_l.
  Qed.
End ModuleTheory.
