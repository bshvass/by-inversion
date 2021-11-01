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

Require Export Coq.Classes.RelationClasses.
Require Export Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import AAC_tactics.AAC.

From BY Require Import ListLemmas.

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

Class Equiv A := equiv :> relation A.
Class Rel A := rel :> relation A.
Class Sub A := sub :> A -> Prop.

Definition InSub {A} (P : Sub A) x := P x.

Infix "=" := equiv : type_scope.
Notation "(=)" := equiv (only parsing).
Infix "≡" := eq (at level 70) : type_scope.
Infix "≢" := (not eq) (at level 70) : type_scope.
Infix "<>" := (complement equiv) : type_scope.
Infix "∼" := rel (at level 70) : type_scope.
Notation "(∼)" := rel (only parsing).
Infix "≁" := (complement rel) (at level 70) : type_scope.
Notation "x ∈ P" := (InSub P x) (at level 70).

Class Setoid A `{Equiv A} := setoid :> Equivalence (=).
Class Suboid A `{Setoid A} (P : Sub A) := sub_proper :> Proper ((=) ==> iff) (InSub P).

Class SetoidMorph {A} {B} (f : A -> B) `{Equiv A, Equiv B} :=
  {
    setmor_dom : Setoid A;
    setmor_cod : Setoid B;
    setmor_proper :> Proper ((=) ==> (=)) f
  }.

(* Class BinOp A B C := bin_op : A -> B -> C. *)
(* Class BinId A := bin_id : A. *)
(* Class BinInv A B := bin_inv : A -> B. *)

(* Typeclasses Transparent BinOp BinId BinInv *)
Typeclasses Transparent Equiv Rel.

(* Declare Scope bin_scope. *)

(* Infix "∘" := bin_op (at level 60) : bin_scope. *)
(* Notation "(∘)" := bin_op (only parsing) : bin_scope. *)
(* Notation "'ε'" := bin_id : bin_scope. *)
(* Notation "x ⁻" := (bin_inv x) (at level 1) : bin_scope. *)
(* Notation "(⁻)" := bin_inv (only parsing) : bin_scope. *)

Section BinOp.

  Class Congruence `(Rel A) (op : A -> A -> A) :=
    {
      cong_equiv :> Equivalence (∼);
      cong_proper :> Proper ((∼) ==> (∼) ==> (∼)) op
    }.

  Class Associative {A} {B} {C} {D} {E} {F} `{Equiv F}
        (bcd : B -> C -> D)
        (adf : A -> D -> F)
        (abe : A -> B -> E)
        (ecf : E -> C -> F) :=
    associative : forall x y z, adf x (bcd y z) = ecf (abe x y) z.
  Class Commutative {A} {B} {C} `{Equiv C}
        (abc : A -> B -> C)
        (bac : B -> A -> C) :=
    commutative : forall x y, abc x y = bac y x.
  Class LeftIdentity {A} {B} `{Equiv A}
        (baa : B -> A -> A)
        (b : B) :=
    left_identity : forall x, baa b x = x.
  Class RightIdentity {A} {B} `{Equiv A}
        (aba : A -> B -> A)
        (b : B) :=
    right_identity : forall x, aba x b  = x.
  Class LeftInverse {A} {B} `{Equiv C}
        (abc : A -> B -> C)
        (ba : B -> A)
        (c : C) :=
    left_inverse : forall x, abc (ba x) x = c.
  Class RightInverse {A} {B} `{Equiv C}
        (abc : A -> B -> C)
        (ab : A -> B)
        (c : C) :=
    right_inverse : forall x, abc x (ab x) = c.
  Class LeftDistributive {A} {B} {C} {D} {E} {F} {G} `{Equiv G}
        (adg : A -> D -> G)
        (bcd : B -> C -> D)
        (abe : A -> B -> E)
        (acf : A -> C -> F)
        (efg : E -> F -> G) :=
    left_distributive : forall x y z, adg x (bcd y z) = efg (abe x y) (acf x z).
  Class RightDistributive {A} {B} {C} {D} {E} {F} {G} `{Equiv G}
        (abd : A -> B -> D)
        (dcg : D -> C -> G)
        (ace : A -> C -> E)
        (bcf : B -> C -> F)
        (efg : E -> F -> G) :=
    right_distributive : forall x y z, dcg (abd x y) z = efg (ace x z) (bcf y z).
  Class ZeroRule {A} {B} {C} `{Equiv A, Equiv B, Equiv C}
        (abc : A -> B -> C)
        (a : A)
        (b : B)
        (c : C) :=
    zero_rule : forall x y, x <> a -> y <> b -> abc x y <> c.
  Class Closed {A} (P : A -> Prop) (op : A -> A -> A) :=
    closed : forall x y, P x -> P y -> P (op x y).

End BinOp.

Section AAC.
  Context
    `{e : Equiv A}
    `{@Associative A A A A A A e f f f f}
    `{@Commutative A A A e f f}
    `{@RightIdentity A A e f a}
    `{@LeftIdentity A A e f a}.

  Global Instance : AAC.Associative (=) f := associative.
  Global Instance : AAC.Commutative (=) f := commutative.
  Global Instance : AAC.Unit (=) f a := {| law_neutral_left := left_identity;
                                           law_neutral_right := right_identity |}.
End AAC.

Class MagOp A := mag_op : A -> A -> A.
Class MonId A := mon_id : A.
Class GrpInv A := grp_inv : A -> A.
Class SrOp1 A := sr_op1 :> MagOp A.
Class SrOp2 A := sr_op2 :> MagOp A.
Class RingInv1 A := ring_inv1 :> GrpInv A.
Class RingInv2 A := ring_inv2 :> GrpInv A.
Class RingId1 A := ring_id1 :> MonId A.
Class RingId2 A := ring_id2 :> MonId A.

Typeclasses Transparent MagOp MonId GrpInv SrOp1 SrOp2 RingId1 RingId2 RingInv1 RingInv2.

Declare Scope mag_scope.
Declare Scope mon_scope.
Declare Scope grp_scope.
Declare Scope abgrp_scope.
Declare Scope sr_scope.
Declare Scope ring_scope.
Delimit Scope sr_scope with sr.
Delimit Scope ring_scope with ring.

Infix "∘" := mag_op (left associativity, at level 50)  : mag_scope.
(* Notation "( x ∘)" := (mag_op x) (only parsing, at level 70) : mag_scope. *)
(* Notation "(∘ x )" := (fun y => mag_op _ x) (only parsing, at level 70) : mag_scope. *)
Notation "(∘)" := mag_op (only parsing) : mag_scope.

Notation "'ε'" := mon_id : mon_scope.

Notation "x ⁻¹" := (grp_inv x) (at level 1) : grp_scope.
Notation "(⁻¹)" := grp_inv (only parsing) : grp_scope.
(* Notation "x / y" := (mag_op x (grp_inv y)) : grp_scope. *)

Infix "+" := mag_op (left associativity, at level 50) : abgrp_scope.
Notation "(+)" := mag_op (only parsing) : abgrp_scope.
(* Notation "( x +)" := (mag_op x) (only parsing, at level 70) : abgrp_scope. *)
(* Notation "(+ x )" := (fun y => mag_op _ x) (only parsing, at level 70) : abgrp_scope. *)
Notation "0" := mon_id : abgrp_scope.
Notation "- x" := (grp_inv x) : abgrp_scope.
Notation "(-)" := grp_inv (only parsing) : abgrp_scope.
Notation "x - y" := (mag_op x (grp_inv y)) : abgrp_scope.

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

Section Magma.

  Local Open Scope mag_scope.
  Class Magma A `{Equiv A, MagOp A} :=
    {
      mag_setoid :> Setoid A;
      mag_proper :> Proper ((=) ==> (=) ==> (=)) (∘)
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
      sg_proper :> Proper ((=) ==> (=) ==> (=)) (∘);
      sg_assoc :> Associative (∘) (∘) (∘) (∘)
    }.

End SemiGroup.

Section Monoid.
  Local Open Scope mag_scope.
  Local Open Scope mon_scope.

  Class Monoid A `{Equiv A, MagOp A, MonId A} :=
    {
      mon_setoid :> Setoid A;
      mon_proper :> Proper ((=) ==> (=) ==> (=)) (∘);
      mon_assoc :> Associative (∘) (∘) (∘) (∘);
      mon_id_l :> LeftIdentity (∘) ε;
      mon_id_r :> RightIdentity (∘) ε
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
      cmon_proper :> Proper ((=) ==> (=) ==> (=)) (∘);
      cmon_assoc :> Associative (∘) (∘) (∘) (∘);
      cmon_lid :> LeftIdentity (∘) ε;
      cmon_rid :> RightIdentity (∘) ε;
      cmon_comm :> Commutative (∘) (∘)
    }.


End CommutativeMonoid.

Section Group.
  Local Open Scope mag_scope.
  Local Open Scope mon_scope.
  Local Open Scope grp_scope.

  Class Group A `{Equiv A, MagOp A, MonId A, GrpInv A} :=
    {
      grp_setoid :> Setoid A;
      grp_op_proper :> Proper ((=) ==> (=) ==> (=)) (∘);
      grp_assoc :> Associative (∘) (∘) (∘) (∘);
      grp_id_l :> LeftIdentity (∘) ε;
      grp_id_r :> RightIdentity (∘) ε;
      grp_inv_proper :> Proper ((=) ==> (=)) (⁻¹);
      grp_inv_l :> LeftInverse (∘) (⁻¹) ε;
      grp_inv_r :> RightInverse (∘) (⁻¹) ε
    }.

End Group.

Section AbelianGroup.

  Local Open Scope abgrp_scope.

  Class AbelianGroup A `{Equiv A, MagOp A, MonId A, GrpInv A} :=
    {
      abgrp_setoid :> Setoid A;
      abgrp_proper :> Proper ((=) ==> (=) ==> (=)) (+);
      abgrp_assoc :> Associative (+) (+) (+) (+);
      abgrp_id_l :> LeftIdentity (+) 0;
      abgrp_id_r :> RightIdentity (+) 0;
      abgrp_comm :> Commutative (+) (+);
      abgrp_inv_proper :> Proper ((=) ==> (=)) (-);
      abgrp_inv_l :> LeftInverse (+) (-) 0;
      abgrp_inv_r :> RightInverse (+) (-) 0;
    }.

End AbelianGroup.

Section SemiRing.

  Local Open Scope sr_scope.

  Class SemiRing A `{Equiv A, SrOp1 A, SrOp2 A} :=
    {
      sr_mag1 :> @Magma _ _ (+);
      sr_mag2 :> @Magma _ _ [*];
      sr_distr_l :> LeftDistributive [*] (+) [*] [*] (+);
      sr_distr_r :> RightDistributive (+) [*] [*] [*] (+)
    }.

End SemiRing.

Section Ring.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Class Ring A `{Equiv A, SrOp1 A, SrOp2 A, RingId1 A, RingId2 A, RingInv1 A} :=
    {
      ring_abgrp :> @AbelianGroup _ _ (+) 0 (-);
      ring_monoid :> @Monoid _ _ [*] 1;
      ring_distr_l :> LeftDistributive [*] (+) [*] [*] (+);
      ring_distr_r :> RightDistributive (+) [*] [*] [*] (+)
    }.
End Ring.

Section CommutativeRing.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Class CommutativeRing A `{Equiv A, SrOp1 A, SrOp2 A, RingId1 A, RingId2 A, RingInv1 A} :=
    {
      cring_abgrp :> @AbelianGroup _ _ (+) 0 (-);
      cring_monoid :> @CommutativeMonoid _ _ [*] 1;
      cring_ldistr :> LeftDistributive [*] (+) [*] [*] (+);
      cring_rdistr :> RightDistributive (+) [*] [*] [*] (+);
    }.

End CommutativeRing.

Section IntegralDomain.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Class IntegralDomain A `{Equiv A, SrOp1 A, SrOp2 A, RingId1 A, RingId2 A, RingInv1 A} :=
    {
      dom_abgrp :> @AbelianGroup _ _ (+) 0 (-);
      dom_monoid :> @CommutativeMonoid _ _ [*] 1;
      dom_distr_l :> LeftDistributive [*] (+) [*] [*] (+);
      dom_distr_r :> RightDistributive (+) [*] [*] [*] (+);
      dom_non_trivial : 0 <> 1;
      dom_zero_rule :> ZeroRule [*] 0 0 0
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

(* Global Arguments bin_id /. *)
(* Global Arguments mon_id /. *)
(* Global Arguments bin_op /. *)
(* Global Arguments mag_op /. *)
(* Global Arguments equiv /. *)
(* Global Arguments rel /. *)
(* Global Arguments complement /. *)

Section Magma.

  Local Open Scope mag_scope.
  Context `{Magma A}
          `{Congruence A (∘)}.

  Instance : @Magma A (∼) (∘).
  repeat split; try apply _. Qed.

End Magma.

Ltac substructure := repeat split; try apply _.

Section SemiGroup.

  Local Open Scope mag_scope.
  Context `{SemiGroup A}.

  Instance sg_mag : Magma A. substructure. Qed.

  Context `{Congruence A (∘)}
          `{subrelation A (=) (∼)}.

  Instance quot_sg : @SemiGroup A (∼) (∘).
  repeat split; try apply _.
  cbv; intros; apply is_subrelation; apply associative. Qed.

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

  Context `{Monoid A}
          `{Congruence A (∘)}
          `(subrelation A (=) (∼)).

  Instance mon_sg : SemiGroup A. substructure. Qed.

  Instance quot_mon : @Monoid A (∼) (∘) ε.
  repeat split; try apply _;
  cbv; intros; apply is_subrelation; apply associative || apply right_identity || apply left_identity. Qed.

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

Require Import Coq.Classes.SetoidTactics.

Section Group.
  Local Open Scope mag_scope.
  Local Open Scope mon_scope.
  Local Open Scope grp_scope.
  Context `{Group A}.

  Hint Rewrite associative using apply _: group_simplify.
  Hint Rewrite left_identity right_identity left_inverse right_inverse using apply _: group_cancellation.

  Ltac group_simplify :=
    rewrite_strat
      (try bottomup (hints group_simplify));
    (try bottomup (choice (hints group_cancellation) <- associative)).
  Ltac group_simplify_in H :=
    rewrite_strat
      (try bottomup (hints group_simplify));
    (try bottomup (choice (hints group_cancellation) <- associative)) in H.
  Ltac group := group_simplify; easy.

  Instance quot_grp `(Rel A) `{!Congruence (∼) (∘)} `{!subrelation (=) (∼)} `{!Proper ((∼) ==> (∼)) (⁻¹)} : @Group A (∼) _ _ _.
  Proof.
    repeat split; try apply _;
      red; intros; apply is_subrelation.
    - apply associative.
    - apply left_identity.
    - apply right_identity.
    - apply left_inverse.
    - apply right_inverse.
  Qed.
  Check quot_grp.

  Lemma grp_op_inj_l : forall x y z, x ∘ y = x ∘ z -> y = z.
  Proof.
    intros.
    setoid_replace y with (x⁻¹ ∘ (x ∘ y)) by group.
    rewrite H4.
    group.
  Qed.

  Lemma grp_op_inj_r : forall x y z, y ∘ x = z ∘ x -> y = z.
  Proof.
    intros.
    setoid_replace y with (y ∘ x ∘ x⁻¹) by group.
    rewrite H4.
    group.
  Qed.

  Lemma grp_inv_unique_r : forall x y : A, x ∘ y = ε -> y = x⁻¹.
  Proof.
    intros.
    apply (grp_op_inj_l x).
    group.
  Qed.

  Lemma grp_inv_unique_l : forall x y : A, y ∘ x = ε -> y = x⁻¹.
  Proof.
    intros.
    apply (grp_op_inj_r x).
    group.
  Qed.

  Lemma grp_op_inv : forall x y, (x ∘ y)⁻¹ = y⁻¹ ∘ x⁻¹.
    intros.
    symmetry.
    apply grp_inv_unique_r.
    group.
  Qed.

  Lemma grp_inv_inv : forall x, (x ⁻¹) ⁻¹ = x.
  Proof.
    intros.
    symmetry.
    apply grp_inv_unique_r.
    group.
  Qed.

  Hint Rewrite grp_op_inv grp_inv_inv using apply _: group_cancellation.

  Class Subgroup (P : Sub A) :=
    {
      subgrp_suboid :> Suboid A P;
      subgrp_id : ε ∈ P;
      subgrp_inv : forall x, x ∈ P -> x⁻¹ ∈ P;
      subgrp_closed : forall x y, x ∈ P -> y ∈ P -> x ∘ y ∈ P
    }.

  Lemma subgrp_inv_if `{!Subgroup P} : forall x, x ⁻¹ ∈ P -> x ∈ P.
  Proof.
    intros.
    rewrite <- grp_inv_inv.
    apply subgrp_inv.
    assumption.
  Qed.

  Class NormalSubgroup (P : Sub A) :=
    {
      nsubgrp_subgrp :> Subgroup P;
      nsubgrp_normal : forall x y, x ∈ P -> y ∘ x ∘ y⁻¹ ∈ P
    }.

  Lemma nsubgrp_normal_if `{!NormalSubgroup P} : forall x y, y ∘ x ∘ y⁻¹ ∈ P -> x ∈ P.
  Proof.
    intros.
    apply nsubgrp_normal with (y0:=y⁻¹) in H4.
    group_simplify_in H4.
    assumption.
  Qed.

  Instance nsubgrp_rel `{!NormalSubgroup P} : Rel A := (fun x y : A => x ∘ y ⁻¹ ∈ P).

  Instance nsubgrp_rel_cong `{!NormalSubgroup P} : Congruence (∼) (∘).
  Proof.
  split; [repeat split; red; intros|];unfold rel, nsubgrp_rel in *.
  - rewrite right_inverse.
    apply subgrp_id.
  - setoid_replace (y ∘ x ⁻¹) with ((x ∘ y ⁻¹) ⁻¹) by group.
    apply subgrp_inv.
    assumption.
  - setoid_replace (x ∘ z ⁻¹) with ((x ∘ y ⁻¹) ∘ (y ∘ z ⁻¹)) by group.
    apply subgrp_closed; assumption.
  - do 3 red; intros.
    setoid_replace (x ∘ x0 ∘ (y ∘ y0) ⁻¹) with (y ∘ ((y ⁻¹ ∘ x) ∘ (x0 ∘ y0 ⁻¹)) ∘ y ⁻¹) by group.
    apply nsubgrp_normal.
    apply subgrp_closed.
    apply nsubgrp_normal_if with (y1:=y).
    group_simplify.
    assumption.
    assumption.
  Qed.
End Group.

Section AbelianGroup.

  Context `{G : AbelianGroup A}.
  Local Open Scope abgrp_scope.

  Instance abgrp_grp : Group A. substructure. Qed.
  (* Existing Instance abgrp_grp. *)

  Hint Rewrite associative using apply _: group_simplify.
  Hint Rewrite left_identity right_identity left_inverse right_inverse using apply _: group_cancellation.
  Hint Rewrite grp_op_inv grp_inv_inv using apply _: group_cancellation.

  Ltac group_simplify :=
    rewrite_strat
      (try bottomup (hints group_simplify));
    (try bottomup (choice (hints group_cancellation) <- associative)).
  Ltac group_simplify_in H :=
    rewrite_strat
      (try bottomup (hints group_simplify));
    (try bottomup (choice (hints group_cancellation) <- associative)) in H.
  Ltac group := group_simplify; easy.
  Ltac abgrp_normalize := aac_rewrite left_inverse; aac_normalise.

  Hint Rewrite left_identity right_identity left_inverse right_inverse using apply _: abgrp_rewrite.

  Ltac abgrp_simplify :=
      repeat match goal with
      | [ |- context [ ?a + ?b ] ] => progress let H := fresh in eassert (H : a + b = _) by (abgrp_normalize; reflexivity); setoid_rewrite H; clear H
      | [ |- context [ ?a - ?b ] ] => progress let H := fresh in eassert (H : a - b = _) by (abgrp_normalize; reflexivity); setoid_rewrite H; clear H
      | [ |- context [ - ?a ] ] => progress let H := fresh in eassert (H : - a = _) by (abgrp_normalize; reflexivity); setoid_rewrite H; clear H
      end.

  Ltac abgrp := abgrp_simplify; easy.

  Instance subgrp_ab_normal `{!Subgroup P} : NormalSubgroup P.
    intros; split; intros.
    - assumption.
    - abgrp.
  Qed.

End AbelianGroup.

Require Import Coq.setoid_ring.Ring.

Section SemiRing.

  Context `{SemiRing A}.

  Local Open Scope sr_scope.

  Instance quot_ring `(Rel A) `{!Congruence (∼) (+)} `{!Congruence (∼) [*]} `{subrelation A (=) (∼)} : @SemiRing A (∼) _ _.
  Proof.
    repeat split; try apply _;
      red; intros; apply is_subrelation.
    - apply left_distributive.
    - apply right_distributive.
  Qed.

End SemiRing.

Section CommutativeRing.

  Context `{CommutativeRing A}.
  Local Open Scope sr_scope.
  Local Open Scope ring_scope.

  Lemma ring_ring_theory : @ring_theory A 0 1 (+) [*] (fun x y : A => x - y) (-) (=).
  Proof.
    split; intros.
    - apply left_identity.
    - apply commutative.
    - apply associative.
    - apply left_identity.
    - apply commutative.
    - apply associative.
    - apply right_distributive.
    - reflexivity.
    - apply right_inverse.
  Qed.

  Instance cring_sr : SemiRing A. substructure. Qed.

  Add Ring commutative_ring_is_ring : ring_ring_theory.
  Check ring_ring_theory.

  Existing Instance abgrp_grp.

  Class Ideal (P : Sub A) :=
    {
      ideal_subgroup :> Subgroup P;
      ideal_closed : forall x y, x ∈ P -> y * x ∈ P
    }.


  (* Instance ideal_nsubgrp `{Ideal} : NormalSubgroup P. *)


  (* Instance ideal_rel `{Ideal} : Rel A := (fun x y : A => x - y ∈ P). *)

  Tactic Notation "replace" constr(T1) "with" constr(T2) "by" tactic3(tac) :=
    let H := fresh in
    assert (H : T1 = T2) by tac; rewrite H || rewrite <- H; clear H.

  Existing Instance subgrp_ab_normal.
  Existing Instance nsubgrp_rel.
  Instance ideal_rel_op1_cong `(!Ideal P) : Congruence (∼) (+) := nsubgrp_rel_cong.
  Instance ideal_rel_op2_cong `(!Ideal P) : Congruence (∼) [*].
  split.
  - apply _.
  - do 3 red; intros.
    cbv -[sr_op1 sr_op2 ring_inv1 InSub].
    replace (x * x0 - y * y0) with ((x0 * (x - y)) + (y * (x0 - y0))) by ring.
    apply subgrp_closed.
    apply ideal_closed. assumption.
    apply ideal_closed. assumption.
  Qed.

  Definition div a : Sub A := fun b => exists k, k * b = a.
  Definition mul a : Sub A := fun b => div b a.

  Notation "'Σ_(' i ',' n ')^(' m ')' f" := (@big_op _ (+) 0 (fun i => f) n m)%sr (at level 50) : sr_scope.
  Notation "Π_ ( i , n )^ m f" := (@big_op _ [*] 1 (fun i => f) n m)%sr (at level 50) : sr_scope.

  (* Check forall a c m, Σ_(i , 0 )^(m) c i. *)

  Definition is_linear_comb a (x : nat -> A) (m : nat) (c : nat -> A) :=
    exists c m, a = Σ_( i , 0 )^( m ) (c i * x i).

  Notation "⟨ a ⟩" := (mul a).

  Infix "|" := div (at level 40).

  Definition principal_ideal (a : A) : Ideal ⟨a⟩.
  repeat split; intros; unfold InSub, mul, div, mon_id, grp_inv, mag_op in *.
  - setoid_rewrite <- H6; assumption.
  - setoid_rewrite H6. assumption.
  - exists 0. ring.
  - destruct H6 as [k]. exists (- k).
    rewrite <- H6. ring.
  - destruct H6 as [kx].
    destruct H7 as [ky].
    exists (kx + ky).
    rewrite <- H6, <- H7.
    ring.
  - destruct H6.
    exists (y * x0). rewrite <- H6.
    ring.
  Qed.

End CommutativeRing.
Notation "⟨ a ⟩" := (mul a).

Section IntegralDomain.

  Context `{IntegralDomain A}.

  Global Instance domain_semiring : SemiRing A. substructure. Qed.
  Global Instance domain_cring : CommutativeRing A. substructure. Qed.

End IntegralDomain.


Section __.
  Context (A : Type).
  Global Instance eq_Equiv : (Equiv A) := eq.
  Hint Unfold equiv eq_Equiv : equiv_unfold.

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

  Instance : SrOp1 Z := Z.add.
  Instance : SrOp2 Z := Z.mul.
  Instance : RingId1 Z := Z0.
  Instance : RingId2 Z := 1%Z.
  Instance : RingInv1 Z := Z.opp.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.

  Instance : RightIdentity (+) 0 := Z.add_0_r.
  Instance : LeftIdentity (+) 0 := Z.add_0_l.
  Instance : RightIdentity [*] 1 := Z.mul_1_r.
  Instance : LeftIdentity [*] 1 := Z.mul_1_l.
  Instance : Associative (+) (+) (+) (+) := Z.add_assoc.
  Instance : Commutative (+) (+) := Z.add_comm.
  Instance : Associative [*] [*] [*] [*] := Z.mul_assoc.
  Instance : Commutative [*] [*] := Z.mul_comm.
  Instance : LeftInverse (+) (-) 0 := Z.add_opp_diag_l.
  Instance : RightInverse (+) (-) 0 := Z.add_opp_diag_r.
  Instance : LeftDistributive [*] (+) [*] [*] (+) := Z.mul_add_distr_l.
  Instance : RightDistributive (+) [*] [*] [*] (+) := Z.mul_add_distr_r.
  Instance : ZeroRule Z.mul 0%Z 0%Z 0%Z. repeat red; intros. cbv -[Z.mul] in *; lia. Qed.

(* Check quot. *)
(* Check SemiGroup.A. *)
(* Import SemiGroup. *)

(* Check quot. *)

(* Print quot. *)

(* Print Instances SemiGroup. *)

  Instance : IntegralDomain Z. repeat (split; try apply _). cbv; lia. Qed.

  Context (p : Z) (pprime : prime p).
  (* Existing Instance domain_cring. *)
  (* Print Instances SrOp1. *)
  (* Print Instances IntegralDomain. *)
  Instance : Ideal ⟨p⟩ := principal_ideal p.
  Existing Instance nsubgrp_rel.
  Existing Instance subgrp_ab_normal.
  Print Instances Rel.
  (* Instance : NormalSubgroup ⟨p⟩ := subgrp_ab_normal (principal_ideal p). *)
  (* Instance : Rel Z := nsubgrp_rel. *)
  Set Typeclasses Debug.
  Check quot_ring.
  Instance : @SemiRing Z (∼) _ _. (* := quot_ring Z (∼) _ _. *)
  Print Instances SemiRing.
  exact (@quot_ring Z (∼) _ _ (SemiRing_instance_0)).
  := quot_ring Z. (∼) _ _ _ _ _ _.

  Existing Instance principal_ideal.
  Existing Instance nsubgrp_rel.
  Existing Instance nsubgrp_rel_cong.

  Existing Instance quot_ring.

  Instance : SemiRing := Zp.

  Print Instances SemiRing.

  Print Instances Ideal.





eauto. intuition. firstorder. constructor. simpl. cbn. Set Printing All. lia. congruence. Defined.

Section __.
  Context
    `{Setoid A}
    `.


End __.

Section __.
  Context
    `{Setoid A}
    `(AbGrpOp A, RngOp A, AbGrpId A, RngId A, AbGrpOpp A).




End __.

Print CommutativeRing.

Class Module_left_act M R := module_left_act : R -> M -> M.
Class Module_right_act M R := module_right_act : M -> R -> M.

Typeclasses Transparent Module_left_act Module_right_act.

Declare Scope lmodule_scope.
Declare Scope rmodule_scope.

Infix "⋅" := module_left_act (at level 30) : lmodule_scope.
Infix "⋅" := module_right_act : rmodule_scope.

Section __.
  Context
    {M R}
    `{abelian_group M}
    `{ring R}
    `{Module_left_act M R}
    `{Module_right_act M R}.

  Class left_module :=
    {
      left_module_abelian_group :> @abelian_group M _ _ _;
      left_module_ring :> @ring R _ _ _ _ _;
      left_module_left_distributive :> @LeftDistributive M R M abelian_group_op abelian_group_op module_left_act;
      left_module_right_distributive :> @RightDistributive R M M abelian_group_op abelian_group_op module_left_act;
      left_module_left_act :> @LeftAction M R ring_op module_left_act;
      left_module_left_identity :> @LeftIdentity M R module_left_act ring_id
    }.
End __.

Section __.
  Context
    `{Associative}.

  Infix "∘" := opA (at level 50).

  Lemma fold_left_assoc (a b : A) ls :
    a ∘ (fold_left opA ls b) = fold_left opA ls (a ∘ b).
  Proof.
    revert b; induction ls; intros b; simpl.
    - reflexivity.
    - rewrite IHls, associative; reflexivity.
  Qed.
End __.

Declare Scope monoid_scope.

Infix "∘" := monoid_op (at level 50) : monoid_scope.
Notation "'id'" := monoid_id : monoid_scope.
Notation "x ⁻" := (monoid_inv x) (at level 1) : monoid_scope.

Section Monoid.
  Context
    `{monoid}.
  Open Scope monoid_scope.

  Global Instance mon_id_r : RightIdentity := right_identity.
  Global Instance mon_id_l : LeftIdentity := left_identity.

  Global Instance mon_assoc : Associative := associative.

  Context
    (f : nat -> A).

  Definition big_op_list (l : list nat) f := fold_left monoid_op (map f l) id.
  Definition big_op f n m := big_op_list (seq n (m - n)) f.
  Definition big_op_rev f n m := big_op_list (rev (seq n (m - n))) f.

  Hint Unfold big_op big_op_rev big_op_list : bigop.

  Lemma big_op_S_r n m (nltm : n <= m) :
    big_op f n (S m) = big_op f n m ∘ f m.
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, map_app, fold_left_app, <- le_plus_minus; auto. Qed.

  Lemma big_op_S_l n m (nltm : n <= m) :
    big_op f n (S m) = f n ∘ big_op f (S n) (S m).
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, fold_left_assoc; auto.
         simpl; rewrite (mon_id_l (f n)), (mon_id_r (f n)); auto. Qed.

  Lemma big_op_rev_S_r n m (nltm : n <= m) :
    big_op_rev f n (S m) = big_op_rev f (S n) (S m) ∘ f n.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l by auto; simpl; rewrite map_app, fold_left_app. reflexivity. Qed.

  Lemma big_op_rev_S_l n m (nltm : n <= m) :
    big_op_rev f n (S m) = f m ∘ big_op_rev f n m.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, rev_app_distr, fold_left_assoc, <- le_plus_minus, (mon_id_r (f m)) by auto; simpl;
           rewrite (mon_id_l (f m)); auto. Qed.

  Lemma big_op_rev_nil n m (mltn : m <= n) :
    big_op_rev f n m = id.
  Proof. unfold big_op_rev; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_nil n m (mltn : m <= n) :
    big_op f n m = id.
  Proof. unfold big_op; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_split n m k (nmk : n <= m <= k) :
    (big_op f n m) ∘ (big_op f m k) = big_op f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n = 0); assert (m = 0); subst; try lia. rewrite big_op_nil, mon_id_l. reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_nil (S k)), mon_id_r. reflexivity. lia.
      + rewrite big_op_S_r, mon_assoc, IHk, <- big_op_S_r by lia. reflexivity. Qed.

  Lemma big_op_rev_split n m k (nmk : n <= m <= k) :
    (big_op_rev f m k) ∘ (big_op_rev f n m) = big_op_rev f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n = 0); assert (m = 0); try lia; subst. rewrite big_op_rev_nil, mon_id_l. reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_rev_nil (S k)), mon_id_l. reflexivity. lia.
      + rewrite big_op_rev_S_l, <- mon_assoc, IHk, <- big_op_rev_S_l by lia. reflexivity. Qed.

  Lemma big_op_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op f n m = big_op g (n + k) (m + k).
  Proof.
    intros. unfold big_op, big_op_list. apply f_equal2; [|reflexivity].
    replace (m + k - (n + k)) with (m - n) by lia.
    apply map_seq_ext; intros. rewrite H2. apply f_equal. lia. lia. Qed.

  Lemma big_op_rev_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op_rev f n m = big_op_rev g (n + k) (m + k).
  Proof.
    intros. unfold big_op_rev, big_op_list. apply f_equal2; [|reflexivity].
    rewrite !map_rev. replace (m + k - (n + k)) with (m - n) by lia.
    apply f_equal; apply map_seq_ext; intros. rewrite H2; apply f_equal; lia. lia. Qed.
End Monoid.

Section Group.
  Context
    `{group}.

  Open Scope monoid_scope.

  Global Instance grp_inv_r : RightInverse := right_inverse.
  Global Instance grp_inv_l : LeftInverse := left_inverse.

  Global Instance grp_id_r : RightIdentity := right_identity.
  Global Instance grp_id_l : LeftIdentity := left_identity.

  Global Instance grp_assoc : Associative := associative.

  Lemma inv_unique_r : forall x y, x ∘ y = id -> y = x⁻.
  Proof.
    intros.
    apply (f_equal (monoid_op (monoid_inv x))) in H3.
    rewrite grp_assoc, grp_inv_l, grp_id_l, grp_id_r in H3.
    assumption.
  Qed.

  Lemma inv_unique_l : forall x y, y ∘ x = id -> y = x⁻.
  Proof.
    intros.
    apply (f_equal (fun a => a ∘ x⁻)) in H3.
    rewrite <- mon_assoc, grp_inv_r, mon_id_r, mon_id_l in H3.
    assumption.
  Qed.

  Lemma grp_r_inj : forall x y z, x ∘ y = x ∘ z -> y = z.
  Proof.
    intros.
    apply (f_equal (fun y => x⁻ ∘ y)) in H3.
    rewrite grp_assoc, grp_inv_l in H3.
    rewrite grp_assoc, grp_inv_l in H3.
    rewrite !grp_id_l in H3. assumption.
  Qed.

  Lemma grp_l_inj : forall y x z, x ∘ y = z ∘ y -> x = z.
  Proof.
    intros.
    apply (f_equal (fun x => x ∘ y⁻)) in H3.
    rewrite <- grp_assoc, grp_inv_r in H3.
    rewrite <- grp_assoc, grp_inv_r in H3.
    rewrite !grp_id_r in H3. assumption.
  Qed.

  Lemma inv_op : forall x y, (x ∘ y)⁻ = y⁻ ∘ x⁻.
  Proof.
    intros. symmetry.
    apply inv_unique_r.
    rewrite grp_assoc.
    rewrite <- (grp_assoc x y _).
    rewrite grp_inv_r.
    rewrite grp_id_r.
    rewrite grp_inv_r.
    reflexivity.
  Qed.

  Lemma id_inv : id⁻ = id.
  Proof.
    apply (grp_l_inj id).
    rewrite grp_inv_l.
    rewrite grp_id_r.
    reflexivity.
  Qed.

  Lemma inv_invol : forall x, x⁻⁻ = x.
  Proof.
    intros. symmetry; apply inv_unique_r. apply grp_inv_l.
  Qed.

  Lemma inv_inj : forall x y, x⁻ = y⁻ -> x = y.
  Proof.
    intros. rewrite <- (inv_invol x), <- (inv_invol y). rewrite H3. reflexivity.
  Qed.

  Lemma inv_id : forall x, x⁻ = id -> x = id.
  Proof.
    intros.
    rewrite <- (inv_invol x).
    rewrite H3.
    apply id_inv.
  Qed.
End Group.

Section AbelianGroup.

  Context
    `{abelian_group}.

  Open Scope group_scope.

  Definition opp_unique_r : forall x y, x + y = 0 -> y = -x := inv_unique_r.
  Definition opp_unique_l : forall x y, y + x = 0 -> y = -x := inv_unique_l.

  Definition opp_invol : forall x, - (- x) = x := inv_invol.

  Definition opp_0 : forall x, - x = 0 -> x = 0 := inv_id.
  Definition opp0 : - 0 = 0 := id_inv.

  Definition opp_inj : forall x y, - x = - y -> x = y := inv_inj.

  Global Instance add_0_r : @RightIdentity _ _ abelian_group_op 0 := right_identity.
  Global Instance add_0_l : @LeftIdentity _ _ abelian_group_op 0 := left_identity.

  Global Instance add_assoc : @Associative _ abelian_group_op := associative.
  Global Instance add_comm : @Commutative  _ abelian_group_op := commutative.

  Global Instance add_opp_r : @RightInverse _ abelian_group_op 0 abelian_group_opp := right_inverse.
  Global Instance add_opp_l : @LeftInverse _ abelian_group_op 0 abelian_group_opp := left_inverse.

  Lemma opp_add : forall x y, - (x + y) = - x - y.
  Proof.
    intros; rewrite inv_op, add_comm; reflexivity.
  Qed.

End AbelianGroup.

Section Ring.
  Context
    `{ring}.

  Open Scope ring_scope.
  Open Scope group_scope.

  Global Instance mul_1_r : @RightIdentity _ _ ring_op 1 := right_identity.
  Global Instance mul_1_l : @LeftIdentity _ _ ring_op 1 := left_identity.

  Global Instance mul_assoc : @Associative _ ring_op := associative.

  Global Instance mul_add_distr_l : LeftDistributive := left_distributive.
  Global Instance mul_add_distr_r : RightDistributive := right_distributive.

  Lemma mul_0_r : forall x : A, x * 0 = 0.
  Proof.
    intros.
    replace (x * 0) with (x * 0 + 0) by (apply add_0_r).
    replace 0 with (x * 0 - x * 0) at 2 3 by (apply add_opp_r).
    rewrite add_assoc.
    rewrite <- mul_add_distr_l.
    rewrite add_0_r.
    reflexivity.
  Qed.

  Lemma mul_0_l : forall x, 0 * x = 0.
  Proof.
    intros.
    replace (0 * x) with (0 * x + 0) by (apply add_0_r).
    replace 0 with (0 * x - 0 * x) at 2 3 by (apply add_opp_r).
    rewrite add_assoc.
    rewrite <- mul_add_distr_r.
    rewrite add_0_r.
    reflexivity.
  Qed.

  Lemma opp_mul_l : forall x y, - (x * y) = - x * y.
  Proof.
    intros. symmetry.
    apply opp_unique_l.
    rewrite <- mul_add_distr_r.
    rewrite add_opp_l.
    apply mul_0_l.
  Qed.

  Lemma opp_mul_r : forall x y, - (x * y) = x * - y.
  Proof.
    intros. symmetry.
    apply opp_unique_l.
    rewrite <- mul_add_distr_l.
    rewrite add_opp_l.
    apply mul_0_r.
  Qed.
End Ring.

Section CommutativeRing.
  Context
    `{commutative_ring}.

  Global Instance mul_comm : @Commutative _ ring_op := commutative.

  Open Scope ring_scope.
  Open Scope group_scope.

  Lemma ring_ring_theory : @ring_theory A 0 1 abelian_group_op ring_op  (fun x y => x + (- y)) abelian_group_opp eq.
  Proof.
    split; intros.
    - apply add_0_l.
    - apply add_comm.
    - apply add_assoc.
    - apply mul_1_l.
    - apply mul_comm.
    - apply mul_assoc.
    - apply mul_add_distr_r.
    - reflexivity.
    - apply add_opp_r.
  Qed.

  Add Ring commutative_ring_is_ring : ring_ring_theory.

  Example ex1 : forall x y, x + y = y + x.
  Proof. intros. ring. Qed.

  Example ex2 : forall x, 0 + x = x.
  Proof. intros. ring. Qed.

  Example ex3 : forall x, 1 * x = x.
  Proof. intros. ring. Qed.
End CommutativeRing.

Section __.
  Context
    {A : Type}.

  Class decidable P :=
    dec : {P} + {~ P}.
End __.
Notation decidable_rel r := (forall x y, decidable (r x y)).

Section IntegralDomain.
  Context
    `{integral_domain}.

  Add Ring integral_domain_ring : ring_ring_theory.

  Open Scope ring_scope.
  Open Scope group_scope.

  Lemma mul_r_inj : forall x y z, y <> 0 -> x * y = z * y -> x = z.
  Proof.
    intros.
    assert ((x - z) * y = 0).
    rewrite mul_add_distr_r, H6.
    ring.
    apply zero_rule1 in H7.
    destruct H7.
    - apply opp_unique_l in H7. rewrite H7. ring.
    - contradiction.
  Qed.

  Lemma mul_l_inj : forall x y z, x <> 0 -> x * y = x * z -> y = z.
  Proof.
    intros.
    eapply mul_r_inj.
    exact H5.
    rewrite mul_comm, H6.
    ring.
  Qed.

  Global Instance integral_domain_zero_rule2 : @ZeroRule2 A A A ring_op 0 0 0.
  Proof.
    intros ? ? ? ? contra; apply zero_rule1 in contra; destruct contra; contradiction.
  Qed.
End IntegralDomain.

Section ModuleTheory.
  Context
    `{left_module}.

  Open Scope group_scope.
  Open Scope ring_scope.
  Open Scope lmodule_scope.

  Global Instance act_1_l : @LeftIdentity M R module_left_act 1 := left_module_left_identity.

  Lemma act_0_r : forall x, x ⋅ 0 = 0.
  Proof.
    intros.
    replace (x ⋅ 0) with (x ⋅ 0 + 0) by (apply add_0_r).
    replace 0 with (x ⋅ 0 - x ⋅ 0) at 2 3 by (apply add_opp_r).
    rewrite add_assoc.
    rewrite <- left_distributive.
    rewrite add_0_r.
    reflexivity.
  Qed.

  Lemma act_0_l : forall x, 0 ⋅ x = 0.
    intros.
    replace (0 ⋅ x) with (0 ⋅ x + 0) by (apply add_0_r).
    replace 0 with (0 ⋅ x - 0 ⋅ x) by (apply add_opp_r).
    rewrite add_assoc.
    rewrite <- right_distributive.
    rewrite add_0_r.
    reflexivity.
  Qed.

  Lemma opp_act : forall x y, - x ⋅ y = (- x) ⋅ y.
    intros. symmetry. apply opp_unique_r.
    rewrite <- right_distributive.
    rewrite add_opp_r.
    apply act_0_l.
  Qed.
End ModuleTheory.
