From Coq Require Import Ring.
From BY Require Export Hierarchy.Definitions.
From BY.Hierarchy Require Import Group AbelianGroup CommutativeMonoid Ring.

Section CommutativeRing.

  Local Open Scope ring_scope.

  Class CommutativeRing A `{Equiv A, Op1 A, Op2 A, Id1 A, Id2 A, Inv1 A} :=
    {
      cring_ab_grp :> @AbelianGroup _ _ (+) 0 (-);
      cring_mon :> @CommutativeMonoid _ _ [*] 1;
      cring_distr_l :> LeftDistr (≡) [*] (+);
      cring_distr_r :> RightDistr (≡) [*] (+);
    }.

  Context
    {A : Type}
    `{CommutativeRing A}.

  Global Instance : Ring A. sub_class_tac. Qed.

  Ltac solve_tc :=
    first [ apply reflexivity | apply assoc | apply comm | apply right_id | apply left_id | apply right_inv | apply left_inv | apply left_distr | apply right_distr ]; exact _.

  Instance quot_cring (rel : relation A) `{!RingCongruence rel} `{subrelation A (≡) rel} : @CommutativeRing _ rel _ _ _ _ _.
  Proof.
    repeat split; try apply _;
      red; intros; apply is_subrelation; solve_tc.
  Qed.

  Lemma cring_ring_theory : @ring_theory A 0 1 (+) [*] (fun x y : A => x - y) (-) (≡).
  Proof.
    split; intros; solve_tc.
  Qed.
  Add Ring cring_is_ring : cring_ring_theory.

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
