From BY Require Export Hierarchy.Definitions.
From BY.Hierarchy Require Import Monoid.

Local Open Scope grp_scope.

Section Group.

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
