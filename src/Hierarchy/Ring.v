From Coq Require Import Ring.
From BY Require Import Hierarchy.Definitions Hierarchy.Group.

Section Ring.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.

  Context
    `{Ring A}.
  Local Instance : @Group A _ (+) 0 (-). sub_class_tac. Qed.

  (* Instance : @AbelianGroup A _ (+) 0 (-) := _. *)

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
