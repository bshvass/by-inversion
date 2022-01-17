Require Import Hierarchy.Definitions Hierarchy.Group Hierarchy.AAC.

Section AbelianGroup.

  Context `{G : AbelianGroup A}.
  Local Open Scope abgrp_scope.

  Global Instance abgrp_grp : Group A. sub_class_tac. Qed.

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
