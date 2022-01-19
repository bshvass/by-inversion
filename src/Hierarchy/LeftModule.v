Require Import Hierarchy.Definitions Hierarchy.Group Hierarchy.AbelianGroup.

Section LeftModule.
  Context
    `{LeftModule A B}.

  Open Scope sr_scope.
  Open Scope ring_scope.
  Open Scope ab_grp_scope.
  Open Scope lmod_scope.

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
    setoid_replace (0 : A)  with (0 ⋅ x - 0 ⋅ x)
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
    rewrite (right_inv 0 (-) (+)).
    apply act_0_l.
  Qed.

End LeftModule.
