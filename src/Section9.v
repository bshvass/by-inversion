Require Import Bool ZArith micromega.Lia.

From BY Require Import Matrix Divstep Zpower_nat Hierarchy Impl.

Local Open Scope Z.
Local Open Scope mat_scope.
Local Open Scope vec_scope.

Local Open Scope group_scope.
Local Open Scope ring_scope.
Local Open Scope lmodule_scope.

Import Z.

Notation big_mmult_rev := (fun n m f => @big_op_rev _ mmult I f n m).

Theorem _9_1_1 d f g (n m : nat) : (m <= n)%nat -> Z.odd f = true ->
    2 ^+ (n - m) ⋅ [ fn d f g n ; gn d f g n ]=
    big_mmult_rev m n (fun i => Tn d f g i) ⋅ [ fn d f g m ; gn d f g m ].
Proof.
  revert m. induction n; intros.
  - replace m with 0%nat by lia; cbv [module_left_act vmult_left_act vmult]; auto_mat; zify; lia.
  - destruct (Nat.eq_dec m (S n)).
    + subst. rewrite big_op_rev_nil.

      rewrite Nat.sub_diag.
      cbv [scvec_left_act module_left_act vmult_left_act vmult]; auto_mat; zify; lia. lia.
    + rewrite <- minus_Sn_m. rewrite <- Zpower_nat_mul_r.
      rewrite left_action. rewrite Tn_transition.
      rewrite scvec_vmult, <- vmult_scvec.
      rewrite IHn.
      rewrite <- left_action.
      rewrite <- big_op_rev_S_l. reflexivity. all: try lia; assumption. Qed.

Theorem _9_1_2 d f g (n m : nat) : (m <= n)%nat -> odd f = true ->
    [ 1 ; dn d f g n  ] =
    big_mmult_rev m n (fun i => Sn d f g i) ⋅ [ 1 ; dn d f g m ].
Proof.
  revert m. induction n; intros.
  - replace m with 0%nat by lia.
    cbv [scvec_left_act module_left_act vmult_left_act vmult]; auto_mat; zify; lia. 
  - destruct (Nat.eq_dec m (S n)).
    + subst. rewrite big_op_rev_nil.
      cbv [I scvec_left_act module_left_act vmult_left_act vmult]; zify; auto_mat; lia. lia.
    + rewrite Sn_transition. rewrite IHn with (m:=m).
      rewrite <- left_action. rewrite <- big_op_rev_S_l. reflexivity. all: try lia; assumption. Qed.
