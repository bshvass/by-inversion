Require Import Bool ZArith micromega.Lia.

Require Import MatrixZ Divstep Zpower_nat BigOp.

Local Open Scope Z.
Local Open Scope mat_scope.
Local Open Scope vec_scope.

Import Z.

Notation big_mmult_rev := (fun n m f => @big_op_rev _ mmult I f n m).

Theorem _9_1_1 d f g (n m : nat) : (m <= n)%nat -> Z.odd f = true ->
    2 ^+ (n - m) **v [ fn d f g n ; gn d f g n ]=
    big_mmult_rev m n (fun i => Tn d f g i) *v [ fn d f g m ; gn d f g m ].
Proof.
  revert m. induction n; intros.
  - replace m with 0%nat by lia; auto_mat.
  - destruct (Nat.eq_dec m (S n)).
    + subst. rewrite big_op_rev_nil.
      rewrite Nat.sub_diag. auto_mat. lia.
    + rewrite <- minus_Sn_m. rewrite <- Zpower_nat_mul_r.
      rewrite <- scvec_scvec. rewrite Tn_transition.
      rewrite scvec_vmult_com.
      rewrite IHn.
      rewrite <- mmult_vmult.
      rewrite <- big_op_rev_S_l. reflexivity. all: try lia; assumption. Qed.

Theorem _9_1_2 d f g (n m : nat) : (m <= n)%nat -> odd f = true ->
    [ 1 ; dn d f g n  ] =
    big_mmult_rev m n (fun i => Sn d f g i) *v [ 1 ; dn d f g m ].
Proof.
  revert m. induction n; intros.
  - replace m with 0%nat by lia; auto_mat.
  - destruct (Nat.eq_dec m (S n)).
    + subst. rewrite big_op_rev_nil. auto_mat. lia.
    + rewrite Sn_transition. rewrite IHn with (m:=m).
      rewrite <- mmult_vmult. rewrite <- big_op_rev_S_l. reflexivity. all: try lia; assumption. Qed.
