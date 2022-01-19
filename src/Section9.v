Require Import Bool ZArith micromega.Lia.

From BY Require Import Matrix Divstep Zpower_nat Impl.
From BY.Hierarchy Require Import Definitions BigOp.

Local Open Scope Z_scope.
Local Open Scope mat_scope.
Local Open Scope vec_scope.

Local Open Scope ring_scope.
Local Open Scope lmod_scope.

Import Z.

(* Notation big_mmult_rev := (fun n m f => @big_op_rev _ mmult I f n m). *)

Theorem _9_1_1 d f g (n m : nat) : (m <= n)%nat -> Z.odd f = true ->
    2 ^+ (n - m) ⋅ [ fn d f g n , gn d f g n ] ≡
    big_mul_rev (fun i => Tn d f g i) m n ⋅ [ fn d f g m , gn d f g m ].
Proof.
  revert m. induction n; intros.
  - replace m with 0%nat by lia; auto_mat.
  - destruct (Nat.eq_dec m (S n)).
    + subst. rewrite big_op_rev_nil.

      rewrite Nat.sub_diag.
      auto_mat; lia. lia.
    + rewrite <- minus_Sn_m. rewrite <- Zpower_nat_mul_r.
      rewrite (left_act_assoc (⋅) Z.mul). rewrite Tn_transition.
      rewrite scvec_vmult, scmat_vmult_swap.
      rewrite IHn.
      rewrite <- (left_act_assoc (⋅) [*]).
      rewrite <- (big_op_rev_S_l [*] 1). reflexivity. all: try lia; assumption. Qed.

Theorem _9_1_2 d f g (n m : nat) : (m <= n)%nat -> odd f = true ->
    [ 1 , dn d f g n  ] ≡
    big_mul_rev (fun i => Sn d f g i) m n ⋅ [ 1 , dn d f g m ].
Proof.
  revert m. induction n; intros.
  - replace m with 0%nat by lia. auto_mat.
  - destruct (Nat.eq_dec m (S n)).
    + subst. rewrite big_op_rev_nil. auto_mat. lia.
    + rewrite Sn_transition. rewrite IHn with (m:=m).
      rewrite <- (left_act_assoc (⋅) [*]). rewrite <- (big_op_rev_S_l [*] 1). reflexivity. all: try lia; assumption. Qed.
