Require Import ZArith micromega.Lia.

From BY Require Import Zpower_nat AppendixE PadicVal.

Local Open Scope Z.

Fixpoint Rtail R0 R1 i {struct i} :=
  match i with
  | 0%nat => R0
  | S j => if R1 =? 0 then 0 else Rtail R1 (- ((split2 R0) mod2 R1) / 2 ^+ (ord2 R1)) j
  end.

Lemma Rtail_S R0 R1 i :
  Rtail R0 R1 (S i) = if R1 =? 0 then 0 else Rtail R1 (- ((split2 R0) mod2 R1) / 2 ^+ (ord2 R1)) i.
Proof. reflexivity. Qed.

Lemma Rtail_R_aux R0 R1 i j :
  Rtail (R_ R0 R1 i) (R_ R0 R1 (S i)) j = R_ R0 R1 (j + i).
Proof.
  revert R0 R1 i; induction j; intros R0 R1 i.
  - reflexivity.
  - rewrite Rtail_S.
    destruct (R_ R0 R1 (S i) =? 0) eqn:E.
    + symmetry; eapply R_zero'. apply Z.eqb_eq in E. apply E. lia.
    + rewrite <- R_S_S' by assumption. rewrite IHj. apply f_equal. lia. Qed.

Lemma Rtail_R R0 R1 i :
  Rtail R0 R1 i = R_ R0 R1 i.
Proof.
  replace R0 with (R_ R0 R1 0) at 1 by reflexivity.
  replace R1 with (R_ R0 R1 1) at 2 by reflexivity. rewrite Rtail_R_aux.
  apply f_equal; lia. Qed.
