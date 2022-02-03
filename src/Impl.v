From Coq Require Import ZArith Reals QArith Qcanon micromega.Lia micromega.Lra.
From BY.Hierarchy Require Import CommutativeMonoid IntegralDomain.

Global Arguments equiv {_ _} _ _ / : assert.
Global Arguments op1 {_ _} _ _ / : assert.
Global Arguments op2 {_ _} _ _ / : assert.
Global Arguments id1 {_ _} / : assert.
Global Arguments id2 {_ _} / : assert.
Global Arguments inv1 {_ _} _ / : assert.
Global Arguments inv2 {_ _} _ / : assert.
Global Arguments left_act {_ _ _} _ _ / : assert.
Global Arguments right_act {_ _ _} _ _ / : assert.

Section nat.

  Global Instance Nateq_equiv : Equiv nat := eq.
  Global Instance Natadd_op1 : Op1 nat := Nat.add.
  Global Instance Natzero_id1 : Id1 nat := O.

  Global Arguments Nateq_equiv /.
  Global Arguments Natadd_op1 /.
  Global Arguments Natzero_id1 /.

  Global Instance Nat_commutative_monoid : CommutativeMonoid nat.
  Proof. repeat split; repeat red; intros; simpl in *; try lia. Qed.

End nat.

Section Z.

  Global Instance Zeq_equiv : Equiv Z := eq.
  Global Instance Zadd_op1 : Op1 Z := Z.add.
  Global Instance Zzero_id1 : Id1 Z := Z0.
  Global Instance Zopp_inv1 : Inv1 Z := Z.opp.
  Global Instance Zmult_op2 : Op2 Z := Z.mul.
  Global Instance Zone_id2 : Id2 Z := 1%Z.

  Global Arguments Zeq_equiv /.
  Global Arguments Zadd_op1 /.
  Global Arguments Zzero_id1 /.
  Global Arguments Zopp_inv1 /.
  Global Arguments Zmult_op2 /.
  Global Arguments Zone_id2 /.

  Global Arguments Z.mul : simpl never.

  Global Instance Z_integral_domain : IntegralDomain Z.
  Proof. repeat split; repeat red; intros; cbn in *; auto with zarith; nia. Qed.

  Global Instance Z_eq_dec : forall x y : Z, Decision (x = y) := Z.eq_dec.

End Z.

Section R.

  Global Instance Req_equiv : Equiv R := eq.
  Global Instance Rplus_op1 : Op1 R := Rplus.
  Global Instance Rzero_id1 : Id1 R := R0.
  Global Instance Ropp_inv1 : Inv1 R := Ropp.
  Global Instance Rmult_op2 : Op2 R := Rmult.
  Global Instance Rone_id2 : Id2 R := R1.

  Global Arguments Req_equiv /.
  Global Arguments Rplus_op1 /.
  Global Arguments Rzero_id1 /.
  Global Arguments Ropp_inv1 /.
  Global Arguments Rmult_op2 /.
  Global Arguments Rone_id2 /.

  Global Instance R_integral_domain : IntegralDomain R.
  Proof. repeat split; repeat red; simpl in *; intros; nra. Qed.

  Global Instance R_eq_dec : RelDecision (=@{R}) := Req_EM_T.

  Global Instance Rle_reflexive : Reflexive Rle. red; intros; lra. Qed.
  Global Instance Rle_transitive : Transitive Rle. red; intros; lra. Qed.

End R.

Require Import micromega.Lqa.

Section Q.

  Local Open Scope Q_scope.

  Global Instance Qeq_Equiv : Equiv Q := Qeq.
  Global Arguments Qeq_Equiv /.

  Global Instance Qadd_op1 : Op1 Q := Qplus.
  Global Instance Qzero_id1 : Id1 Q := 0%Q.
  Global Instance Qopp_inv1 : Inv1 Q := Qopp.
  Global Instance Qmult_op2 : Op2 Q := Qmult.
  Global Instance Qone_id2 : Id2 Q := 1%Q.
  Global Instance Qinv_inv2 : Inv2 Q := Qinv.

  Global Arguments Qadd_op1 /.
  Global Arguments Qzero_id1 /.
  Global Arguments Qopp_inv1 /.
  Global Arguments Qmult_op2 /.
  Global Arguments Qone_id2 /.

  Global Instance Q_integral_domain : IntegralDomain Q.
  Proof. repeat split; repeat intro; cbn in *; nra. Qed.

  Global Instance Q_eq_dec : forall x y : Q, Decision (x ≡ y) := Qeq_dec.

End Q.

Section Qc.

  Local Open Scope Qc.

  Global Instance Qceq_equiv : Equiv Qc := eq.
  Global Arguments Qceq_equiv /.
  Global Instance Qcplus_op1 : Op1 Qc := Qcplus.
  Global Arguments Qcplus_op1 /.
  Global Instance Qczero_id1 : Id1 Qc := 0.
  Global Arguments Qczero_id1 /.
  Global Instance Qcopp_inv1 : Inv1 Qc := Qcopp.
  Global Arguments Qcopp_inv1 /.

  Global Instance Qcmult_op2 : Op2 Qc := Qcmult.
  Global Arguments Qcmult_op2 /.
  Global Instance Qcone_id2 : Id2 Qc := 1.
  Global Arguments Qcone_id2 /.

  Global Instance Qc_integral_domain : IntegralDomain Qc.
  Proof.
    repeat split; repeat red; intros; cbn in *; try field; try congruence.
    inversion H. apply Qcmult_integral. assumption.
  Qed.

End Qc.
