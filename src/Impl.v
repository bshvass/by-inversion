From Coq Require Import ZArith Reals QArith micromega.Lia micromega.Lra.
From stdpp Require Import base.
From BY Require Import Hierarchy.Definitions.

Global Arguments equiv {_ _} _ _ / : assert.
Global Arguments op1 {_ _} _ _ / : assert.
Global Arguments op2 {_ _} _ _ / : assert.
Global Arguments id1 {_ _} / : assert.
Global Arguments id2 {_ _} / : assert.
Global Arguments inv1 {_ _} _ / : assert.
Global Arguments inv2 {_ _} _ / : assert.
Global Arguments left_act {_ _ _} _ _ / : assert.
Global Arguments right_act {_ _ _} _ _ / : assert.

Local Open Scope grp_scope.
Local Open Scope ring_scope.

Instance Nateq_equiv : Equiv nat := eq.
Instance Natadd_op1 : Op1 nat := Nat.add.
Instance Natzero_id1 : Id1 nat := O.

Arguments Nateq_equiv /.
Arguments Natadd_op1 /.
Arguments Natzero_id1 /.

Instance Nat_commutative_monoid : CommutativeMonoid nat.
Proof. repeat split; repeat red; intros; simpl in *; try lia. Qed.

Instance Zeq_equiv : Equiv Z := eq.
Instance Zadd_op1 : Op1 Z := Z.add.
Instance Zzero_id1 : Id1 Z := Z0.
Instance Zopp_inv1 : Inv1 Z := Z.opp.
Instance Zmult_op2 : Op2 Z := Z.mul.
Instance Zone_id2 : Id2 Z := 1%Z.

Global Arguments Zeq_equiv /.
Global Arguments Zadd_op1 /.
Global Arguments Zzero_id1 /.
Global Arguments Zopp_inv1 /.
Global Arguments Zmult_op2 /.
Global Arguments Zone_id2 /.

Global Arguments Z.mul : simpl never.

Instance Z_integral_domain : IntegralDomain Z.
Proof. repeat split; repeat red; intros; cbn in *; auto with zarith. nia. Qed.

Instance Z_eq_dec : forall x y : Z, Decision (x = y) := Z.eq_dec.

Instance Req_equiv : Equiv R := eq.
Instance Rplus_op1 : Op1 R := Rplus.
Instance Rzero_id1 : Id1 R := R0.
Instance Ropp_inv1 : Inv1 R := Ropp.
Instance Rmult_op2 : Op2 R := Rmult.
Instance Rone_id2 : Id2 R := R1.

Global Arguments Req_equiv /.
Global Arguments Rplus_op1 /.
Global Arguments Rzero_id1 /.
Global Arguments Ropp_inv1 /.
Global Arguments Rmult_op2 /.
Global Arguments Rone_id2 /.

Instance R_integral_domain : IntegralDomain R.
Proof. repeat split; repeat red; simpl in *; intros;  nra. Qed.

Instance R_eq_dec : RelDecision (=@{R}) := Req_EM_T.

Instance Rle_reflexive : Reflexive Rle. red; intros; lra. Qed.
Instance Rle_transitive : Transitive Rle. red; intros; lra. Qed.
