From Coq Require Import ZArith Reals QArith micromega.Lia micromega.Lra.
From stdpp Require Import base.
From BY Require Import Hierarchy.Definitions.

Global Arguments equiv {_ _} _ _ / : assert.
Global Arguments mag_op {_ _} _ _ / : assert.
Global Arguments sr_op1 {_ _} _ _ / : assert.
Global Arguments abgrp_op {_ _} _ _ / : assert.
Global Arguments abgrp_opp {_ _} _ / : assert.
Global Arguments abgrp_id {_ _} / : assert.
Global Arguments sr_op2 {_ _} _ _ / : assert.
Global Arguments mon_id {_ _} / : assert.
Global Arguments ring_id1 {_ _} / : assert.
Global Arguments ring_id2 {_ _} / : assert.
Global Arguments ring_inv1 {_ _} _ / : assert.
Global Arguments ring_inv2 {_ _} _ / : assert.
Global Arguments grp_inv {_ _} _ / : assert.
Global Arguments left_act {_ _ _} _ _ / : assert.
Global Arguments right_act {_ _ _} _ _ / : assert.

Local Open Scope grp_scope.
Local Open Scope ring_scope.

Instance Nateq_equiv : Equiv nat := eq.
Instance Natadd_monoid_op : MagOp nat := Nat.add.
Instance Natzero_monoid_id : MonId nat := O.

Arguments Nateq_equiv /.
Arguments Natadd_monoid_op /.
Arguments Natzero_monoid_id /.

(* Global Arguments eq_Equiv {_} _ _ / : assert. *)

Instance Nat_commutative_monoid : CommutativeMonoid nat.
Proof. repeat split; repeat red; intros; simpl in *; try lia. Qed.

Instance Zeq_equiv : Equiv Z := eq.
Instance Zadd_abelian_group_op : AbGrpOp Z := Z.add.
Instance Zzero_abelian_group_id : AbGrpId Z := Z0.
Instance Zopp_abelian_group_opp : AbGrpOpp Z := Z.opp.
Instance Zadd_sr_op1 : SrOp1 Z := Z.add.
Instance Zzero_ring_id1 : RingId1 Z := Z0.
Instance Zopp_ring_inv1 : RingInv1 Z := Z.opp.
Instance Zmult_ring_op : SrOp2 Z := Z.mul.
Instance Zone_ring_id : RingId2 Z := 1%Z.

Global Arguments Zeq_equiv /.
Global Arguments Zadd_abelian_group_op /.
Global Arguments Zzero_abelian_group_id /.
Global Arguments Zopp_abelian_group_opp /.
Global Arguments Zadd_sr_op1 /.
Global Arguments Zzero_ring_id1 /.
Global Arguments Zopp_ring_inv1 /.
Global Arguments Zmult_ring_op /.
Global Arguments Zone_ring_id /.

Global Arguments Z.mul : simpl never.

Instance Z_integral_domain : IntegralDomain Z.
Proof. repeat split; repeat red; intros; cbn in *; auto with zarith. nia. Qed.

Instance Z_eq_dec : forall x y : Z, Decision (x = y) := Z.eq_dec.

Instance Req_equiv : Equiv R := eq.
Instance Rplus_abelian_group_op : AbGrpOp R := Rplus.
Instance Rzero_abelian_group_id : AbGrpId R := R0.
Instance Ropp_abelian_group_opp : AbGrpOpp R := Ropp.
Instance Rplus_sr_op1 : SrOp1 R := Rplus.
Instance Rzero_ring_id1 : RingId1 R := R0.
Instance Ropp_ring_inv1 : RingInv1 R := Ropp.
Instance Rmult_ring_op : SrOp2 R := Rmult.
Instance Rone_ring_id : RingId2 R := R1.

Global Arguments Req_equiv /.
Global Arguments Rplus_abelian_group_op /.
Global Arguments Rzero_abelian_group_id /.
Global Arguments Ropp_abelian_group_opp /.
Global Arguments Rplus_sr_op1 /.
Global Arguments Rzero_ring_id1 /.
Global Arguments Ropp_ring_inv1 /.
Global Arguments Rmult_ring_op /.
Global Arguments Rone_ring_id /.

Instance R_integral_domain : IntegralDomain R.
Proof. repeat split; repeat red; simpl in *; intros;  nra. Qed.

(* Instance R_eq_dec : forall x y : R, decidable (x = y) := Req_EM_T. *)
Instance R_eq_dec : RelDecision (=@{R}) := Req_EM_T.

Instance Rle_reflexive : Reflexive Rle. red; intros; lra. Qed.
Instance Rle_transitive : Transitive Rle. red; intros; lra. Qed.

Ltac rify_all := cbv [sr_op1 sr_op2 Rplus_abelian_group_op ring_inv1 Rmult_ring_op
                              Ropp_abelian_group_opp ring_id1 Rzero_abelian_group_id ring_id2 Rone_ring_id] in *.
Ltac rify_in H := cbv [sr_op1 sr_op2 Rplus_abelian_group_op ring_inv1 Rmult_ring_op
                               Ropp_abelian_group_opp ring_id1 Rzero_abelian_group_id ring_id2 Rone_ring_id] in H.
Ltac rify := cbv [abgrp_op abgrp_opp sr_op1 sr_op2 Rplus_abelian_group_op ring_inv1 Rmult_ring_op
                          Ropp_abelian_group_opp ring_id1 Rzero_abelian_group_id ring_id2 Rone_ring_id].

Ltac zify := cbv [sr_op1 Zmult_ring_op
                          sr_op2 Zadd_abelian_group_op
                          ring_inv1 Zopp_abelian_group_opp
                          ring_id1
                          Zzero_abelian_group_id
                          ring_id2
                          Zone_ring_id
                          mon_id].
Ltac zify_all := cbv [sr_op1 Zmult_ring_op
                          sr_op2 Zadd_abelian_group_op
                          ring_inv1 Zopp_abelian_group_opp
                          ring_id1
                          Zzero_abelian_group_id
                          ring_id2
                          Zone_ring_id
                          mon_id] in *.
Ltac zify_in H := cbv [sr_op1 Zmult_ring_op
                          sr_op2 Zadd_abelian_group_op
                          ring_inv1 Zopp_abelian_group_opp
                          ring_id1
                          Zzero_abelian_group_id
                          ring_id2
                          Zone_ring_id
                          mon_id] in H.
