From Coq Require Import ZArith Reals QArith micromega.Lia micromega.Lra.

From BY Require Import Hierarchy.

Local Open Scope group_scope.
Local Open Scope ring_scope.

Instance Natadd_monoid_op : Monoid_op nat := Nat.add.
Instance Natzero_monoid_id : Monoid_id nat := O.

Instance Nat_commutative_monoid : @commutative_monoid nat Nat.add O.
Proof. repeat split; red; intros; unfold monoid_op, monoid_id; lia. Qed.

Instance Zadd_abelian_group_op : Abelian_group_op Z := Z.add.
Instance Zzero_abelian_group_id : Abelian_group_id Z := Z0.
Instance Zopp_abelian_group_opp : Abelian_group_opp Z := Z.opp.

Instance Zmult_ring_op : Ring_op Z := Z.mul.
Instance Zone_ring_id : Ring_id Z := Zpos xH.

Instance Z_integral_domain : @integral_domain Z Z.add Z.mul 0 1 Z.opp.
Proof. repeat split; red; intros; auto with zarith.
       apply Zmult_1_r.
       apply Zmult_1_r.
       apply Zmult_1_r.
       cbv. lia.
       change (@ring_op Z _) with Zmult in *.
       change (@abelian_group_id Z _) with Z0 in *.
       lia. Qed.

Instance Z_eq_dec : forall x y : Z, decidable (x = y) := Z.eq_dec.

Instance Rplus_abelian_group_op : Abelian_group_op R := Rplus.
Instance Rzero_abelian_group_id : Abelian_group_id R := R0.
Instance Ropp_abelian_group_opp : Abelian_group_opp R := Ropp.

Instance Rmult_ring_op : Ring_op R := Rmult.
Instance Rone_ring_id : Ring_id R := R1.

Instance R_integral_domain : @integral_domain R Rplus Rmult 0 1 Ropp.
Proof. repeat split; cbv; intros; try ring. nra. nra. Qed.

Instance R_eq_dec : forall x y : R, decidable (x = y) := Req_EM_T.

Ltac rify_all := cbv [ring_op abelian_group_op Rplus_abelian_group_op abelian_group_opp Rmult_ring_op
                              Ropp_abelian_group_opp abelian_group_id Rzero_abelian_group_id ring_id Rone_ring_id] in *.
Ltac rify_in H := cbv [ring_op abelian_group_op Rplus_abelian_group_op abelian_group_opp Rmult_ring_op
                               Ropp_abelian_group_opp abelian_group_id Rzero_abelian_group_id ring_id Rone_ring_id] in H.
Ltac rify := cbv [ring_op abelian_group_op Rplus_abelian_group_op abelian_group_opp Rmult_ring_op
                          Ropp_abelian_group_opp abelian_group_id Rzero_abelian_group_id ring_id Rone_ring_id].

Ltac zify := cbv [ring_op Zmult_ring_op
                          abelian_group_op Zadd_abelian_group_op
                          abelian_group_opp Zopp_abelian_group_opp
                          abelian_group_id
                          Zzero_abelian_group_id
                          ring_id
                          Zone_ring_id
                          monoid_id].
Ltac zify_all := cbv [ring_op Zmult_ring_op
                          abelian_group_op Zadd_abelian_group_op
                          abelian_group_opp Zopp_abelian_group_opp
                          abelian_group_id
                          Zzero_abelian_group_id
                          ring_id
                          Zone_ring_id
                          monoid_id] in *.
Ltac zify_in H := cbv [ring_op Zmult_ring_op
                          abelian_group_op Zadd_abelian_group_op
                          abelian_group_opp Zopp_abelian_group_opp
                          abelian_group_id Zzero_abelian_group_id
                          ring_id Zone_ring_id
                          monoid_id] in H.
