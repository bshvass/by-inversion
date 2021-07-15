Require Import Rbase Reals QArith micromega.Lia micromega.Lra.

From BY Require Import Hierarchy Impl.

Local Open Scope R.

Ltac assert_pow :=
    repeat match goal with
    | [ |- context[?a ^ 2] ] => match goal with
                               | [ _ : 0 <= a ^ 2 |- _ ] => fail 1
                               | [ |- _ ] =>
                                 assert (0 <= a ^ 2) by (apply pow2_ge_0; nra)
                               end
           end.

Ltac assert_sqrt :=
    repeat match goal with
    | [ |- context[sqrt ?a] ] => match goal with
                               | [ _ : 0 <= sqrt a |- _ ] => fail 1
                               | [ |- _ ] =>
                                 assert (0 <= sqrt a) by (apply sqrt_positivity; nra)
                               end
           end.

Ltac split_pairs :=
  repeat match goal with
         | [ |- context[let '(_, _) := ?b in _] ] => let E := fresh in destruct b eqn:E
         | [ H : context[let '(_, _) := ?b in _] |- _ ] => let E := fresh in destruct b eqn:E
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : ?a = ?a |- _ ] => clear H
         | [ H : (?a, ?b) = (?c, ?d) |- _ ] => assert (a = c) by congruence; assert (b = d) by congruence; clear H
         end; subst.

Ltac destruct_ifs :=
  repeat match goal with
         | [ |- context[if ?b then _ else _] ] => let E := fresh in destruct b eqn:E
         end; subst.

Ltac split_pairs2 :=
  repeat match goal with
         | [ |- context[let '(_, _) := ?b in _] ] => let E := fresh in destruct b eqn:E
         | [ H : context[let '(_, _) := ?b in _] |- _ ] => let E := fresh in destruct b eqn:E
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : ?a = ?a |- _ ] => clear H
         | [ H : (?a, ?b) = (?c, ?d) |- _ ] => assert (a = c) by congruence; assert (b = d) by congruence; clear H
         end.

Ltac split_pairs_in H :=
  repeat match H with
         | context[let '(_, _) := ?b in _] => let E := fresh in destruct b eqn:E
         end.

Ltac rify_all := cbv [ring_op abelian_group_op Rplus_abelian_group_op abelian_group_opp Rmult_ring_op
                              Ropp_abelian_group_opp abelian_group_id Rzero_abelian_group_id ring_id Rone_ring_id] in *.
Ltac rify_in H := cbv [ring_op abelian_group_op Rplus_abelian_group_op abelian_group_opp Rmult_ring_op
                               Ropp_abelian_group_opp abelian_group_id Rzero_abelian_group_id ring_id Rone_ring_id] in H.
Ltac rify := cbv [ring_op abelian_group_op Rplus_abelian_group_op abelian_group_opp Rmult_ring_op
                          Ropp_abelian_group_opp abelian_group_id Rzero_abelian_group_id ring_id Rone_ring_id].

Ltac lira :=
  lra +
  (autorewrite with push_izr; try apply lt_IZR; lra) +
  (autorewrite with push_izr; try apply le_IZR; lra) +
  (autorewrite with pull_izr;
       try match goal with
       | [ |- IZR _ < IZR _ ] => try apply IZR_lt
       | [ |- IZR _ <= IZR _ ] => try apply IZR_le
       | [ |- IZR _ <> IZR _ ] => try apply IZR_neq
       end; lia).
