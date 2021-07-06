Require Import ZArith micromega.Lia.
Require Import micromega.Lra.
Require Import micromega.Lqa.
Require Import List.
Require Import QArith.
Require Import Qpower.
From BY Require Import Q AppendixF Qmin_list Impl MatrixQ Zpower_nat.

Import ListNotations.
Local Open Scope mat_scope.
Local Open Scope Q.
Local Coercion inject_Z : Z >-> Q.

Notation "a <=? b" := (match a ?= b with Gt => false | _ => true end).
Notation "a <? b" := (match a ?= b with Lt => true | _ => false end).
Notation "a =? b" := (match a ?= b with Eq => true | _ => false end).

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

Definition M (e q : Z) := [ 0 , 1 / (2 ^ e) ; - 1 / (2 ^ e) , q / (2 ^ (2 * e)) ]%Q.

Definition scaledM (e q : Z) := [ 0 , 2 ^ e ; - (2 ^ e) , inject_Z q ]%Q.

Definition has_at_most_norm (P : mat) N :=
  let '(a, b, c, d) := P in
  let X := (2 * N ^ 2 - a - d) in
  (0 <=? X) && ((a - d) ^ 2 + 4 * b ^ 2 <=? X ^ 2).

Instance has_at_most_norm_Proper : Proper (eq ==> Qeq ==> eq) has_at_most_norm.
Proof.
  repeat red; intros.
  unfold has_at_most_norm.
  split_pairs.
  setoid_rewrite H0. reflexivity. Qed.

Inductive inSQ_scaled : Z -> mat -> Prop :=
| ISQ_scaled : inSQ_scaled 0 I
| SQc_scaled (w : Z) (P : mat) :
    forall (e : Z) (q : Z),
    inSQ_scaled w P ->
    (0 <? w)%Z && (has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * betaQ (Z.to_nat w))) = false ->
    has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * gammaQ (Z.to_nat w) (Z.to_nat e)) = false ->
    (1 <= e)%Z ->
    Z.odd q = true ->
    (1 <= q < 2 ^ (e + 1))%Z ->
    inSQ_scaled (e + w) (mmult (scaledM e q) P).

Inductive inSQ : nat -> mat -> Prop :=
| IS : inSQ 0%nat I
| Sc (w : nat) (P : mat) :
    forall (e : nat) (q : Z),
    inSQ w P ->
    (w =? 0)%nat || (has_at_most_norm (mmult (mtrans P) P) (betaQ w)) = true ->
    has_at_most_norm (mmult (mtrans P) P) (gammaQ w e) = true ->
    (1 <= e)%nat ->
    Z.odd q = true ->
    (1 <= q < 2 ^+ (S e))%Z ->
    inSQ (w + e) (mmult (M (Z.of_nat e) q) P).

Inductive inSQ_gen {P w} : nat -> mat -> Prop :=
| IS_gen : inSQ_gen w P
| Sc_gen (w0 : nat) (P0 : mat) :
    forall (e : nat) (q : Z),
    inSQ_gen w P ->
    (w =? 0)%nat || (has_at_most_norm (mmult (mtrans P) P) (betaQ w)) = true ->
    has_at_most_norm (mmult (mtrans P) P) (gammaQ w e) = true ->
    (1 <= e)%nat ->
    Z.odd q = true ->
    (1 <= q < 2 ^+ (S e))%Z ->
    inSQ_gen (w + e) (mmult (M (Z.of_nat e) q) P).


Fixpoint depth_first_verify_aux_no_mem_three_fuel_gen m (nodes nodes0 cnodes0 w e0 : Z) fuel1 fuel2 fuel3 :=
  match fuel1 with
  | 0%nat => None
  | S fuel1 =>
    let mm := mmult (mtrans m) m in
    if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None
    else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w))
         then Some nodes
         else (fix inner_loop e nodes fuel2 :=
                 match fuel2 with
                 | 0%nat => None
                 | S fuel2 => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e)))
                            then Some nodes
                            else match
                                (fix verify_children cnodes fuel4 :=
                                   match fuel4 with
                                   | 0%nat => Some cnodes
                                   | S fuel4 => let q := ((2 * fuel4) + 1)%nat in
                                           match
                                             depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat q)) m) nodes0 nodes0 cnodes0 (e + w)%Z e0 fuel1 fuel2 fuel3 with
                                           | None => None
                                           | Some nodes =>
                                             verify_children (nodes + cnodes)%Z fuel4
                                           end
                                   end) cnodes0 fuel3 with
                              | None => None
                              | Some cnodes =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel2
                              end
                 end) e0 nodes fuel2
  end.
