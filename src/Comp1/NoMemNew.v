Require Import ZArith micromega.Lia.
Require Import micromega.Lra.
Require Import micromega.Lqa.
Require Import List.
Require Import QArith.
Require Import Qpower.
From BY Require Import Q AppendixFdefs Qmin_list Impl Matrix Zpower_nat Tactics Mem.

Import ListNotations.
Local Open Scope mat_scope.
Local Open Scope Q.
Local Coercion inject_Z : Z >-> Q.

Fixpoint depth_first_verify_aux_no_mem_three_fuel_gen (m : mat Q) (w e0 : Z) fuel1 fuel2 :=
  match fuel1 with
  | 0%nat => false
  | S fuel1 =>
    let mm := mmult (mtrans m) m in
    if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w)))
    then false
    else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w))
         then true
         else (fix inner_loop e fuel3 :=
                 match fuel3 with
                 | 0%nat => false
                 | S fuel4 => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e)))
                            then true
                            else match
                                (fix verify_children fuel5 :=
                                   match fuel5 with
                                   | 0%nat => true
                                   | S fuel6 =>
                                           match
                                             depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat ((2 * fuel6) + 1))) m) (e + w)%Z e0 fuel1 fuel2 with
                                           | false => false
                                           | true =>
                                             verify_children fuel6
                                           end
                                   end) (Z.to_nat (2 ^ e)) with
                              | false => false
                              | true =>
                                inner_loop (e + 1)%Z fuel4
                              end
                 end) e0 fuel2
  end.

Lemma lemma1 P0 w0 e0 fuel1 fuel2 :
  depth_first_verify_aux_no_mem_three_fuel_gen P0 w0 e0 fuel1 fuel2 = true -> has_at_most_norm (mmult (mtrans P0) P0) (4 ^ w0 * alphaQ_nat (Z.to_nat w0)) = true.
Proof.
  destruct fuel1;
    cbn [depth_first_verify_aux_no_mem_three_fuel_gen]. congruence.
  destruct_ifs; intros.  congruence.
  apply negb_false_iff. assumption.

  revert H1.
  generalize e0 at 2.
  generalize fuel2 at 1.
  induction fuel2; intros. congruence.
  revert H1.
  destruct_ifs; intros.
  apply negb_false_iff. assumption.

  (* specialize (IHfuel2 (e1 + 1)%Z H3). *)
  apply IHfuel2 in H3. assumption. congruence. Qed.

Lemma lemma11 e P0 w0 e0 fuel1 fuel2 fuel7 fuel :
((fix verify_children (fuel5 : nat) {struct fuel5} :=
            match fuel5 with
            | 0%nat => true
            | S fuel6 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel6 + 1))) P0)
                    (e + w0) e0 fuel1 fuel2
                with
                | true => verify_children fuel6
                | false => false
                end
            end) fuel7 )
= true -> (fuel7 <> 0)%nat -> (fuel < fuel7)%nat -> depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel + 1))) P0) (e + w0) e0 fuel1 fuel2 = true.
Proof.
  destruct fuel7. congruence.
  revert fuel.
  induction fuel7. intros.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * 0 + 1))) P0)
                                                         (e + w0) e0 fuel1 fuel2) eqn:E.
  assert (fuel = 0)%nat by lia. subst. assumption. congruence.

  intros.
  destruct (Nat.eq_dec fuel (S fuel7)). subst.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * S fuel7 + 1))) P0)
                                                         (e + w0) e0 fuel1 fuel2); congruence.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * S fuel7 + 1))) P0)
                                                         (e + w0) e0 fuel1 fuel2).
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel7 + 1))) P0)
                                                         (e + w0) e0 fuel1 fuel2).
  apply IHfuel7. assumption. lia. lia. congruence. congruence. Qed.

Lemma lemma11_rev e P0 w0 e0 fuel1 fuel2 fuel7 :
  (fuel7 <> 0)%nat ->
 (forall fuel, (fuel < fuel7)%nat -> depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel + 1))) P0) (e + w0) e0 fuel1 fuel2 = true) -> ((fix verify_children (fuel5 : nat) {struct fuel5} :=
            match fuel5 with
            | 0%nat => true
            | S fuel6 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel6 + 1))) P0)
                    (e + w0) e0 fuel1 fuel2
                with
                | true => verify_children fuel6
                | false => false
                end
            end) fuel7)
= true.
Proof.
  intros.
  destruct fuel7. congruence.
  rewrite H0.
  induction fuel7. congruence.

  rewrite H0.

  apply IHfuel7. lia. intros. apply H0. lia.  lia. lia. Qed.

Lemma lemma21 e P0 w0 e0 fuel1 fuel2 fuel7 fuel :
((fix verify_children (fuel5 : nat) {struct fuel5} :=
            match fuel5 with
            | 0%nat => true
            | S fuel6 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel6 + 1))) P0)
                    (e + w0) e0 fuel1 fuel2
                with
                | true => verify_children fuel6
                | false => false
                end
            end) fuel7 )
= true -> (fuel7 <> 0)%nat -> (fuel < fuel7)%nat -> has_at_most_norm (mmult (mtrans (mmult (scaledM e (Z.of_nat (2 * fuel + 1))) P0)) (mmult (scaledM e (Z.of_nat (2 * fuel + 1))) P0)) (4 ^ ((e + w0)%Z) * alphaQ_nat (Z.to_nat (e + w0)%Z)) = true.
Proof.
  intros.
  revert H.
  induction fuel7; intros. congruence.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel7 + 1))) P0)
          (e + w0) e0 fuel1 fuel2) eqn:E.
  destruct (Nat.eq_dec fuel fuel7). subst.
  apply lemma1 in E. assumption.

  apply IHfuel7. lia. lia. assumption. congruence. Qed.

Lemma odd_lemma a n : Z.odd a = true -> (0 <= a < Z.of_nat (2 * n))%Z -> exists m, (m < n)%nat /\ a = Z.of_nat (2 * m + 1).
Proof.
  intros.
  pose proof Zdiv2_odd_eqn a.
  rewrite H in H1.
  exists (Z.to_nat (Z.div2 a)).
  split. lia. lia. Qed.

Lemma lemma12 e P0 w0 e0 fuel1 fuel2 fuel7 q :
((fix verify_children (fuel5 : nat) {struct fuel5} :=
            match fuel5 with
            | 0%nat => true
            | S fuel6 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel6 + 1))) P0)
                    (e + w0) e0 fuel1 fuel2
                with
                | true => verify_children fuel6
                | false => false
                end
            end) fuel7 )
= true -> (fuel7 <> 0)%nat -> Z.odd q = true -> (0 <= q < Z.of_nat (2 * fuel7)%nat)%Z -> depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e q) P0) (e + w0) e0 fuel1 fuel2 = true.
Proof.
  intros.
  apply odd_lemma in H2; [|assumption].
  destruct H2 as [m [HH HH2]].
  subst.
  eapply lemma11. apply H. assumption. assumption. Qed.

Lemma lemma22 e P0 w0 e0 fuel1 fuel2 fuel7 q :
((fix verify_children (fuel5 : nat) {struct fuel5} :=
            match fuel5 with
            | 0%nat => true
            | S fuel6 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel6 + 1))) P0)
                    (e + w0) e0 fuel1 fuel2
                with
                | true => verify_children fuel6
                | false => false
                end
            end) fuel7 )
= true -> (fuel7 <> 0)%nat -> Z.odd q = true -> (0 <= q < Z.of_nat (2 * fuel7)%nat)%Z -> has_at_most_norm (mmult (mtrans (mmult (scaledM e q) P0)) (mmult (scaledM e q) P0)) (4 ^ ((e + w0)%Z) * alphaQ_nat (Z.to_nat (e + w0)%Z)) = true.
Proof.
  intros.
  apply odd_lemma in H2; [|assumption].
  destruct H2 as [m [HH HH2]].
  subst.
  eapply lemma21. apply H. assumption. assumption. Qed.

Lemma lemma22_rev e P0 w0 e0 fuel1 fuel2 fuel7 :
  (fuel7 <> 0)%nat ->
 (forall q, Z.odd q = true -> (0 <= q < Z.of_nat (2 * fuel7)%nat)%Z -> depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e q) P0) (e + w0) e0 fuel1 fuel2 = true) -> ((fix verify_children (fuel5 : nat) {struct fuel5} :=
            match fuel5 with
            | 0%nat => true
            | S fuel6 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel6 + 1))) P0)
                    (e + w0) e0 fuel1 fuel2
                with
                | true => verify_children fuel6
                | false => false
                end
            end) fuel7) = true.
Proof.
  intros. apply lemma11_rev. assumption.
  intros.
  apply H0.
  rewrite Nat2Z.inj_add.
  rewrite Nat2Z.inj_mul.
  replace (Z.of_nat 2) with 2%Z by lia.
  replace (Z.of_nat 1) with 1%Z by lia.
  rewrite Z.add_comm.
  apply Z.odd_add_mul_2. lia. Qed.

Lemma Z_to_nat_pow a b : (0 <= a)%Z -> (0 <= b)%Z -> ((Z.to_nat a) ^ (Z.to_nat b) = Z.to_nat (a ^ b))%nat.
Proof.
  remember (Z.to_nat b).
  revert b Heqn. induction n.
  - intros. assert (b = 0)%Z. lia. subst.
    reflexivity.
  - intros.
    assert (b = 1 + Z.of_nat n)%Z by lia.
    rewrite H1.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    rewrite Z2Nat.inj_mul. simpl.
    rewrite IHn with (b:= Z.of_nat n). reflexivity. lia. lia. lia. lia.
    apply Z.pow_nonneg. lia. Qed.

Lemma inner_lemma P0 w0 e0 e1 fuel1 fuel2 fuel8 :
  (fix inner_loop (e : Z) (fuel3 : nat) {struct fuel3} : bool :=
          match fuel3 with
          | 0%nat => false
          | S fuel4 =>
              if has_at_most_norm (mmult (mtrans P0) P0) (4 ^ w0 * gammaQ (Z.to_nat w0) (Z.to_nat e))
              then true
              else
               if
                (fix verify_children (fuel5 : nat) : bool :=
                   match fuel5 with
                   | 0%nat => true
                   | S fuel6 =>
                       if
                        depth_first_verify_aux_no_mem_three_fuel_gen
                          (mmult (scaledM e (Z.of_nat (2 * fuel6 + 1))) P0) (e + w0) e0 fuel1 fuel2
                       then verify_children fuel6
                       else false
                   end) (Z.to_nat (2 ^ e))
               then inner_loop (e + 1)%Z fuel4
               else false
          end) e1 fuel8 = true ->
  forall e q, has_at_most_norm (mmult (mtrans P0) P0) ((4 ^ w0) * (gammaQ (Z.to_nat w0) (Z.to_nat e))) = false ->
  (0 <= e0)%Z -> (e0 <= e1)%Z -> (e1 <= e)%Z ->
  Z.odd q = true -> (e0 <= q < 2 ^ (e + 1))%Z ->
  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e q) P0) (e + w0) e0 fuel1 fuel2 = true.
Proof.
  (* generalize e0 at 2. *)

  revert e1.
  induction fuel8. congruence. intros.
  assert (has_at_most_norm (mmult (mtrans P0) P0) (4 ^ w0 * gammaQ (Z.to_nat w0) (Z.to_nat e1)) = false).
  apply has_at_most_norm_false_trans with (M:=(4 ^ w0 * gammaQ (Z.to_nat w0) (Z.to_nat e))).
  split.
  apply Qmult_le_0_compat.
  apply Qpower_pos. lra.
  apply gammaQ_pos.
  rewrite Qmult_comm.
  rewrite (Qmult_comm (4 ^ _) _).
  apply Qmult_le_compat_r.
  apply gammaQ_mono. lia.
  apply Qpower_pos. lra.
  assumption.
  rewrite H6 in H.
  cbn [depth_first_verify_aux_no_mem_three_fuel_gen].

  destruct
    ((fix verify_children (fuel4 : nat) : bool :=
           match fuel4 with
           | 0%nat => true
           | S fuel5 =>
               if
                depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                  (e1 + w0) e0 fuel1 fuel2
               then verify_children fuel5
               else false
           end) (Z.to_nat (2 ^ e1))) eqn:E.

    destruct (Z.eq_dec e1 e).
    subst.
    apply lemma12 with (q:=q) in E.
    assumption.

    replace (Z.to_nat (2 ^ e)) with (2 ^ (Z.to_nat e))%nat.
    apply Nat.pow_nonzero. lia.
     rewrite <- Z_to_nat_pow. reflexivity. lia. lia. assumption. split. lia.
    replace 2%nat with (Z.to_nat 2).
    rewrite <- Z2Nat.inj_mul.
    rewrite Z2Nat.id.
    replace 2%Z with (2 ^ 1)%Z at 1 by reflexivity.
    rewrite <- Z.pow_add_r by lia.
    rewrite Z.add_comm. lia.
    assert (0 <= 2 ^ e)%Z by (apply Z.pow_nonneg; lia). nia. lia.
    apply Z.pow_nonneg; lia. lia.

  apply IHfuel8 with (e1:=(e1+1)%Z).

 assumption. congruence.
  assumption.

  lia. lia. assumption. lia. congruence. Qed.

Lemma depth_first_verify_aux_no_mem_three_fuel_gen_S P0 w0 e0 fuel1 fuel2 :
  depth_first_verify_aux_no_mem_three_fuel_gen P0 w0 e0 (S fuel1) fuel2 =
  if negb (has_at_most_norm (mmult (mtrans P0) P0) ((4 ^ w0) * alphaQ_nat (Z.to_nat w0)))
  then false
  else if (0 <? w0)%Z && has_at_most_norm (mmult (mtrans P0) P0) ((4^w0) * betaQ (Z.to_nat w0))
       then true
       else (fix inner_loop e fuel3 :=
               match fuel3 with
               | 0%nat => false
               | S fuel4 => if has_at_most_norm (mmult (mtrans P0) P0) ((4^w0) * (gammaQ (Z.to_nat w0) (Z.to_nat e)))
                           then true
                           else match
                               (fix verify_children fuel5 :=
                                  match fuel5 with
                                  | 0%nat => true
                                  | S fuel6 =>
                                              match
                                                depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat ((2 * fuel6) + 1))) P0) (e + w0)%Z e0 fuel1 fuel2 with
                                              | false => false
                                              | true =>
                                                verify_children fuel6
                                              end
                                  end) (Z.to_nat (2 ^ e)) with
                             | false => false
                             | true =>
                               inner_loop (e + 1)%Z fuel4
                             end
               end) e0 fuel2.
Proof. reflexivity. Qed.

Lemma depth_lemma P0 w0 e0 fuel1 fuel2 :
  depth_first_verify_aux_no_mem_three_fuel_gen P0 w0 e0 (S fuel1) fuel2 = true ->
  forall e q, (0 <? w0)%Z && (has_at_most_norm (mmult (mtrans P0) P0) ((4 ^ w0) * (betaQ (Z.to_nat w0)))) = false ->
         has_at_most_norm (mmult (mtrans P0) P0) ((4 ^ w0) * (gammaQ (Z.to_nat w0) (Z.to_nat e))) = false ->
         (0 <= e0)%Z -> (e0 <= e)%Z -> Z.odd q = true -> (e0 <= q < 2 ^ (e + 1))%Z ->
         depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e q) P0) (e + w0) e0 fuel1 fuel2 = true.
Proof.
  intros.
  cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *.
  rewrite H0 in H.
  revert H. destruct_ifs. congruence. intros.
  apply inner_lemma with (e:=e) (q:=q) in H6. assumption.
  assumption. assumption. lia. lia. assumption. assumption. Qed.

Lemma fuel_lemma P0 w0 e0 fuel1 fuel2 :
  (0 <= e0)%Z -> depth_first_verify_aux_no_mem_three_fuel_gen P0 w0 e0 fuel1 fuel2 = true -> depth_first_verify_aux_no_mem_three_fuel_gen P0 w0 e0 (S fuel1) fuel2 = true.
Proof.
  revert P0 w0 e0 fuel2.
  induction fuel1; intros. cbn in *; congruence.
  revert H0.
  rewrite depth_first_verify_aux_no_mem_three_fuel_gen_S.
  rewrite depth_first_verify_aux_no_mem_three_fuel_gen_S.
  destruct_ifs. congruence. congruence.

  generalize fuel2 at 1 3.
  assert (He0: (e0 <= e0)%Z) by lia.
  revert He0.
  generalize e0 at 2 4 6.
  induction fuel2; intros.
  congruence. intros.
  destruct_ifs. congruence.

  (* apply IHfuel2. *)
  apply IHfuel2. lia.

  destruct ((fix verify_children (fuel5 : nat) : bool :=
            match fuel5 with
            | 0%nat => true
            | S fuel6 =>
                if
                 depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel6 + 1))) P0)
                   (e1 + w0) e0 fuel1 fuel0
                then verify_children fuel6
                else false
            end) (Z.to_nat (2 ^ e1))
    ) eqn:E.
  assumption. congruence.

  destruct ((fix verify_children (fuel5 : nat) : bool :=
            match fuel5 with
            | 0%nat => true
            | S fuel6 =>
                if
                 depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel6 + 1))) P0)
                   (e1 + w0) e0 fuel1 fuel0
                then verify_children fuel6
                else false
            end) (Z.to_nat (2 ^ e1))
    ) eqn:E.
  epose proof (lemma22_rev e1 P0 w0 e0 (S fuel1) fuel0 (Z.to_nat (2 ^ e1)) _ _). congruence.
  congruence.

  Unshelve.
    replace (Z.to_nat (2 ^ e1)) with (2 ^ (Z.to_nat e1))%nat.
    apply Nat.pow_nonzero. lia.
    rewrite <- Z_to_nat_pow. reflexivity. lia.

    lia.

    intros.
    apply lemma12 with (q:=q) in E.
    apply IHfuel1. lia. assumption.

    replace (Z.to_nat (2 ^ e1)) with (2 ^ (Z.to_nat e1))%nat.
    apply Nat.pow_nonzero. lia.
    rewrite <- Z_to_nat_pow. reflexivity. lia. lia. assumption. assumption. Qed.

Lemma inSQ_depth P0 w0 e0 fuel1 fuel2 :
(0 <= e0)%Z -> depth_first_verify_aux_no_mem_three_fuel_gen P0 w0 e0 fuel1 fuel2 = true ->
(forall w P, @inSQ_gen_scaled w0 P0 e0 w P -> depth_first_verify_aux_no_mem_three_fuel_gen P w e0 fuel1 fuel2 = true).
Proof.
  intros.
  induction H1. assumption.
  apply fuel_lemma in IHinSQ_gen_scaled.
  apply depth_lemma with (e:=e) (q:=q) in IHinSQ_gen_scaled.
  assumption. assumption. assumption. lia. lia. assumption. lia. lia. Qed.

Lemma depth_verify_spec P0 w0 e0 fuel1 fuel2 :
  (0 <= e0)%Z -> depth_first_verify_aux_no_mem_three_fuel_gen P0 w0 e0 fuel1 fuel2 = true ->
  forall w P, @inSQ_gen_scaled w0 P0 e0 w P -> has_at_most_norm (mmult (mtrans P) P) (4 ^ w * alphaQ_nat (Z.to_nat w)) = true.
Proof.
  intros.
  apply lemma1 with (e0:=e0) (fuel1:=fuel1) (fuel2:=fuel2).
  apply inSQ_depth with (P0:=P0) (w0:=w0). assumption. assumption. assumption. Qed.

Lemma old_no_mem P0 w0 e0 fuel1 fuel2 nodes nodes0 cnodes resnodes :
  Mem.depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes w0 e0 fuel1 fuel2 = Some resnodes ->
  depth_first_verify_aux_no_mem_three_fuel_gen P0 w0 e0 fuel1 fuel2 = true.
Proof.
  revert fuel2 P0 w0 e0 nodes nodes0 cnodes resnodes.
  induction fuel1. simpl; congruence.
  cbn [depth_first_verify_aux_no_mem_three_fuel_gen Mem.depth_first_verify_aux_no_mem_three_fuel_gen].
  intros. revert H.
  destruct_ifs; try congruence.
  generalize e0 at 2 4.
  generalize nodes at 1.
  generalize fuel2 at 2 4.
  induction fuel0; try congruence; intros.
  destruct_ifs; try congruence. intros.

  destruct ((fix verify_children (cnodes0 : Z) (fuel4 : nat) {struct fuel4} : option Z :=
       match fuel4 with
       | 0%nat => Some cnodes0
       | S fuel5 =>
           match
             Mem.depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
               nodes0 nodes0 cnodes (e1 + w0) e0 fuel1 fuel2
           with
           | Some nodes1 => verify_children (nodes1 + cnodes0)%Z fuel5
           | None => None
           end
       end) cnodes (Z.to_nat (2 ^ e1))).
  intros.
  apply IHfuel0 in H1. assumption. congruence.

  revert H1.

  match goal with
  | [ |- context [ match ?E with _ => _ end]] => destruct E eqn:E2
  end.
  intros.
  revert E2 H3.
  generalize cnodes at 1.
  generalize cnodes at 1.
  generalize (Z.to_nat (2 ^ e1)).
  induction n. congruence. intros cnodes0 cnodes1.
  destruct (Mem.depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * n + 1))) P0) nodes0
                                                             nodes0 cnodes1 (e1 + w0) e0 fuel1 fuel2) eqn:E3.
  apply IHfuel1 in E3. rewrite E3.  intros. apply IHn with (cnodes:= (z0 + cnodes0)%Z) (cnodes0:=cnodes1).
 assumption.   assumption. congruence.
 congruence.   Qed.

Lemma no_mem_term :
  depth_first_verify_aux_no_mem_three_fuel_gen I 0 1 10000 10000 = true.
Proof.
  apply old_no_mem with (nodes:=1%Z) (nodes0:=1%Z) (cnodes:=0%Z) (resnodes:=3787975117%Z).
  pose proof comp1_theorem.
  unfold depth_first_verify in *.
  pose proof mem_no_mem_three_fuel_aux I 1 1 0 0 1 10000 10000 init_amap init_bmap init_gmap init_bqmap init_aqmap init_a_map_correct init_b_map_correct init_g_map_correct init_bq_map_correct init_aq_map_correct ltac:(lia) ltac:(lia).
  revert H.
  match goal with
  | [ |- context [ match ?E with _ => _ end]] => destruct E eqn:E2
  end.   split_pairs. intros.
  rewrite H in H9. assumption.
  intros. inversion H. Admitted.

Lemma F22_Q : forall w P, @inSQ_gen_scaled 0%Z I 1%Z w P -> has_at_most_norm (mmult (mtrans P) P) (4 ^ w * alphaQ_nat (Z.to_nat w)) = true.
Proof.
  apply depth_verify_spec with (fuel1:=10000%nat) (fuel2:=10000%nat). lia. exact no_mem_term. Qed.
