Require Import ZArith micromega.Lia.
Require Import micromega.Lra.
Require Import micromega.Lqa.
Require Import List.
Require Import QArith.
Require Import Qpower.
From BY Require Import Q AppendixFdefs Qmin_list Impl MatrixQ Zpower_nat Tactics.

Import ListNotations.
Local Open Scope matQ_scope.
Local Open Scope Q.
Local Coercion inject_Z : Z >-> Q.

(* Inductive inSQ_scaled : Z -> matQ -> Prop := *)
(* | ISQ_scaled : inSQ_scaled 0 I *)
(* | SQc_scaled (w : Z) (P : matQ) : *)
(*     forall (e : Z) (q : Z), *)
(*     inSQ_scaled w P -> *)
(*     (0 <? w)%Z && (has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * betaQ (Z.to_nat w))) = false -> *)
(*     has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * gammaQ (Z.to_nat w) (Z.to_nat e)) = false -> *)
(*     (1 <= e)%Z -> *)
(*     Z.odd q = true -> *)
(*     (1 <= q < 2 ^ (e + 1))%Z -> *)
(*     inSQ_scaled (e + w) (mmult (scaledM e q) P). *)

(* Inductive inSQ : nat -> matQ -> Prop := *)
(* | IS : inSQ 0%nat I *)
(* | Sc (w : nat) (P : matQ) : *)
(*     forall (e : nat) (q : Z), *)
(*     inSQ w P -> *)
(*     (w =? 0)%nat || (has_at_most_norm (mmult (mtrans P) P) (betaQ w)) = true -> *)
(*     has_at_most_norm (mmult (mtrans P) P) (gammaQ w e) = true -> *)
(*     (1 <= e)%nat -> *)
(*     Z.odd q = true -> *)
(*     (1 <= q < 2 ^+ (S e))%Z -> *)
(*     inSQ (w + e) (mmult (Q.M (Z.of_nat e) q) P). *)

Fixpoint depth_first_verify_aux_no_mem_three_fuel_gen m (nodes nodes0 cnodes0 w e0 : Z) (l cl0 : list (Z * matQ)) fuel1 fuel2 :=
  match fuel1 with
  | 0%nat => None
  | S fuel1 =>
    let mm := mmult (mtrans m) m in
    if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None
    else if (0 <? w) && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w))
         then Some (nodes, (w, m) :: l)
         else (fix inner_loop e nodes l fuel2 :=
                 match fuel2 with
                 | 0%nat => None
                 | S fuel2 => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e)))
                            then Some (nodes, (w, m) :: l)
                            else match
                                (fix verify_children cnodes cl fuel4 :=
                                   match fuel4 with
                                   | 0%nat => Some (cnodes, cl)
                                   | S fuel4 => let q := ((2 * fuel4) + 1)%nat in
                                           match
                                             depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat q)) m) nodes0 nodes0 cnodes0 (e + w)%Z e0 cl0 cl0 fuel1 fuel2 with
                                           | None => None
                                           | Some (nodes, l) =>
                                             verify_children (nodes + cnodes)%Z (l ++ cl) fuel4
                                           end
                                   end) cnodes0 cl0 (Z.to_nat (2 ^ e)) with
                              | None => None
                              | Some (cnodes, cl) =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z (l ++ cl) fuel2
                              end
                 end) e0 nodes l fuel2
  end.

(* Lemma test1_lemma P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 : depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> @inSQ_gen_scaled w0 P0 e0 w0 P0. (* -> forall q, Z.odd q = true -> (1 <= q < 2 ^ (e + 1))%Z -> @inSQ_gen_scaled w0 P0 e0 (e + w) (mmult (scaledM e q) P). *) *)
(* Proof. *)
(*   constructor. *)
(*   intros. *)
(*   (* constructor. assumption. *) *)
(*   destruct fuel1.  *)
(*   cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. inversion H. *)
(*   cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. revert H. *)
(*   destruct_ifs. congruence. *)

(*   inversion H. *)

(*                                                                                         (forall P w e q, (e0 <= q <= 2 ^ e)%Z -> e0 <= e -> In (w, P) lres -> (0 <? w) && has_at_most_norm (mmult (mtrans P) P) ((4^w) * betaQ (Z.to_nat w)) = false -> has_at_most_norm (mmult (mtrans P) P) ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) = false -> In ((e + w)%Z, mmult (scaledM e q) P) lres). *)
(* Proof. *)
(*   intros. *)
(*   unfold depth_first_verify_aux_no_mem_three_fuel_gen in *. *)
(*   induction fuel1. inversion H. *)

From BY Require Import InductionPrinciples.

Lemma test_lemma1 P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 nodesres lres :
  depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> In (w0, P0) lres.
Proof.
  destruct fuel1;
    cbn [depth_first_verify_aux_no_mem_three_fuel_gen]. congruence.
  destruct_ifs; intros.  congruence.
  inversion H1. left. reflexivity.

  revert H1.
  revert nodes l.
  generalize e0 at 2.
  induction fuel2; intros. congruence.
  revert H1.
  destruct_ifs; intros. inversion H2. left. reflexivity.
  destruct (
      (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) cnodes0 cl0 (Z.to_nat (2 ^ e1))
    ). split_pairs.
  apply IHfuel2 in H2. assumption. congruence. Qed.

Lemma test_lemma21 P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 nodesres lres :
  depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> has_at_most_norm (mmult (mtrans P0) P0) (4 ^ w0 * alphaQ_nat (Z.to_nat w0)) = true.
Proof.
  destruct fuel1;
    cbn [depth_first_verify_aux_no_mem_three_fuel_gen]. congruence.
  destruct_ifs; intros.  congruence.
  apply negb_false_iff. assumption.

  revert H1.
  revert nodes l.
  generalize e0 at 2.
  induction fuel2; intros. congruence.
  revert H1.
  destruct_ifs; intros. inversion H2.
  apply negb_false_iff. assumption.

  destruct (
      (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) cnodes0 cl0 (Z.to_nat (2 ^ e1))
    ). split_pairs.
  apply IHfuel2 in H2. assumption. congruence. Qed.

Lemma test_lemma31 P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 nodesres lres :
  depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> In (w0, P0) lres /\ has_at_most_norm (mmult (mtrans P0) P0) (4 ^ w0 * alphaQ_nat (Z.to_nat w0)) = true.
Proof.
  destruct fuel1;
    cbn [depth_first_verify_aux_no_mem_three_fuel_gen]. congruence.
  destruct_ifs; intros.  congruence.
  inversion H1.
  split.
  left. reflexivity.
  apply negb_false_iff. assumption.

  revert H1.
  revert nodes l.
  generalize e0 at 2.
  induction fuel2; intros. congruence.
  revert H1.
  destruct_ifs; intros. inversion H2. split. left. reflexivity.
    apply negb_false_iff. assumption.

  destruct (
      (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) cnodes0 cl0 (Z.to_nat (2 ^ e1))
    ). split_pairs.
  apply IHfuel2 in H2. assumption. congruence. Qed.

(* Lemma test_new_lemma31 P P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 nodesres lres : *)
(*   depth_first_verify_aux_no_mem_three_fuel_gen P nodes nodes0 cnodes0 w e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> @in (w0, P0) lres /\ has_at_most_norm (mmult (mtrans P) P) (4 ^ w * alphaQ_nat (Z.to_nat w)) = true. *)
(* Proof. *)
(*   destruct fuel1; *)
(*     cbn [depth_first_verify_aux_no_mem_three_fuel_gen]. congruence. *)
(*   destruct_ifs; intros.  congruence. *)
(*   inversion H1. *)
(*   split. *)
(*   left. reflexivity. *)
(*   apply negb_false_iff. assumption. *)

(*   revert H1. *)
(*   revert nodes l. *)
(*   generalize e0 at 2. *)
(*   induction fuel2; intros. congruence. *)
(*   revert H1. *)
(*   destruct_ifs; intros. inversion H2. split. left. reflexivity. *)
(*     apply negb_false_iff. assumption. *)

(*   destruct ( *)
(*       (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : *)
(*               option (Z * list (Z * matQ)) := *)
(*             match fuel4 with *)
(*             | 0%nat => Some (cnodes, cl) *)
(*             | S fuel5 => *)
(*                 match *)
(*                   depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0) *)
(*                     nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 *)
(*                 with *)
(*                 | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5 *)
(*                 | None => None *)
(*                 end *)
(*             end) cnodes0 cl0 (Z.to_nat (2 ^ e1)) *)
(*     ). split_pairs. *)
(*   apply IHfuel2 in H2. assumption. congruence. Qed. *)

(* Lemma test_lemma32 e1 P0 nodes0 cnodes0 w0 e0 cl0 fuel1 fuel2 fuel3 nodesres lres w P nodes l : *)
(* ((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : *)
(*               option (Z * list (Z * matQ)) := *)
(*             match fuel4 with *)
(*             | 0%nat => Some (cnodes, cl) *)
(*             | S fuel5 => *)
(*                 match *)
(*                   depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0) *)
(*                     nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 *)
(*                 with *)
(*                 | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5 *)
(*                 | None => None *)
(*                 end *)
(*             end) nodes l fuel3 ) *)
(*      = Some (nodesres, lres) -> In (w, P) l -> In (w, P) lres /\ has_at_most_norm (mmult (mtrans P) P) (4 ^ w * alphaQ_nat (Z.to_nat w)) = true. *)
(* Proof. *)
(*   intros. *)
(*   revert H H0. *)
(*   revert l nodes. *)
(*   induction fuel3; intros. inversion H. subst. split. assumption. *)
(*   destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0 *)
(*           nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2). *)
(*   split_pairs. *)
(*   apply IHfuel3 in H. assumption. Search app. apply in_app_iff. right. assumption. inversion H. Qed. *)

Lemma test_lemma2 e1 P0 nodes0 cnodes0 w0 e0 cl0 fuel1 fuel2 fuel3 nodesres lres a nodes l :
((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) nodes l fuel3 )
     = Some (nodesres, lres) -> In a l -> In a lres.
Proof.
  intros.
  revert H H0.
  revert l nodes.
  induction fuel3; intros. inversion H. subst. assumption.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0
          nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2).
  split_pairs.
  apply IHfuel3 in H. assumption. Search app. apply in_app_iff. right. assumption. inversion H. Qed.


Lemma rev_1_natlike_ind_lt (P : Z -> Prop) x : P (Z.pred x) -> (forall y, (0 < y < x)%Z -> P y -> P (Z.pred y)) -> (forall y, (0 <= y)%Z -> (y < x)%Z -> P y).
Proof.
  intros Px Hind y. remember (Z.abs_nat ((Z.pred x) - y)). revert y x Heqn Hind Px.
  induction n; intros.
  - assert (Z.pred x = y) by lia; subst; assumption.
  - destruct (Z.eq_dec (Z.pred x) y); [subst; assumption|].
    replace y with (Z.pred (Z.succ y)) by lia.
    apply Hind; [lia|]; apply IHn with (x:=x); try assumption; lia. Qed.

Lemma rev_1_ind_lt m (P : nat -> Prop) : P (Nat.pred m) -> (forall k, (0 < k < m)%nat -> P k -> P (Nat.pred k)) -> forall k, (k < m)%nat -> P k.
Proof.
  intros.
  assert { l : nat | ((Nat.pred m) - k)%nat = l }. eexists. reflexivity. destruct H2. generalize dependent k.
  induction x; intros.
  replace k with (Nat.pred m) by lia. assumption.
  destruct (S k =? (Nat.pred m))%nat eqn:E2. apply Nat.eqb_eq in E2. replace k with (Nat.pred (Nat.pred m)) by lia. apply H0. lia. assumption.
  apply Nat.eqb_neq in E2.
  replace k with (Nat.pred (S k)) by lia. apply H0. lia.
  apply IHx. lia. lia. Qed.

Lemma test_lemma3 e1 P0 nodes0 cnodes0 w0 e0 cl0 fuel1 fuel2 fuel3 nodesres lres nodes l :
((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) nodes l (S fuel3) )
= Some (nodesres, lres) -> In ((e1 + w0)%Z, mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) lres.
Proof.

  intros.
  induction fuel3.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * 0 + 1))) P0) nodes0 nodes0
                                                         cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2) eqn:E.
  split_pairs. inversion H.
  apply test_lemma1 in E.
  apply in_app_iff. left. assumption. inversion H.
  destruct (
      depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0) nodes0
          nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
    ) eqn:E2.
  split_pairs.
  apply test_lemma1 in E2.

  destruct (
      depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0
          nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
    ).
  split_pairs.
  apply test_lemma2 with (a:=((e1 + w0)%Z, mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0))in H.
  assumption. apply in_app_iff. right.
  apply in_app_iff.   left. assumption.
  inversion H. inversion H. Qed.

Lemma test_lemma23 e1 P0 nodes0 cnodes0 w0 e0 cl0 fuel1 fuel2 fuel3 nodesres lres nodes l :
((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) nodes l (S fuel3) )
= Some (nodesres, lres) -> has_at_most_norm (mmult (mtrans (mmult (scaledM e1 (Z.of_nat (2 * 0 + 1))) P0)) (mmult (scaledM e1 (Z.of_nat (2 * 0 + 1))) P0)) (4 ^ ((e1 + w0)%Z) * alphaQ_nat (Z.to_nat (e1 + w0)%Z)) = true.
Proof.

  intros.
  revert H.
  revert nodes l.
  induction fuel3; intros.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * 0 + 1))) P0) nodes0 nodes0
                                                         cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2) eqn:E.
  split_pairs. inversion H.
  apply test_lemma21 in E.  assumption.
  inversion H.
  destruct (
      depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0) nodes0
          nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
    ) eqn:E2.
  split_pairs.
  apply test_lemma1 in E2.

  destruct (
      depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0
          nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
    ).
  split_pairs.
  apply IHfuel3 in H. assumption. inversion H. inversion H. Qed.

Lemma test_lemma4 e1 P0 nodes0 cnodes0 w0 e0 cl0 fuel1 fuel2 fuel3 nodesres lres nodes l fuel :
((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) nodes l fuel3 )
= Some (nodesres, lres) -> (fuel3 <> 0)%nat -> (fuel < fuel3)%nat -> In ((e1 + w0)%Z, mmult (scaledM e1 (Z.of_nat (2 * fuel + 1))) P0) lres.
Proof.
  destruct fuel3. lia.
  revert nodes l.
  induction fuel3. intros. destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * 0 + 1))) P0) nodes0 nodes0
                                                                                  cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2) eqn:E.
  split_pairs. inversion H.
  apply test_lemma1 in E. apply in_app_iff. left.
  assert (fuel = 0)%nat by lia. subst. assumption. inversion H.
  intros.
  destruct (Nat.eq_dec fuel (S fuel3)). subst.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2) eqn:E2.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2).
  split_pairs.
  apply test_lemma1 in E2.
  apply test_lemma2 with (a:=((e1 + w0)%Z, mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0)) in H.
  assumption.
  apply in_app_iff. right.
  apply in_app_iff. left. assumption.
  split_pairs. inversion H. inversion H.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0) nodes0
          nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2).
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2).
  split_pairs.
  apply IHfuel3 with (nodes:=(z+nodes)%Z) (l:=l0 ++ l).
  assumption. lia. lia.
  split_pairs. inversion H. inversion H. Qed.

Lemma test_lemma24 e1 P0 nodes0 cnodes0 w0 e0 cl0 fuel1 fuel2 fuel3 nodesres lres nodes l fuel :
((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) nodes l fuel3 )
= Some (nodesres, lres) -> (fuel3 <> 0)%nat -> (fuel < fuel3)%nat -> has_at_most_norm (mmult (mtrans (mmult (scaledM e1 (Z.of_nat (2 * fuel + 1))) P0)) (mmult (scaledM e1 (Z.of_nat (2 * fuel + 1))) P0)) (4 ^ ((e1 + w0)%Z) * alphaQ_nat (Z.to_nat (e1 + w0)%Z)) = true.
Proof.
  destruct fuel3. lia.
  revert fuel nodes l.
  induction fuel3. intros. destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * 0 + 1))) P0) nodes0 nodes0
                                                                                  cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2) eqn:E.
  split_pairs. inversion H.
  apply test_lemma21 in E.
  assert (fuel = 0)%nat by lia. subst.
  assumption.  inversion H.
  intros.
  destruct (Nat.eq_dec fuel (S fuel3)). subst.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2) eqn:E2.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2).
  split_pairs.
  apply test_lemma21 in E2. assumption.
  split_pairs. inversion H. inversion H.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2) eqn:E2.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2).
  split_pairs.
  apply IHfuel3 with (fuel:=fuel) in H. assumption. lia. lia.
  split_pairs. inversion H. inversion H. Qed.

Lemma test_new_lemma4 e1 P0 nodes0 cnodes0 w0 e0 cl0 cl1 fuel1 fuel2 fuel3 nodesres lres nodes l fuel :
((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl1 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) nodes l fuel3 )
= Some (nodesres, lres) -> (fuel3 <> 0)%nat -> (fuel < fuel3)%nat -> exists nodesres lres, depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel + 1))) P0) nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl1 fuel1 fuel2 = Some (nodesres, lres).
Proof.
  destruct fuel3. lia.
  revert fuel nodes l.
  induction fuel3. intros. destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * 0 + 1))) P0) nodes0 nodes0
                                                                                  cnodes0 (e1 + w0) e0 cl0 cl1 fuel1 fuel2) eqn:E.
  split_pairs. inversion H.
  (* apply test_lemma21 in E. *)
  assert (fuel = 0)%nat by lia. subst.
  eexists. eexists. apply E.

  inversion H.
  intros.
  destruct (Nat.eq_dec fuel (S fuel3)). subst.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl1 fuel1 fuel2) as [[nodesres2 lres2] H|] eqn:E2. eauto. inversion H.
  (* destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0 *)
                                                         (* nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2). *)
  (* split_pairs. *)
  (* apply test_lemma21 in E2. assumption. *)
  (* split_pairs. inversion H. inversion H. *)
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * S fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl1 fuel1 fuel2) eqn:E2.
  destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0
                                                         nodes0 cnodes0 (e1 + w0) e0 cl0 cl1 fuel1 fuel2).
  split_pairs.
  apply IHfuel3 with (fuel:=fuel) in H. assumption. lia. lia.
  split_pairs. inversion H. inversion H. Qed.

Lemma odd_lemma a n : Z.odd a = true -> (0 <= a < Z.of_nat (2 * n))%Z -> exists m, (m < n)%nat /\ a = Z.of_nat (2 * m + 1).
Proof.
  intros.
  Search Z.odd.
  pose proof Zdiv2_odd_eqn a.
  rewrite H in H1.
  exists (Z.to_nat (Z.div2 a)).
  split. lia. lia. Qed.

Lemma test_lemma5 e1 P0 nodes0 cnodes0 w0 e0 cl0 fuel1 fuel2 fuel3 nodesres lres nodes l q :
((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) nodes l fuel3 )
= Some (nodesres, lres) -> (fuel3 <> 0)%nat -> Z.odd q = true -> (0 <= q < Z.of_nat (2 * fuel3)%nat)%Z -> In ((e1 + w0)%Z, mmult (scaledM e1 q) P0) lres.
Proof.
  intros.
  apply odd_lemma in H2; [|assumption].
  destruct H2 as [m [HH HH2]].
  subst.
  eapply test_lemma4. apply H. assumption. assumption. Qed.

Lemma test_lemma25 e1 P0 nodes0 cnodes0 w0 e0 cl0 fuel1 fuel2 fuel3 nodesres lres nodes l q :
((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) nodes l fuel3 )
= Some (nodesres, lres) -> (fuel3 <> 0)%nat -> Z.odd q = true -> (0 <= q < Z.of_nat (2 * fuel3)%nat)%Z -> has_at_most_norm (mmult (mtrans (mmult (scaledM e1 q) P0)) (mmult (scaledM e1 q) P0)) (4 ^ ((e1 + w0)%Z) * alphaQ_nat (Z.to_nat (e1 + w0)%Z)) = true.
Proof.
  intros.
  apply odd_lemma in H2; [|assumption].
  destruct H2 as [m [HH HH2]].
  subst.
  eapply test_lemma24. apply H. assumption. assumption. Qed.

Lemma test_new_lemma5 e1 P0 nodes0 cnodes0 w0 e0 cl0 cl1 fuel1 fuel2 fuel3 nodesres lres nodes l q :
((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl1 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) nodes l fuel3 )
= Some (nodesres, lres) -> (fuel3 <> 0)%nat -> Z.odd q = true -> (0 <= q < Z.of_nat (2 * fuel3)%nat)%Z -> exists nodesres lres, depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 q) P0) nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl1 fuel1 fuel2 = Some (nodesres, lres).
Proof.
  intros.
  apply odd_lemma in H2; [|assumption].
  destruct H2 as [m [HH HH2]].
  subst.
  eapply test_new_lemma4. apply H. assumption. assumption. Qed.

Lemma test_lemma6 P0 nodes0 cnodes0 w0 e0 cl0 fuel1 fuel2 nodesres lres nodes e l a :
  (fix inner_loop (e nodes : Z) (l : list (Z * matQ)) (fuel2 : nat) {struct fuel2} : option (Z * list (Z * matQ)) :=
     match fuel2 with
     | 0%nat => None
     | S fuel3 =>
       if has_at_most_norm (mmult (mtrans P0) P0) (4 ^ w0 * gammaQ (Z.to_nat w0) (Z.to_nat e))
       then Some (nodes, (w0, P0) :: l)
       else
         match
           (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
              match fuel4 with
              | 0%nat => Some (cnodes, cl)
              | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel5 + 1))) P0) nodes0
                                                               nodes0 cnodes0 (e + w0) e0 cl0 cl0 fuel1 fuel3
                with
                | Some (nodes0, l0) => verify_children (nodes0 + cnodes)%Z (l0 ++ cl) fuel5
                | None => None
                end
              end) cnodes0 cl0 (Z.to_nat (2 ^ e))
         with
         | Some (cnodes, cl) => inner_loop (e + 1)%Z (cnodes + nodes)%Z (l ++ cl) fuel3
         | None => None
         end
     end) e nodes l fuel2 = Some (nodesres, lres) -> In a l -> In a lres.
Proof.
  revert e0 nodes l e.
  induction fuel2.
  - congruence.
  - intros. revert H. destruct_ifs.
    intros. inversion H1. right. assumption.
    destruct(
        (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : option (Z * list (Z * matQ)) :=
       match fuel4 with
       | 0%nat => Some (cnodes, cl)
       | S fuel5 =>
           match
             depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel5 + 1))) P0) nodes0 nodes0 cnodes0
               (e + w0) e0 cl0 cl0 fuel1 fuel2
           with
           | Some (nodes1, l0) => verify_children (nodes1 + cnodes)%Z (l0 ++ cl) fuel5
           | None => None
           end
       end) cnodes0 cl0 (Z.to_nat (2 ^ e))
      ).
    split_pairs.
    intros. eapply IHfuel2. eassumption. apply in_app_iff. left. assumption. congruence. Qed.

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

(* Lemma test2_new_lemma0 q e P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 : *)
(* (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : *)
(*            option (Z * list (Z * matQ)) := *)
(*          match fuel4 with *)
(*          | 0%nat => Some (cnodes, cl) *)
(*          | S fuel5 => *)
(*              match *)
(*                depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel5 + 1))) P0) *)
(*                  nodes0 nodes0 cnodes0 (e + w0) e0 cl0 cl0 fuel1 fuel2 *)
(*              with *)
(*              | Some (nodes0, l0) => verify_children (nodes0 + cnodes)%Z (l0 ++ cl) fuel5 *)
(*              | None => None *)
(*              end *)
(*          end) cnodes0 cl0 (Z.to_nat (2 ^ e)) = Some (nodesres, lres) -> (e0 <= e)%Z -> *)
(*     Z.odd q = true -> (e0 <= q < 2 ^ (e + 1))%Z -> exists nodesres lres, depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e q) P0) nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres).   *)
(* Proof. *)
(*   intros. *)

(* Lemma test2_new_lemma6 q e P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 : *)
(*       (fix inner_loop (e nodes : Z) (l : list (Z * matQ)) (fuel2 : nat) {struct fuel2} : *)
(*          option (Z * list (Z * matQ)) := *)
(*          match fuel2 with *)
(*          | 0%nat => None *)
(*          | S fuel3 => *)
(*            if has_at_most_norm (mmult (mtrans P0) P0) (4 ^ w0 * gammaQ (Z.to_nat w0) (Z.to_nat e)) *)
(*            then Some (nodes, (w0, P0) :: l) *)
(*            else *)
(*              match *)
(*                (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : *)
(*                   option (Z * list (Z * matQ)) := *)
(*                   match fuel4 with *)
(*                   | 0%nat => Some (cnodes, cl) *)
(*                   | S fuel5 => *)
(*                     match *)
(*                       depth_first_verify_aux_no_mem_three_fuel_gen *)
(*                         (mmult (scaledM e (Z.of_nat (2 * fuel5 + 1))) P0) nodes0 nodes0 cnodes0  *)
(*                         (e + w0) e0 cl0 cl0 fuel1 fuel3 *)
(*                     with *)
(*                     | Some (nodes0, l0) => verify_children (nodes0 + cnodes)%Z (l0 ++ cl) fuel5 *)
(*                     | None => None *)
(*                     end *)
(*                   end) cnodes0 cl0 (Z.to_nat (2 ^ e)) *)
(*              with *)
(*              | Some (cnodes, cl) => inner_loop (e + 1)%Z (cnodes + nodes)%Z (l ++ cl) fuel3 *)
(*              | None => None *)
(*              end *)
(*          end) e nodes l fuel2 = Some (nodesres, lres) -> *)
(*     has_at_most_norm (mmult (mtrans P0) P0) ((4 ^ w0) * (gammaQ (Z.to_nat w0) (Z.to_nat e))) = false -> *)
(*     (e0 <= e)%Z -> *)
(*     Z.odd q = true -> (e0 <= q < 2 ^ (e + 1))%Z -> exists nodesres lres, depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e q) P0) nodes nodes0 cnodes0 (e + w0) e0 l cl0 fuel1 fuel2 = Some (nodesres, lres).   *)
(* Proof. *)
(*   intros. induction fuel2. congruence. *)
(*   rewrite H0 in H. *)

(*   destruct ((fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : *)
(*              option (Z * list (Z * matQ)) := *)
(*            match fuel4 with *)
(*            | 0%nat => Some (cnodes, cl) *)
(*            | S fuel5 => *)
(*                match *)
(*                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat (2 * fuel5 + 1))) P0) *)
(*                    nodes0 nodes0 cnodes0 (e + w0) e0 cl0 cl0 fuel1 fuel2 *)
(*                with *)
(*                | Some (nodes0, l0) => verify_children (nodes0 + cnodes)%Z (l0 ++ cl) fuel5 *)
(*                | None => None *)
(*                end *)
(*            end) cnodes0 cl0 (Z.to_nat (2 ^ e))) eqn:E. *)
(*   split_pairs. *)
(*   apply test_new_lemma5 with (q:=q) in E. assumption. *)

Lemma test2_new_lemma P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 : depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> forall e q, (0 <? w0) && (has_at_most_norm (mmult (mtrans P0) P0) ((4 ^ w0) * (betaQ (Z.to_nat w0)))) = false ->
    has_at_most_norm (mmult (mtrans P0) P0) ((4 ^ w0) * (gammaQ (Z.to_nat w0) (Z.to_nat e))) = false ->
    (e0 <= e)%Z ->
    Z.odd q = true -> exists nodesres lres, depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e q) P0) nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres).
Proof.
  intros.
  revert H.
  induction fuel1.
  - cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. congruence.
  - intros. cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in H.
    rewrite H0 in H.
    revert H. destruct_ifs. congruence.
    intros.
    induction fuel2.
    congruence.
    Admitted.

(* Lemma test_lemma P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 : depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> (0 <= e0)%Z -> (forall P w, @inSQ_gen_scaled w0 P0 e0 w P (* -> ~ In (w, P) l  *)-> In (w, P) lres). *)
(* Proof. *)
(*   intros. *)
(*   (* revert H. *) *)
(*   (* revert nodes nodes0 cnodes0 l cl0 fuel1 fuel2 fuel3 lres nodesres. *) *)
(*   (* revert P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel2 fuel3 lres nodesres. *) *)

(*    induction H1. *)
(*   - destruct fuel1. *)
(*     simpl in *. intros; inversion H. *)
(*     cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. revert H. *)
(*     destruct_ifs; intros. inversion H1. *)
(*     inversion H2. left. reflexivity. *)

(*     revert H2. *)
(*     generalize e0 at 2. *)

(*     revert H0. *)
(*     revert nodes nodes0 cnodes0 l cl0 fuel1 lres nodesres e0. *)

(*     induction fuel2. intros. inversion H2. *)
(*     (* revert H1. *) *)
(*     (* intros fuel3 lres noderes w0 e0 P0. *) *)
(*     intros. revert H2. *)
(*     destruct_ifs. intros. inversion H3. left. reflexivity. *)

(*     destruct ( *)
(*         (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : *)
(*          option (Z * list (Z * matQ)) := *)
(*        match fuel4 with *)
(*        | 0%nat => Some (cnodes, cl) *)
(*        | S fuel5 => *)
(*            match *)
(*              depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0) nodes0 *)
(*                nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 *)
(*            with *)
(*            | Some (nodes1, l0) => verify_children (nodes1 + cnodes)%Z (l0 ++ cl) fuel5 *)
(*            | None => None *)
(*            end *)
(*        end) cnodes0 cl0 (Z.to_nat (2 ^ e1)) *)
(*       ). *)
(*     split_pairs. intros. apply IHfuel2 in H3. assumption. assumption. intros. inversion H3. *)
(*   - destruct fuel1. *)
(*     simpl in H. inversion H. *)
(*     cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. revert H. *)
(*     rewrite H2. *)
(*     destruct_ifs. intros. inversion H7. *)

(*     intros. *)
(*     (* inversion H6. *) *)

(*     revert H7. *)
(*     assert (HH:(e0 <= e)%Z). lia. revert HH. *)
(*     assert (HH1:(e0 <= e0)%Z). lia. revert HH1. *)
(*     generalize e0 at 2 3 5. *)
(*     (* generalize e0 at 2. *) *)

(*     revert H0 H1 H2 H5 IHinSQ_gen_scaled H H4 H3 H6. *)
(*     revert nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 e q P0. *)

(*     induction fuel2; *)
(*     intros. *)
(*     inversion H7. *)
(*     revert H7. *)
(*     destruct_ifs. intros. inversion H7. *)
(*     apply has_at_most_norm_false_trans with (N:=(4 ^ w0 * gammaQ (Z.to_nat w0) (Z.to_nat e1))) in H3. *)
(*     congruence. *)

(*     split. *)
(*     apply Qmult_le_0_compat. *)
(*     apply Qpower_pos. lra. *)
(*     apply gammaQ_pos. *)
(*     rewrite Qmult_comm. *)
(*     rewrite (Qmult_comm (4 ^ _) _). *)
(*     apply Qmult_le_compat_r. *)
(*     apply gammaQ_mono. lia. *)
(*     apply Qpower_pos. lra. *)

(*     intros. *)


(*     destruct( *)
(*         (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : *)
(*               option (Z * list (Z * matQ)) := *)
(*             match fuel4 with *)
(*             | 0%nat => Some (cnodes, cl) *)
(*             | S fuel5 => *)
(*                 match *)
(*                   depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0) *)
(*                     nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 *)
(*                 with *)
(*                 | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5 *)
(*                 | None => None *)
(*                 end *)
(*             end) cnodes0 cl0 (Z.to_nat (2 ^ e1)) *)
(*       ) eqn:E. *)
(*     split_pairs. *)

(*     destruct (Z.eq_dec e1 e). *)
(*     subst. *)
(*     apply test_lemma5 with (q:=q) in E. *)
(*     apply test_lemma6 with (a:=((e + w0)%Z, mmult (scaledM e q) P0)) in H8. *)
(*     assumption. *)
(*     apply in_app_iff. right. assumption. *)
(*     Search Z.to_nat. *)
(*     replace (Z.to_nat (2 ^ e)) with (2 ^ (Z.to_nat e))%nat. *)
(*     Search Nat.pow. apply Nat.pow_nonzero. lia. *)
(*     rewrite <- Z_to_nat_pow. reflexivity. lia. lia. assumption. split. lia. *)
(*     replace 2%nat with (Z.to_nat 2). *)
(*     rewrite <- Z2Nat.inj_mul. *)
(*     rewrite Z2Nat.id. *)
(*     replace 2%Z with (2 ^ 1)%Z at 1 by reflexivity. *)
(*     Search Z.pow. *)
(*     rewrite <- Z.pow_add_r by lia. *)
(*     rewrite Z.add_comm. lia. *)
(*     assert (0 <= 2 ^ e)%Z by (apply Z.pow_nonneg; lia). nia. lia. *)
(*     apply Z.pow_nonneg; lia. lia. *)

(*     (* induction fuel3. assert (0 < 2 ^ (e + 1))%Z. apply Z.pow_pos_nonneg. lia. lia.  lia. *) *)

(*     (* destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0 *) *)
(*     (*                                                        nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 (S fuel3)) eqn:E2. *) *)
(*     (* split_pairs. *) *)
(*     (* apply test_lemma1 in E2. *) *)
(*     (* apply test_lemma2 with (a:=((e + w0)%Z, mmult (scaledM e (Z.of_nat (2 * fuel3 + 1))) P0)) in E. *) *)
(*     (* admit.  *) *)
(*     (* assert (forall fuel, (fuel <= fuel3)%nat -> In ((w0 + e)%Z, mmult (scaledM e (Z.of_nat (2 * fuel + 1))) P0) l0). *) *)


(*     (* apply rev_1_ind. *) *)
(*     (* destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0 *) *)
(*     (*                                                        nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 (S fuel3)) eqn:E2. *) *)
(*     (* split_pairs. *) *)

(*     (* intros. *) *)
(*     (* inversion E. subst. *) *)

(*     (* admit. *) *)
(*     (* inversion H8. *) *)
(*     (* subst. *) *)

(*     (* specialize (IHfuel2 (z + nodes)%Z nodesres nodes0 cnodes0 w0 (e0 + 1)%Z l lres cl0 fuel1 fuel3 e q P0 H0) . *) *)
(*     apply IHfuel2 with (e:=e) (q:=q) in H8. *)
(*     assumption. *)
(*     assumption. *)
(*     assumption. *)
(*     assumption. assumption. assumption. *)
(*     assumption. *)
(*     lia. assumption. lia. lia. lia. inversion H8. Qed. *)

(* Lemma test_new2_lemma1 P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 w P : depth_first_verify_aux_no_mem_three_fuel_gen P nodes nodes0 cnodes0 w e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> (0 <= e0)%Z -> @inSQ_gen_scaled w0 P0 e0 w P. *)
(* Proof. *)
(*   induction fuel1. *)
(*   simpl. intros. inversion H. *)
(*   cbn [depth_first_verify_aux_no_mem_three_fuel_gen]. *)
(*   destruct_ifs. congruence. *)
(*   intros. *)
(*   inversion H1. *)

(* Lemma test_new2_lemma P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 w P : depth_first_verify_aux_no_mem_three_fuel_gen P nodes nodes0 cnodes0 w e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> (0 <= e0)%Z -> forall e q, *)
(*     (0 <? w) && (has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * (betaQ (Z.to_nat w)))) = false -> *)
(*     has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) = false -> *)
(*     (e0 <= e)%Z -> *)
(*     Z.odd q = true -> *)
(*     (e0 <= q < 2 ^ (e + 1))%Z -> @inSQ_gen_scaled w0 P0 e0 (e + w) (mmult (scaledM e q) P). *)
(* Proof. *)
(*   intros. *)
(*   revert H H1 H2 H0 H4 H3 H5. *)
(*   revert P w e q fuel2. *)
(*   induction fuel1. *)
(*   - cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *; congruence. *)
(*   - intros; revert H. *)
(*     cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. *)
(*     rewrite H1. *)
(*     destruct_ifs; try congruence. *)
(*     intros. *)
(*     (* apply IHfuel1. *) *)

(*     induction fuel2. inversion H6. *)

(*     revert H6. *)
(*     destruct_ifs. intros. inversion H7. *)
(*     apply has_at_most_norm_false_trans with (N:=(4 ^ w * gammaQ (Z.to_nat w) (Z.to_nat e0))) in H2. *)
(*     congruence. *)

(*     split. *)
(*     apply Qmult_le_0_compat. *)
(*     apply Qpower_pos. lra. *)
(*     apply gammaQ_pos. *)
(*     rewrite Qmult_comm. *)
(*     rewrite (Qmult_comm (4 ^ _) _). *)
(*     apply Qmult_le_compat_r. *)
(*     apply gammaQ_mono. lia. *)
(*     apply Qpower_pos. lra. *)

(*     cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. intros. *)
(*     apply IHfuel2. *)
(*     apply IHfuel1 with (fuel2:=fuel2). *)





(* Lemma test_new2_lemma P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 w P : depth_first_verify_aux_no_mem_three_fuel_gen P nodes nodes0 cnodes0 w e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> (0 <= e0)%Z -> @inSQ_gen_scaled w0 P0 e0 w P (* -> ~ In (w, P) l  *)-> has_at_most_norm (mmult (mtrans P) P) (4 ^ w * alphaQ_nat (Z.to_nat w)) = true. *)
(* Proof. *)
(*   intros. *)
(*   (* revert H. *) *)
(*   (* revert nodes nodes0 cnodes0 l cl0 fuel1 fuel2 fuel3 lres nodesres. *) *)
(*   (* revert P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel2 fuel3 lres nodesres. *) *)


(*    destruct H1. *)
(*   - destruct fuel1. *)
(*     simpl in *. intros; inversion H. *)
(*     cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. revert H. *)
(*     destruct_ifs; intros. inversion H1. *)
(*     inversion H2. *)
(*     apply negb_false_iff. assumption. *)

(*     revert H2. *)
(*     generalize e0 at 2. *)

(*     revert H0. *)
(*     revert nodes nodes0 cnodes0 l cl0 fuel1 lres nodesres e0. *)

(*     induction fuel2. intros. inversion H2. *)
(*     (* revert H1. *) *)
(*     (* intros fuel3 lres noderes w0 e0 P0. *) *)
(*     intros. revert H2. *)
(*     destruct_ifs. intros. inversion H3. *)
(*     apply negb_false_iff. assumption. *)


(*     destruct ( *)
(*         (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : *)
(*          option (Z * list (Z * matQ)) := *)
(*        match fuel4 with *)
(*        | 0%nat => Some (cnodes, cl) *)
(*        | S fuel5 => *)
(*            match *)
(*              depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0) nodes0 *)
(*                nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 *)
(*            with *)
(*            | Some (nodes1, l0) => verify_children (nodes1 + cnodes)%Z (l0 ++ cl) fuel5 *)
(*            | None => None *)
(*            end *)
(*        end) cnodes0 cl0 (Z.to_nat (2 ^ e1)) *)
(*       ). *)
(*     split_pairs. intros. apply IHfuel2 in H3. assumption. assumption. intros. inversion H3. *)
(*   - destruct fuel1. *)
(*     simpl in H. inversion H. *)
(*     cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. revert H. *)
(*     (* rewrite H2. *) *)
(*     destruct_ifs. intros. inversion H7. *)

(*     intros. *)
(*     (* inversion H6. *) *)

(*     revert H7. *)
(*     assert (HH:(e0 <= e)%Z). lia. revert HH. *)
(*     assert (HH1:(e0 <= e0)%Z). lia. revert HH1. *)
(*     generalize e0 at 2 3 5. *)
(*     (* generalize e0 at 2. *) *)

(*     revert H0 H1 H2 H5 IHinSQ_gen_scaled H H4 H3 H6. *)
(*     revert nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 e q P0. *)

(*     induction fuel2; *)
(*     intros. *)
(*     inversion H7. *)
(*     revert H7. *)
(*     destruct_ifs. intros. inversion H7. *)
(*     apply has_at_most_norm_false_trans with (N:=(4 ^ w0 * gammaQ (Z.to_nat w0) (Z.to_nat e1))) in H3. *)
(*     congruence. *)

(*     split. *)
(*     apply Qmult_le_0_compat. *)
(*     apply Qpower_pos. lra. *)
(*     apply gammaQ_pos. *)
(*     rewrite Qmult_comm. *)
(*     rewrite (Qmult_comm (4 ^ _) _). *)
(*     apply Qmult_le_compat_r. *)
(*     apply gammaQ_mono. lia. *)
(*     apply Qpower_pos. lra. *)

(*     intros. *)


(*     destruct( *)
(*         (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} : *)
(*               option (Z * list (Z * matQ)) := *)
(*             match fuel4 with *)
(*             | 0%nat => Some (cnodes, cl) *)
(*             | S fuel5 => *)
(*                 match *)
(*                   depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0) *)
(*                     nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 *)
(*                 with *)
(*                 | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5 *)
(*                 | None => None *)
(*                 end *)
(*             end) cnodes0 cl0 (Z.to_nat (2 ^ e1)) *)
(*       ) eqn:E. *)
(*     split_pairs. *)

(*     destruct (Z.eq_dec e1 e). *)
(*     subst. *)
(*     apply test_lemma25 with (q:=q) in E. assumption. *)
(*     replace (Z.to_nat (2 ^ e)) with (2 ^ (Z.to_nat e))%nat. *)
(*     Search Nat.pow. apply Nat.pow_nonzero. lia. *)
(*     rewrite <- Z_to_nat_pow. reflexivity. lia. lia. assumption. split. lia. *)
(*     replace 2%nat with (Z.to_nat 2). *)
(*     rewrite <- Z2Nat.inj_mul. *)
(*     rewrite Z2Nat.id. *)
(*     replace 2%Z with (2 ^ 1)%Z at 1 by reflexivity. *)
(*     Search Z.pow. *)
(*     rewrite <- Z.pow_add_r by lia. *)
(*     rewrite Z.add_comm. lia. *)
(*     assert (0 <= 2 ^ e)%Z by (apply Z.pow_nonneg; lia). nia. lia. *)
(*     apply Z.pow_nonneg; lia. lia. *)

(*     (* induction fuel3. assert (0 < 2 ^ (e + 1))%Z. apply Z.pow_pos_nonneg. lia. lia.  lia. *) *)

(*     (* destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0 *) *)
(*     (*                                                        nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 (S fuel3)) eqn:E2. *) *)
(*     (* split_pairs. *) *)
(*     (* apply test_lemma1 in E2. *) *)
(*     (* apply test_lemma2 with (a:=((e + w0)%Z, mmult (scaledM e (Z.of_nat (2 * fuel3 + 1))) P0)) in E. *) *)
(*     (* admit.  *) *)
(*     (* assert (forall fuel, (fuel <= fuel3)%nat -> In ((w0 + e)%Z, mmult (scaledM e (Z.of_nat (2 * fuel + 1))) P0) l0). *) *)


(*     (* apply rev_1_ind. *) *)
(*     (* destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0 *) *)
(*     (*                                                        nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 (S fuel3)) eqn:E2. *) *)
(*     (* split_pairs. *) *)

(*     (* intros. *) *)
(*     (* inversion E. subst. *) *)

(*     (* admit. *) *)
(*     (* inversion H8. *) *)
(*     (* subst. *) *)

(*     (* specialize (IHfuel2 (z + nodes)%Z nodesres nodes0 cnodes0 w0 (e0 + 1)%Z l lres cl0 fuel1 fuel3 e q P0 H0) . *) *)
(*     apply IHfuel2 with (e:=e) (q:=q) in H8. *)
(*     assumption. *)
(*     assumption. *)
(*     assumption. *)
(*     assumption. assumption. assumption. *)
(*     assumption. *)
(*     lia. assumption. lia. lia. lia. inversion H8. Qed. *)



(* Lemma test2_new_lemma P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 : depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> forall w P, @inSQ_gen_scaled w0 P0 e0 w P -> depth_first_verify_aux_no_mem_three_fuel_gen P nodes nodes0 cnodes0 w e0 l cl0 fuel1 fuel2 = Some (nodesres, lres). *)
(* Proof. *)

(*   intros. *)
(*   induction H0. *)
(*   assumption. intros. *)
(*   destruct fuel1. *)
(*     cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. congruence.  *)
(*     cbn [depth_first_verify_aux_no_mem_three_fuel_gen]. *)
(*     destruct_ifs.  *)


Lemma test2_lemma P0 nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 fuel2 : depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 = Some (nodesres, lres) -> (0 <= e0)%Z -> (forall P w, @inSQ_gen_scaled w0 P0 e0 w P (* -> ~ In (w, P) l  *)-> has_at_most_norm (mmult (mtrans P) P) (4 ^ w * alphaQ_nat (Z.to_nat w)) = true).
Proof.
  intros.
  (* revert H. *)
  (* revert nodes nodes0 cnodes0 l cl0 fuel1 fuel2 fuel3 lres nodesres. *)
  (* revert P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel2 fuel3 lres nodesres. *)


   induction H1.
  - destruct fuel1.
    simpl in *. intros; inversion H.
    cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. revert H.
    destruct_ifs; intros. inversion H1.
    inversion H2.
    apply negb_false_iff. assumption.

    revert H2.
    generalize e0 at 2.

    revert H0.
    revert nodes nodes0 cnodes0 l cl0 fuel1 lres nodesres e0.

    induction fuel2. intros. inversion H2.
    (* revert H1. *)
    (* intros fuel3 lres noderes w0 e0 P0. *)
    intros. revert H2.
    destruct_ifs. intros. inversion H3.
    apply negb_false_iff. assumption.


    destruct (
        (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
         option (Z * list (Z * matQ)) :=
       match fuel4 with
       | 0%nat => Some (cnodes, cl)
       | S fuel5 =>
           match
             depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0) nodes0
               nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
           with
           | Some (nodes1, l0) => verify_children (nodes1 + cnodes)%Z (l0 ++ cl) fuel5
           | None => None
           end
       end) cnodes0 cl0 (Z.to_nat (2 ^ e1))
      ).
    split_pairs. intros. apply IHfuel2 in H3. assumption. assumption. intros. inversion H3.
  - destruct fuel1.
    simpl in H. inversion H.

    assert (depth_first_verify_aux_no_mem_three_fuel_gen P nodes nodes0 cnodes0 w e0 l cl0 (S fuel1) fuel2 =
            Some (nodesres, lres)).
    admit.
    (* induction fuel1. *)

    cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in H7. revert H7.



    rewrite H2.
    destruct_ifs. congruence.
    (* intros. *)

    (* intros. *)
    (* inversion H6. *)

    revert H7.
    assert (HH:(e0 <= e)%Z). lia. revert HH.
    assert (HH1:(e0 <= e0)%Z). lia. revert HH1.
    generalize e0 at 2 3 5.
    (* generalize e0 at 2. *)

    revert H0 H1 H2 H5 IHinSQ_gen_scaled H H4 H3 H6.
    revert nodes nodesres nodes0 cnodes0 w0 e0 l lres cl0 fuel1 e q P0.

    induction fuel2;
    intros.
    inversion H8.
    revert H8.
    destruct_ifs. intros. inversion H9.
    apply has_at_most_norm_false_trans with (N:=(4 ^ w * gammaQ (Z.to_nat w) (Z.to_nat e1))) in H3.
    congruence.

    split.
    apply Qmult_le_0_compat.
    apply Qpower_pos. lra.
    apply gammaQ_pos.
    rewrite Qmult_comm.
    rewrite (Qmult_comm (4 ^ _) _).
    apply Qmult_le_compat_r.
    apply gammaQ_mono. lia.
    apply Qpower_pos. lra.

    intros.


    destruct(
        (fix verify_children (cnodes : Z) (cl : list (Z * matQ)) (fuel4 : nat) {struct fuel4} :
              option (Z * list (Z * matQ)) :=
            match fuel4 with
            | 0%nat => Some (cnodes, cl)
            | S fuel5 =>
                match
                  depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) P0)
                    nodes0 nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2
                with
                | Some (nodes, l) => verify_children (nodes + cnodes)%Z (l ++ cl) fuel5
                | None => None
                end
            end) cnodes0 cl0 (Z.to_nat (2 ^ e1))
      ) eqn:E.
    split_pairs.

    destruct (Z.eq_dec e1 e).
    subst.
    apply test_lemma25 with (q:=q) in E. assumption.
    replace (Z.to_nat (2 ^ e)) with (2 ^ (Z.to_nat e))%nat.
    Search Nat.pow. apply Nat.pow_nonzero. lia.
    rewrite <- Z_to_nat_pow. reflexivity. lia. lia. assumption. split. lia.
    replace 2%nat with (Z.to_nat 2).
    rewrite <- Z2Nat.inj_mul.
    rewrite Z2Nat.id.
    replace 2%Z with (2 ^ 1)%Z at 1 by reflexivity.
    Search Z.pow.
    rewrite <- Z.pow_add_r by lia.
    rewrite Z.add_comm. lia.
    assert (0 <= 2 ^ e)%Z by (apply Z.pow_nonneg; lia). nia. lia.
    apply Z.pow_nonneg; lia. lia.

    (* induction fuel3. assert (0 < 2 ^ (e + 1))%Z. apply Z.pow_pos_nonneg. lia. lia.  lia. *)

    (* destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0 *)
    (*                                                        nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 (S fuel3)) eqn:E2. *)
    (* split_pairs. *)
    (* apply test_lemma1 in E2. *)
    (* apply test_lemma2 with (a:=((e + w0)%Z, mmult (scaledM e (Z.of_nat (2 * fuel3 + 1))) P0)) in E. *)
    (* admit.  *)
    (* assert (forall fuel, (fuel <= fuel3)%nat -> In ((w0 + e)%Z, mmult (scaledM e (Z.of_nat (2 * fuel + 1))) P0) l0). *)


    (* apply rev_1_ind. *)
    (* destruct (depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel3 + 1))) P0) nodes0 *)
    (*                                                        nodes0 cnodes0 (e1 + w0) e0 cl0 cl0 fuel1 fuel2 (S fuel3)) eqn:E2. *)
    (* split_pairs. *)

    (* intros. *)
    (* inversion E. subst. *)

    (* admit. *)
    (* inversion H8. *)
    (* subst. *)

    (* specialize (IHfuel2 (z + nodes)%Z nodesres nodes0 cnodes0 w0 (e0 + 1)%Z l lres cl0 fuel1 fuel3 e q P0 H0) . *)
    apply IHfuel2 with (e:=e) (q:=q) in H8.
    assumption.
    assumption.
    assumption.
    assumption. assumption. assumption.
    assumption.
    lia. assumption. lia. lia. lia. inversion H8. Qed.


(* Lemma testt_lemma P0 nodes nodesres nodes0 cnodes0 w0 e0 lres cl0 fuel1 fuel2 : depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 [] cl0 fuel1 fuel2 = Some (nodesres, lres) -> (forall w P, In (w, P) lres -> has_at_most_norm (mmult (mtrans P) P) (4 ^ w * alphaQ_nat (Z.to_nat w)) = true). *)
(* Proof. *)
(*   (* intros. induction lres. *) *)
(*   (* inversion H0. *) *)
(*   induction fuel1. *)

(*   cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. congruence.  *)
(*   cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. *)
(*   destruct_ifs. congruence. intros. inversion H1. subst. inversion H2. inversion H3. subst. *)
(*   apply negb_false_iff in H. assumption. inversion H3. *)
(*   intros. *)
(*   induction fuel2. inversion H1. *)
(*   revert H1. *)
(*   destruct_ifs. intros. inversion H3. subst. inversion H2. inversion H4. subst.  *)
(*   apply negb_false_iff in H. assumption. inversion H4. *)
(*   intros. *)




(*   cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *. congruence.  *)
(*   intros. *)
(*   inversion H. *)



(* revert H. cbn *)
(*     intros. *)
(*     (* destruct fuel2.  *) *)
(*     destruct( *)
(*         (fix verify_children (cnodes : Z) (cl : list (Z * mat)) (fuel4 : nat) {struct fuel4} : *)
(*          option (Z * list (Z * mat)) := *)
(*        match fuel4 with *)
(*        | 0%nat => Some (cnodes, cl) *)
(*        | S fuel5 => *)
(*            match *)
(*              depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e0 (Z.of_nat (2 * fuel5 + 1))) P0) nodes0 *)
(*                nodes0 cnodes0 (e0 + w0) e0 cl0 cl0 fuel1 fuel2 fuel3 *)
(*            with *)
(*            | Some (nodes1, l0) => verify_children (nodes1 + cnodes)%Z (l0 ++ cl) fuel5 *)
(*            | None => None *)
(*            end *)
(*        end) cnodes0 cl0 fuel3 *)
(*       ). split_pairs. specialize (IHfuel2 (z + nodes)%Z nodes0 cnodes0 (l ++ l0) cl0 fuel1 fuel3 lres nodesres w0 (e0+ 1)%Z P0 H2). *)


(*   intro *)
(*   induction fuel1. *)
(*   - intros. inversion H. *)
(*   - simpl. intros P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel2 fuel3 lres nodesres. *)
(*     destruct_ifs. intros. inversion H0. *)
(*     intros. inversion H1. *)
(*     destruct H2. *)
(*     simpl. left. reflexivity. *)

(*     simpl *)


(* Fixpoint depth_first_verify_aux_no_mem_three_fuel_gen m (nodes nodes0 cnodes0 w e0 : Z) fuel1 fuel2 fuel3 := *)
(*   match fuel1 with *)
(*   | 0%nat => None *)
(*   | S fuel1 => *)
(*     let mm := mmult (mtrans m) m in *)
(*     if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None *)
(*     else if (0 <? w) && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w)) *)
(*          then Some nodes *)
(*          else (fix inner_loop e nodes fuel2 := *)
(*                  match fuel2 with *)
(*                  | 0%nat => None *)
(*                  | S fuel2 => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) *)
(*                             then Some nodes *)
(*                             else match *)
(*                                 (fix verify_children cnodes fuel4 := *)
(*                                    match fuel4 with *)
(*                                    | 0%nat => Some cnodes *)
(*                                    | S fuel4 => let q := ((2 * fuel4) + 1)%nat in *)
(*                                            match *)
(*                                              depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat q)) m) nodes0 nodes0 cnodes0 (e + w)%Z e0 fuel1 fuel2 fuel3 with *)
(*                                            | None => None *)
(*                                            | Some nodes => *)
(*                                              verify_children (nodes + cnodes)%Z fuel4 *)
(*                                            end *)
(*                                    end) cnodes0 fuel3 with *)
(*                               | None => None *)
(*                               | Some cnodes => *)
(*                                 inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel2 *)
(*                               end *)
(*                  end) e0 nodes fuel2 *)
(*   end. *)


(* Definition depth_first_verify_no_mem fuel := *)
(*   depth_first_verify_aux_no_mem_three_fuel_gen I 1 0 fuel. *)

(* Theorem comp1_con w0 P0 e0 : (exists w P, @inSQ_gen_scaled w0 P0 e0 w P /\ has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * (alphaQ_nat (Z.to_nat w))) = false) -> (forall nodes nodes0 cnodes0 l cl0 fuel1 fuel2 fuel3, depth_first_verify_aux_no_mem_three_fuel_gen P0 nodes nodes0 cnodes0 w0 e0 l cl0 fuel1 fuel2 fuel3 = None). *)
(* Proof. *)
(*   intros. *)

(*   destruct H as [w [P [H1 H2]]]. *)
(*   revert fuel1 fuel2 fuel3 nodes nodes0 cnodes0. *)
(*   induction H1; intros. *)
(*   - simpl in H2. *)


(*   revert fuel2 fuel3 nodes nodes0 cnodes0 e0. *)
(*   induction fuel1; [auto|]; intros. *)

(*   cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *; auto; split_pairs. *)
(*   rewrite H2. reflexivity. *)

(*   - *)

(*   revert IHinSQ_gen_scaled. revert fuel2 fuel3 nodes nodes0 cnodes0. *)
(*   induction fuel1; [auto|]; intros. *)

(*   cbn [depth_first_verify_aux_no_mem_three_fuel_gen] in *; auto; split_pairs. *)
(*   destruct_ifs. reflexivity. *)
(*   inversion H. *)

(*   (* match goal with *) *)
(*   (* | |- (match ?m with _ => _ end) => destruct m *) *)
(*   (* end. *) *)

(*   (* memt. setoid_rewrite H10. *) *)

(*   (* assert (H' := H4). *) *)
(*   (* revert E. revert H'. *) *)

(*   (* generalize e0 at 1 3 5. *) *)

(*   (* revert nodes. *) *)

(*   (* revert H9 H7 H1 H2 H8. *) *)
(*   (* revert t5 t6 g_map bq_map t7. *) *)
(*   (* generalize fuel3 at 2 4. *) *)

(*   induction fuel2; [auto|]; intros. *)

(*   inversion E. *)

(*   split_pairs. memt. setoid_rewrite H18 in E. *)

(*   destruct_ifs; try reflexivity. *)
(*   inversion E. subst. tauto. *)

(*   assert *)
(*     ( *)

(*       match *)
(*         ( *)
(*           fix verify_children (cnodes : Z) (a_map b_map : ZMap.t Q) (g_map bq_map aq_map : ZZMap.t Q) (fuel4 : nat) {struct fuel4} : *)
(*             option (ZMap.t Q * ZMap.t Q * ZZMap.t Q * ZZMap.t Q * ZZMap.t Q * Z) := *)
(*             match fuel4 with *)
(*             | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes) *)
(*             | S fuel5 => *)
(*               match *)
(*                 depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0 *)
(*                                                       (e1 + w) e0 fuel1 fuel2 fuel3 a_map b_map g_map bq_map aq_map *)
(*               with *)
(*               | Some (a_map0, b_map0, g_map0, bq_map0, aq_map0, nodes) => *)
(*                 verify_children (nodes + cnodes)%Z a_map0 b_map0 g_map0 bq_map0 aq_map0 fuel5 *)
(*               | None => None *)
(*               end *)
(*             end) cnodes0 t8 t10 t11 t12 t9 fuel0 *)
(*       with *)
(*       | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) => *)
(*         a_map_correct a_map /\ *)
(*         b_map_correct b_map /\ *)
(*         g_map_correct g_map /\ *)
(*         bq_map_correct bq_map /\ *)
(*         aq_map_correct aq_map /\ *)
(*     (fix verify_children (cnodes : Z) (fuel4 : nat) {struct fuel4} : option Z := *)
(*        match fuel4 with *)
(*        | 0%nat => Some cnodes *)
(*        | S fuel5 => *)
(*            match *)
(*              depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0 *)
(*                (e1 + w) e0 fuel1 fuel2 fuel3 *)
(*            with *)
(*            | Some nodes1 => verify_children (nodes1 + cnodes)%Z fuel5 *)
(*            | None => None *)
(*            end *)
(*        end) cnodes0 fuel0  = Some nodes *)
(*       | None => (fix verify_children (cnodes : Z) (fuel4 : nat) {struct fuel4} : option Z := *)
(*                   match fuel4 with *)
(*                   | 0%nat => Some cnodes *)
(*                   | S fuel0 => *)
(*                     match *)
(*                       depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel0 + 1))) m) nodes0 nodes0 cnodes0 *)
(*                                                                    (e1 + w) e0 fuel1 fuel2 fuel3 *)
(*                     with *)
(*                     | Some nodes1 => verify_children (nodes1 + cnodes)%Z fuel0 *)
(*                     | None => None *)
(*                     end *)
(*                   end) cnodes0 fuel0 = None *)
(*       end). *)

(*   clear E. *)
(*   clear IHfuel2. *)

(*   generalize cnodes0 at 2 4 6. *)
(*   revert cnodes0. *)

(*   revert H17 H15 H13 H14 H16. *)
(*   revert t8 t10 t11 t12 t9. *)
(*   induction fuel0; intros. *)
(*   tauto. *)

(*   assert (IH := IHfuel1). *)

(*   specialize (IH fuel2 fuel3 (mmult (scaledM e1 (Z.of_nat (2 * fuel0 + 1))) m) nodes0 nodes0 cnodes0 *)
(*                  (e1 + w)%Z e0 t8 t10 t11 t12 t9 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(lia)). *)


(*   destruct ( depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel0 + 1))) m) nodes0 nodes0 cnodes0 *)
(*                                                    (e1 + w) e0 fuel1 fuel2 fuel3 t8 t10 t11 t12 t9) eqn:E2. *)
(*   split_pairs. *)

(*   rewrite H30. *)

(*   specialize (IHfuel0 t16 t17 t15 t14 t13 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) cnodes0 (z0 + cnodes1)%Z). *)

(*   destruct ( *)
(*       (fix verify_children (cnodes : Z) (a_map0 b_map0 : ZMap.t Q) (g_map0 bq_map0 aq_map0 : ZZMap.t Q) (fuel4 : nat) {struct fuel4} : *)
(*          option (ZMap.t Q * ZMap.t Q * ZZMap.t Q * ZZMap.t Q * ZZMap.t Q * Z) := *)
(*        match fuel4 with *)
(*        | 0%nat => Some (a_map0, b_map0, g_map0, bq_map0, aq_map0, cnodes) *)
(*        | S fuel5 => *)
(*            match *)
(*              depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0 *)
(*                (e1 + w) e0 fuel1 fuel2 fuel3 a_map0 b_map0 g_map0 bq_map0 aq_map0 *)
(*            with *)
(*            | Some (a_map1, b_map1, g_map1, bq_map1, aq_map1, nodes1) => *)
(*                verify_children (nodes1 + cnodes)%Z a_map1 b_map1 g_map1 bq_map1 aq_map1 fuel5 *)
(*            | None => None *)
(*            end *)
(*        end) (z0 + cnodes1)%Z t16 t17 t15 t14 t13 fuel0) eqn:E4. *)

(*   split_pairs. *)

(*   tauto. *)
(*   tauto. *)

(*   rewrite IH. reflexivity. *)

(*   destruct ((fix verify_children *)
(*              (cnodes : Z) (a_map b_map : ZMap.t Q) (g_map bq_map aq_map : ZZMap.t Q) (fuel4 : nat) {struct fuel4} : *)
(*                option (ZMap.t Q * ZMap.t Q * ZZMap.t Q * ZZMap.t Q * ZZMap.t Q * Z) := *)
(*              match fuel4 with *)
(*              | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes) *)
(*              | S fuel5 => *)
(*                  match *)
(*                    depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0 *)
(*                      (e1 + w) e0 fuel1 fuel2 fuel3 a_map b_map g_map bq_map aq_map *)
(*                  with *)
(*                  | Some (a_map0, b_map0, g_map0, bq_map0, aq_map0, nodes) => *)
(*                      verify_children (nodes + cnodes)%Z a_map0 b_map0 g_map0 bq_map0 aq_map0 fuel5 *)
(*                  | None => None *)
(*                  end *)
(*              end) cnodes0 t8 t10 t11 t12 t9 fuel0). *)

(*   split_pairs. *)
(*   rewrite H30. *)

(*   specialize (IHfuel2 _ t16 t17 t15 t14 t13 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) (z0 + nodes)%Z (e1 + 1)%Z ltac:(lia) E). *)
(*   apply IHfuel2. *)

(*   inversion E. *)


(*   - unfold depth_first_verify_no_mem. *)

(*     unfold depth_first_verify_no_mem. *)
(*     unfold depth_first_verify_aux_no_mem. *)
(*     destruct fuel. *)
(*     + reflexivity. *)
(*     + destruct (negb (has_at_most_norm (mmult (mtrans I) I) (4 ^ 0 * alphaQ_nat (Z.to_nat 0)))). *)
(*       * reflexivity. *)
(*       * simpl in H2. *)

(*         destruct ((0 <? 0%Z) && has_at_most_norm (mmult (mtrans I) I) (4 ^ 0 * betaQ (Z.to_nat 0))) eqn:E. *)
(*         ** simpl in E. inversion E. *)
(*         ** destruct (has_at_most_norm (mmult (mtrans I) I) (4 ^ 0 * gammaQ (Z.to_nat 0) (Z.to_nat 1))) eqn:E2. *)
(*            pose proof gammaQ_0_1. *)
(*            set (gamma01 := gammaQ 0 1). *)
(*            change (gammaQ 0 1) with gamma01 in H. *)
(*            change (Z.to_nat 0) with 0%nat in E2. *)
(*            change (Z.to_nat 1) with 1%nat in E2. *)
(*            change (gammaQ 0 1) with gamma01 in E2. *)
(*            unfold has_at_most_norm in E2. *)
(*            cbn [I mtrans mmult] in E2. *)
(*            setoid_rewrite H in E2. *)
(*            cbn in E2. inversion E2. *)

(*       * destruct ((0 <? 0%Z) && has_at_most_norm (mmult (mtrans I) I) (4 ^ 0 * betaQ (Z.to_nat 0))). *)
(*       unfold has_at_most_norm. *)
(*       cbn [I mtrans mmult Z.to_nat alphaQ_nat betaQ Z.mul Z.add Z.leb Z.pow]. *)
(*       cbn [negb]. *)


(* Proof. *)
(* Theorem comp1 : (exists n fuel, depth_first_verify_no_mem fuel = Some n) -> (forall w P, inSQ w P -> has_at_most_norm (mmult (mtrans P) P) (alphaQ_nat w) = true). *)
(* Proof. *)
(*   intros; destruct H. unfold depth_first_verify_no_mem in H. *)
(*   unfold depth_first_verify_aux_no_mem in H. *)
(*   induction H0. reflexivity. *)
(*   inversion H. *)
(*   destruct (depth_first_verify_aux MatrixQ.I 1 0 100 init_a_map init_b_map init_g_map init_bq_map init_aq_map 1) eqn:E. *)


(* Require Import Reals. *)
(* From BY Require Import Spectral. *)

(* Local Open Scope R. *)



(*     inversion H. *)


(* (* Theorem F22 : (forall w P, inS w P -> mat_norm P <= alpha w). Admitted. *) *)

(* Theorem comp1_con : (exists w P, inSQ w P /\ has_at_most_norm (mmult (mtrans P) P) (alphaQ_nat w) = true) -> *)
(*                     (forall fuel, depth_first_verify_no_mem fuel = None). *)

(* Theorem comp1 : (exists n fuel, depth_first_verify_no_mem fuel = Some n) -> *)
(*                 (forall w P, inSQ w P -> has_at_most_norm (mmult (mtrans P) P) (alphaQ_nat w) = true). *)
