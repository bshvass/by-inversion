Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import micromega.Lia.
Require Import micromega.Lra.
Require Import micromega.Lqa.
Require Import List.

Require Export AlphaQ.

Local Open Scope Q.

From BY Require Import (* Rlemmas AppendixFdefs *) Qmin_list Rmin_list ListLemmas.

Definition alphaQ_high_Z w : Q := (633/1024) ^ w.

Lemma alphaQ_nat_pos w : 0 < alphaQ_nat w.
Proof. do 67 (destruct w as [|w]; simpl; try apply Qlt_shift_div_l; try lra).
       unfold alphaQ_nat_high. apply QExtra.Qpower_pos_lt.
       apply Qlt_shift_div_l; lra. Qed.

Definition alphaQ_quot w i :=
  (alphaQ_nat (w + i)%nat) / (alphaQ_nat i).

Definition betaQ_aux w n :=
  map_seq (alphaQ_quot w) 0%nat n.

Definition betaQ w := Qmin_list (betaQ_aux w 68%nat).

Definition betaQ_quot w j :=
  (betaQ (w + j)) * 2 ^ (Z.of_nat j) * 70 / 169.

Definition gammaQ_aux w e n :=
  map_seq (betaQ_quot w) e n.

Definition gammaQ w e := Qmin_list (gammaQ_aux w e 68%nat).


Require Import OrdersEx.

Lemma alphaQ_min_list : Qmin_list (map_seq (fun j => ((633/1024) ^ (Z.of_nat j)) / alphaQ_nat j) 0 68%nat) == 633^5 / (2^30 * 165219).
Proof.
  vm_cast_no_check (@eq_refl Z ((Qnum (633 ^ 5 / (2 ^ 30 * 165219)) *
   Z_as_DT.pos (Qden (Qmin_list (map_seq (fun j : nat => ((633 / 1024) ^ Z.of_nat j / alphaQ_nat j)%Q) 0 68))))%Z)).
Qed.

Ltac for_each H :=
  match goal with
  | [ H: (?a <= ?b < ?c)%nat |- _ ] => destruct H as [ge lt];
                                  repeat
                                    let t := fresh in inversion ge as [eq|? t];
                                                      [subst; vm_compute; reflexivity|try lia; clear ge; rename t into ge]
  end.
Ltac for_each_new :=
  match goal with
  (* | [ H: (?a <= ?b < ?a)%Z |- _ ] => lia; clear H *)
  | [ H : (?a <= ?b < ?c)%Z |- _ ] => destruct (Z.eq_dec a b); subst; lia;
                                   assert (a + 1 <= b < c) by lia; clear H
  end.

Lemma alphaQ_alphaQ_nat w :
  alphaQ (Z.of_nat w) = alphaQ_nat w.
Proof.
  do 67 (destruct w; try reflexivity). cbn [alphaQ_nat].
  unfold alphaQ.
  replace (_ <=? 66)%Z with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity. Qed.

Lemma alphaQ_nat_alphaQ w : (0 <= w)%Z ->
  alphaQ w = alphaQ_nat (Z.to_nat w).
Proof.
  intros.
  replace w with (Z.of_nat (Z.to_nat w)).
  rewrite Z2Nat.id at 2 by assumption.
  apply alphaQ_alphaQ_nat.
  apply Z2Nat.id; assumption. Qed.
Arguments Z.add /.


From stdpp Require Import base.

Instance Qeq_Equiv : Equiv Q := Qeq.
Arguments Qeq_Equiv /.

Local Open Scope Q.
(* this should go somewhere else *)
Lemma Qmin_mul q x y : 0 <= q -> 0 <= x -> 0 <= y -> Qmin (q * x) (q * y) == q * Qmin x y.
Proof.
  intros. unfold Qmin. unfold GenericMinMax.gmin.
  destruct ((q * x) ?= (q * y)) eqn:E1;
    destruct (x ?= y) eqn:E2; try reflexivity.
  apply Qeq_alt in E1.
  apply Qgt_alt in E2. lra.

  apply Qlt_alt in E1.
  apply Qgt_alt in E2. nra.

  apply Qgt_alt in E1.
  apply Qeq_alt in E2. nra.

  apply Qgt_alt in E1.
  apply Qlt_alt in E2. nra.  Qed.

Lemma betaQ_spec w :
  betaQ w ==
  if (w <=? 66)%nat
        then betaQ w
  else (633/1024) ^ (Z.of_nat w) * (633^5 / (2^30 * 165219)).
Proof.
  destruct ((w <=? 66)%nat) eqn:E; [reflexivity|].
  apply Nat.leb_gt in E.
  setoid_rewrite <- alphaQ_min_list.
  unfold betaQ.
  unfold betaQ_aux.
  generalize 68%nat.
  destruct n.
  simpl. rewrite Qmult_0_r. reflexivity.
  induction n.
  simpl. unfold alphaQ_quot. rewrite Nat.add_0_r.
  rewrite alphaQ_nat_67 by lia. reflexivity.
  rewrite map_seq_snoc.
  setoid_rewrite Qmin_list_app.
  rewrite IHn.
  rewrite (map_seq_snoc (S n)).
  setoid_rewrite Qmin_list_app.
  unfold alphaQ_quot.
  rewrite Nat.add_0_l.
  rewrite (@alphaQ_nat_67 (w + S n)%nat) by lia.
  unfold alphaQ_nat_high.
  replace (Z.of_nat (w + S n))%Z with ((Z.of_nat w) + Z.of_nat (S n))%Z by lia.
  rewrite !Qmin_list_single.
  setoid_rewrite Qpower_plus.
  setoid_rewrite <- Qmin_mul.
  setoid_replace ((633 / 1024) ^ Z.of_nat w * (633 / 1024) ^ Z.of_nat (S n) / alphaQ_nat (S n))
    with ((633 / 1024) ^ Z.of_nat w * ((633 / 1024) ^ Z.of_nat (S n) / alphaQ_nat (S n))).
  reflexivity. cbn -[Qpower Qmult alphaQ_nat]. field.
  apply Qnot_eq_sym.
  apply Qlt_not_eq.
  apply alphaQ_nat_pos.
  apply Qpower_pos.

  apply Qle_shift_div_l. lra. lra.

  pose proof Qmin_list_spec2 (map_seq (fun j : nat => (633 / 1024) ^ Z.of_nat j / alphaQ_nat j) 0 (S n)).
  destruct H as [q []].
  apply map_seq_nonnil. lia.
  apply In_map_seq in H.
  destruct H as [i]. setoid_rewrite H0. rewrite <- H.
  apply Qle_shift_div_l. apply alphaQ_nat_pos.
  setoid_rewrite Qmult_0_l.
  apply Qpower_pos.
  apply Qle_shift_div_l. lra. lra.

  apply Qle_shift_div_l. apply alphaQ_nat_pos.
  setoid_rewrite Qmult_0_l.
  apply Qpower_pos.
  apply Qle_shift_div_l. lra. lra.

  intros contra.
  apply Qeq_eq_bool in contra. cbn in contra. inversion contra.

  apply map_seq_nonnil. lia.

  congruence.

  apply map_seq_nonnil. lia.

  congruence. Qed.

Lemma gammaQ_spec w e :
  gammaQ w e ≡
  if (w + e <=? 66)%nat
        then gammaQ w e
  else  (633/1024) ^ (Z.of_nat (w + e)) * 2 ^ (Z.of_nat e) * (70 / 169) * (633^5 / (2^30 * 165219)).
Proof.
  destruct ((w + e <=? 66)%nat) eqn:E; [reflexivity|].
  apply Nat.leb_gt in E.
  unfold gammaQ.
  unfold gammaQ_aux.
  generalize 67%nat.
  induction n.
  - cbn. unfold betaQ_quot. rewrite betaQ_spec.
    assert ((w + e) <=? 66 = false)%nat. apply Nat.leb_gt. lia.
    rewrite H. field.
  - rewrite map_seq_snoc.
    setoid_rewrite Qmin_list_app.
    rewrite IHn.
    cbn [Qmin_list].
    unfold betaQ_quot.
    setoid_rewrite betaQ_spec.
    assert ((w + (e + S n)) <=? 66 = false)%nat. apply Nat.leb_gt. lia.
    rewrite H.
    rewrite Qminmax.Q.min_l. reflexivity.
    replace (Z.of_nat (w + e)) with
        (Z.of_nat w + Z.of_nat e)%Z by lia.
    replace (Z.of_nat (w + (e + S n))) with
        (Z.of_nat w + (Z.of_nat (e + S n)))%Z by lia.
    setoid_rewrite Qpower_plus.
    do 4 setoid_rewrite <- Qmult_assoc.
    apply Qmult_le_l.
    apply QExtra.Qpower_pos_lt. reflexivity.
    setoid_rewrite Qmult_assoc.
    setoid_replace ((633 / 1024) ^ (Z.of_nat (e + S n)) * (633 ^ 5 / (2 ^ 30 * 165219)) * (2 ^ Z.of_nat (e + S n) * (70 * / 169))) with
        ((633 / 1024) ^ (Z.of_nat (e + S n)) * 2 ^ Z.of_nat (e + S n) * ((633 ^ 5 / (2 ^ 30 * 165219)) * (70 * / 169))) by (cbn -[Qpower Qmult]; field).
    setoid_rewrite <- Qmult_power.
    replace (Z.of_nat (e + S n)) with (Z.of_nat e + Z.of_nat (S n))%Z by lia.
    rewrite Qpower_plus.
    rewrite <- Qmult_assoc.
    apply Qmult_le_l.
    apply QExtra.Qpower_pos_lt. reflexivity.
    rewrite <- Qmult_1_l.
    apply Qmult_le_r. reflexivity.
    apply QExtra.Qpower_le_1_increasing'.
    apply Qle_bool_imp_le. reflexivity. lia.
    apply Qeq_bool_neq. reflexivity.
    apply Qeq_bool_neq. reflexivity.
    apply Qeq_bool_neq. reflexivity.

    apply map_seq_nonnil. lia.
    intros contra. inversion contra. Qed.

Lemma Qmin_list_spec3 l :
  forall a, a <= Qmin_list l -> (forall b, In b l -> a <= b).
Proof.
  intros.
  pose proof Qmin_list_spec l b H0.
  destruct l. inversion H0.
  pose proof Qmin_list_spec2 (q :: l) (ltac:(congruence)).
  destruct H2 as [min []]. rewrite H3 in *. lra. Qed.

Import ListNotations.
Lemma Qmin_cons_le a l : l <> [] -> Qmin_list (a :: l) <= Qmin_list l.
Proof.
  intros.
  destruct l. congruence.
  rewrite Qmin_list_cons.
  apply Qminmax.Q.le_min_r. Qed.

Lemma Qmin_list_map_seq_lemma f (start len : nat) :
  f (start + len)%nat <= f (S (start + len)) ->
  Qmin_list (map_seq f start (S len)) <= Qmin_list (map_seq f (S start) (S len)).
Proof.
  destruct len; intros.
  rewrite Nat.add_0_r in *. assumption.

  rewrite (map_seq_snoc _ (S start)).
  rewrite <- (cons_map_seq _ (S start)).
  (* rewrite map_seq_snoc. *)
  (* rewrite <- cons_map_seq. *)
  setoid_rewrite Qmin_list_snoc.
  apply Qminmax.Q.min_glb_iff.
  split.
  rewrite cons_map_seq.
  rewrite <- cons_map_seq. apply Qmin_cons_le.
  apply map_seq_nonnil. lia.
  rewrite map_seq_snoc.
  rewrite <- cons_map_seq.
  setoid_rewrite Qmin_list_snoc.
  apply Qle_trans with (y:=f(start + S len)%nat).
  apply Qminmax.Q.le_min_r.
  assumption. Qed.

Require Import Tactics.

Lemma gammaQ_S w e : gammaQ w e <= gammaQ w (e + 1).
Proof.
  unfold gammaQ.
  unfold gammaQ_aux.
  replace (e + 1)%nat with (S e) by lia.
  apply Qmin_list_map_seq_lemma.
  unfold betaQ_quot.
  setoid_rewrite betaQ_spec.
  replace (w + (e + 67) <=? 66) with false by (symmetry; apply Nat.leb_gt; nia).
  replace (w + S (e + 67) <=? 66) with false by (symmetry; apply Nat.leb_gt; nia).
  apply Qmult_le_compat_r.
  apply Qmult_le_compat_r.
  rewrite Qmult_comm.
  rewrite (Qmult_comm _ (2 ^ _)).
  rewrite !Qmult_assoc.
  apply Qmult_le_compat_r.
  rewrite !(Nat2Z.inj_add w _).
  setoid_rewrite Qpower_plus.
  rewrite Qmult_comm.
  rewrite (Qmult_comm (2 ^ _) _).
  rewrite <- Qmult_assoc.
  rewrite <- Qmult_assoc.
  setoid_rewrite <- Qmult_power.
  rewrite Qmult_comm.
  rewrite (Qmult_comm _ ((_ * _) ^ _)).

  apply Qmult_le_compat_r.
  apply QExtra.Qpower_le_compat.
  lia. cbv. intros. congruence.
  apply Qpower_pos. cbv. intros. congruence.
  cbv. intros. lia.
  cbv.  lia.
  cbv. congruence.
  lra. cbv. congruence. Qed.

Lemma gammaQ_mono w e1 e2 : (e1 <= e2)%nat -> gammaQ w e1 <= gammaQ w e2.
Proof.
  intros.
  induction e2.
  inversion H. subst. apply Qle_refl.
  destruct (Nat.eq_dec e1 (S e2)). subst.
  apply Qle_refl.
  apply Qle_trans with (y:=gammaQ w e2).
  apply IHe2. lia.
  replace (S e2) with (e2 + 1)%nat.
  apply gammaQ_S. lia. Qed.

Lemma alphaQ_nat_nonneg w : 0 <= alphaQ_nat w.
Proof.
  unfold alphaQ_nat.
  do 67 (destruct w as [|w]; try (lra || cbv; congruence)).
  unfold alphaQ_nat_high. apply Qpower_pos. cbv. congruence. Qed.

Lemma alphaQ_nonneg w : 0 <= alphaQ w.
Proof.
  destruct (Z_le_dec w 0).
  - assert ((w <=? 66) = true)%Z. lia. unfold alphaQ. rewrite H.
    destruct w as [w|w|w]. lra. lia. lra.
  - rewrite alphaQ_nat_alphaQ. apply alphaQ_nat_nonneg. lia. Qed.

From BY Require Import Matrix Hierarchy.

Instance Qadd_abelian_group_op : AbGrpOp Q := Qplus.
Instance Qzero_abelian_group_id : AbGrpId Q := 0%Q.
Instance Qopp_abelian_group_opp : AbGrpOpp Q := Qopp.
Instance Qmult_ring_op : SrOp2 Q := Qmult.
Instance Qone_ring_id : RingId2 Q := 1%Q.

Global Arguments Qadd_abelian_group_op /.
Global Arguments Qzero_abelian_group_id /.
Global Arguments Qopp_abelian_group_opp /.
Global Arguments Qmult_ring_op /.
Global Arguments Qone_ring_id /.

Instance Q_integral_domain : IntegralDomain Q.
Proof. repeat split; repeat intro; cbn in *; nra. Qed.

Instance Q_eq_dec : forall x y : Q, decidable (x ≡ y) := Qeq_dec.

(* Local Open Scope mat_scope. *)
Local Open Scope mat_scope.
Local Coercion inject_Z : Z >-> Q.

Definition M (e q : Z) := [ 0 , 1 / (2 ^ e) ; - 1 / (2 ^ e) , q / (2 ^ (2 * e)) ]%Q.
Definition scaledM (e q : Z) := [ 0 , 2 ^ e ; - (2 ^ e) , inject_Z q ]%Q.

(* Local Notation "a <=? b" := (match a ?= b with Gt => false | _ => true end). *)
(* Local Notation "a <? b" := (match a ?= b with Lt => true | _ => false end). *)
(* Local Notation "a =? b" := (match a ?= b with Eq => true | _ => false end). *)
Notation "a <=? b" := (Qle_bool a b) : Q_scope.

Definition Qlt_bool x y := (Qnum x * Z_as_DT.pos (Qden y) <? Qnum y * Z_as_DT.pos (Qden x))%Z.
Notation "a <? b" := (Qlt_bool a b) : Q_scope.

Notation "a =? b" := (Qeq_bool a b) : Q_scope.
Local Open Scope Q.

Definition has_at_most_norm (P : mat Q) N :=
  let '(a, b, c, d) := P in
  let X := (2 * N ^ 2 - a - d) in
  (0 <=? X) && ((a - d) ^ 2 + 4 * b ^ 2 <=? X ^ 2).

From BY Require Import Tactics Spectral.

Require Import Rbase Reals Qreals micromega.Lra.
Local Coercion Q2R : Q >-> R.

Definition Qmat2Rmat (m : mat Q) : mat R :=
  let '(m11, m12, m21, m22) := m in
  [ Q2R m11, Q2R m12 ; Q2R m21, Q2R m22 ]%M.

Hint Rewrite Q2R_mult Q2R_plus Q2R_minus Q2R_opp RMicromega.Q2R_0 RMicromega.Q2R_1 RMicromega.Q2RpowerRZ : pull_q2r.
Hint Rewrite <- Q2R_mult Q2R_plus Q2R_minus Q2R_opp RMicromega.Q2R_0 RMicromega.Q2R_1 RMicromega.Q2RpowerRZ : push_q2r.

Lemma Qmat2Rmat_mul m1 m2 :
  Qmat2Rmat (mmult m1 m2) = Matrix.mmult (Qmat2Rmat m1) (Qmat2Rmat m2).
Proof.
  destruct m1 as [[[m111 m112] m121] m122].
  destruct m2 as [[[m211 m212] m221] m222].
  cbn.
  auto_mat; autorewrite with pull_q2r; reflexivity. Qed.

Inductive inSQ_gen_scaled {w0 P0 e0} : Z -> mat Q -> Prop :=
| IS_gen_scaled : inSQ_gen_scaled w0 P0
| Sc_gen_scaled (w : Z) (P : mat Q) :
    forall (e : Z) (q : Z),
    inSQ_gen_scaled w P ->
    (0 <? w)%Z && (has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * (betaQ (Z.to_nat w)))) = false ->
    has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) = false ->
    (e0 <= e)%Z ->
    Z.odd q = true ->
    (e0 <= q < 2 ^ (e + 1))%Z ->
    inSQ_gen_scaled (e + w)%Z (mmult (scaledM e q) P).
Local Open Scope lmodule_scope.
Require Import Zpower_nat.


Local Open Scope R.
Lemma has_at_most_norm_spec P N : (0 <= N)%Q -> (has_at_most_norm (mmult (mtrans P) P) N = true <-> mat_norm (Qmat2Rmat P) <= N).
Proof.
  pose (mat_norm_condition (Qmat2Rmat P) N).
  unfold Qmat2Rmat in *.
  split_pairs.
  (* unfold abelian_group_op in *. *)
  (* unfold Impl.Rplus_abelian_group_op in *. *)
  cbn -[Qpower Rpower pow] in *.
  rewrite y.

  split.
  -
    intros. apply andb_prop in H0.
    inversion H0.
    apply Qle_bool_iff in H1.
    apply Qle_bool_iff in H2.
    split.
    rewrite <- RMicromega.Q2R_0. apply Qle_Rle.
    assumption.
    apply Qle_Rle in H1.
    apply Qle_Rle in H2.
    autorewrite with pull_q2r in *.

    replace 2%Z with (Z.of_nat 2) in *.

    rewrite <- !pow_powerRZ in *.

    replace (Z.of_nat 2 # 1) with 2%Q in * by reflexivity.
    split. field_simplify. nra. field_simplify. nra. reflexivity. right. lia. right. lia.
    right. lia. right. lia. right. lia.
  -
    intros.
    apply andb_true_intro.
    rewrite !Qle_bool_iff.
    split_pairs.
    split.
    apply Rle_Qle.
    autorewrite with pull_q2r.
    replace 2%Z with (Z.of_nat 2).
    rewrite <- !pow_powerRZ in *.
    replace (Z.of_nat 2 # 1) with 2%Q in * by reflexivity.
    nra. reflexivity. right. lia.

    apply Rle_Qle.
    autorewrite with pull_q2r.
    replace 2%Z with (Z.of_nat 2).
    rewrite <- !pow_powerRZ in *.
    replace (Z.of_nat 2 # 1) with 2%Q in * by reflexivity.
    nra. reflexivity. right. lia.
    right. lia. right. lia. right. lia.
Qed.

Lemma has_at_most_norm_spec2 P N : (0 <= N)%Q -> (has_at_most_norm (mmult (mtrans P) P) N = false <-> mat_norm (Qmat2Rmat P) > N).
Proof.
  intro.
  pose (has_at_most_norm_spec P N).
  apply not_iff_compat in i.
  destruct i.
  split.
  intros.
  enough (~ mat_norm (Qmat2Rmat P) <= N).
  lra. apply H0. congruence.
  intros. enough (has_at_most_norm (mmult (mtrans P) P) N <> true).
  apply not_true_is_false in H3. assumption.
  apply H1. lra. assumption. Qed.

Arguments Z.of_nat /.

Lemma has_at_most_norm_true_trans P N M : (0 <= N <= M)%Q -> has_at_most_norm (mmult (mtrans P) P) N = true -> has_at_most_norm (mmult (mtrans P) P) M = true.
Proof.
  intro.
  rewrite !has_at_most_norm_spec.
  (* intros. *)
  split_pairs.
  apply Qle_Rle in H.
  apply Qle_Rle in H0. lra.
  split_pairs. unfold Qle in *. nia. easy. Qed.

Lemma has_at_most_norm_false_trans P N M : (0 <= N <= M)%Q -> has_at_most_norm (mmult (mtrans P) P) M = false -> has_at_most_norm (mmult (mtrans P) P) N = false.
  intro.
  rewrite !has_at_most_norm_spec2.
  (* intros. *)
  split_pairs.
  apply Qle_Rle in H.
  apply Qle_Rle in H0. lra.
  split_pairs. unfold Qle in *. nia.
  unfold Qle in *. nia. Qed.

Instance has_at_most_norm_Proper : Proper (eq ==> Qeq ==> eq) has_at_most_norm.
Proof.
  repeat red; intros.
  unfold has_at_most_norm.
  split_pairs.
  setoid_rewrite H0. reflexivity. Qed.


Lemma Q2R_pow x n (H : (n <> 0)%nat) : (Q2R x) ^ n = Q2R (x ^ (Z.of_nat n)).
Proof. rewrite RMicromega.Q2RpowerRZ.
       rewrite pow_powerRZ. reflexivity. right. lia. Qed.

Lemma Q2R_pow' x n (H : (0 <= n)%Z) : (Q2R x) ^ (Z.abs_nat n) = Q2R (x ^ n).
Proof. rewrite RMicromega.Q2RpowerRZ.
       rewrite pow_powerRZ. rewrite Zabs2Nat.id_abs. rewrite Z.abs_eq. reflexivity. assumption. right. lia. Qed.

Lemma Q2R_2 : Q2R 2 = 2.
Proof. lra. Qed.

Lemma alpha_alphaQ w :
  alpha w = Q2R (alphaQ (Z.of_nat w)).
Proof.
  unfold alpha, alphaQ.
  destruct w; try (cbn; lra).
  destruct w; try (cbn; lra).
  repeat (destruct w; [cbn -[Qpower]; rewrite Q2R_div by (apply Qeq_bool_neq; reflexivity); apply f_equal2; [lra|
                                                                                                             rewrite <- ?Q2R_pow', ?Q2R_2 by lia; reflexivity]|]).
  replace (_ <=? 66)%Z with false by (symmetry; apply Z.leb_gt; lia).
  unfold alpha_high.
  unfold alphaQ_high.

  rewrite <- Q2R_pow.
  rewrite Q2R_div.

  replace (Q2R 633) with 633 by lra.
  replace (Q2R 1024) with 1024 by lra. reflexivity. apply Qeq_bool_neq. reflexivity. lia. Qed.

Lemma alpha_alphaQ_nat w :
  alpha w = Q2R (alphaQ_nat w).
Proof.
  rewrite <- alphaQ_alphaQ_nat.
  rewrite alpha_alphaQ.
  reflexivity. Qed.

Hint Rewrite Q2R_div : pull_q2r.
Hint Rewrite <- Q2R_div : push_q2r.

Lemma alpha_quot_alphaQ_quot w i :
  alpha_quot w i = alphaQ_quot w i.
Proof.
  unfold alpha_quot, alphaQ_quot.
  rewrite !alpha_alphaQ_nat.
  autorewrite with push_q2r. reflexivity.
  pose proof alphaQ_nat_pos i.
  intro. symmetry in H0.
  apply Qlt_not_eq in H0. assumption. assumption. Qed.

Lemma Rmin_Qmin a b :
  Rmin (Q2R a) (Q2R b) = Qmin a b.
Proof.
  unfold Rmin.
  destruct (Rle_dec a b).
  rewrite Qminmax.Q.min_l. reflexivity.
  apply Rle_Qle. lra.
  rewrite Qminmax.Q.min_r. reflexivity.
  apply Rle_Qle. lra. Qed.

Lemma Rmin_list_Qmin_list l :
  Rmin_list (map Q2R l) = Qmin_list l.
Proof.
  induction l.
  simpl. lra.
  destruct l.
  reflexivity.
  rewrite map_cons.
  rewrite map_cons.
  rewrite map_cons in IHl.
  rewrite Rmin_list_cons.
  rewrite Qmin_list_cons.
  rewrite IHl.
  rewrite Rmin_Qmin. reflexivity. Qed.

Lemma beta_aux_betaQ_aux w n :
  beta_aux w n = map Q2R (betaQ_aux w n).
Proof.
  unfold beta_aux.
  unfold betaQ_aux.
  generalize 0%nat.
  revert w.
  induction n.
  reflexivity. intros.
  simpl.
  rewrite IHn. rewrite alpha_quot_alphaQ_quot. reflexivity. Qed.

Lemma beta_betaQ w :
  beta w = betaQ w.
Proof.
  unfold betaQ.
  unfold beta.
  rewrite beta_aux_betaQ_aux.
  apply Rmin_list_Qmin_list. Qed.

Lemma betaQ_pos w :
  (0 <= betaQ w)%Q.
Proof.
  apply Rle_Qle.
  rewrite <- beta_betaQ.
  replace (Q2R 0%Q) with 0 by lra.
  apply beta_pos. Qed.

Lemma beta_quot_betaQ_quot w j :
  beta_quot w j = betaQ_quot w j.
Proof.
  unfold beta_quot, betaQ_quot.
  rewrite beta_betaQ.
  rewrite pow_powerRZ.
  autorewrite with pull_q2r.
  replace (Q2R 70%Q) with (IZR 70%Z) by lra.
  replace (Q2R 169%Q) with (IZR 169%Z) by lra.
  replace (Q2R 2%Q) with (IZR 2%Z) by lra. reflexivity.
  lia.

  intro. cbv [Qeq] in *.
  simpl in H. lia. Qed.

Lemma gamma_aux_gammaQ_aux w e n :
  gamma_aux w e n = map Q2R (gammaQ_aux w e n).
Proof.
  unfold gamma_aux, gammaQ_aux.
  revert w e.
  induction n.
  reflexivity.
  intros. simpl.
  rewrite IHn.
  rewrite beta_quot_betaQ_quot. reflexivity. Qed.

Lemma gamma_gammaQ w e :
  gamma w e = gammaQ w e.
Proof.
  unfold gamma, gammaQ.
  rewrite gamma_aux_gammaQ_aux.
  rewrite Rmin_list_Qmin_list. reflexivity. Qed.

Lemma gammaQ_pos w e :
  (0 <= gammaQ w e)%Q.
Proof.
  apply Rle_Qle.
  replace (Q2R 0%Q) with (IZR 0).
  rewrite <- gamma_gammaQ.
  apply gamma_pos. lra. Qed.

Lemma inSQ_gen_scaled_spec w P :
  inS w P -> exists PQ, Qmat2Rmat PQ = (4 ^ w)%R ⋅ P /\ @inSQ_gen_scaled 0%Z I 1%Z (Z.of_nat w) PQ.
Proof.
  intros.
  induction H; intros.
  - exists I. split.
    + unfold I, Matrix.I. cbn.
      repeat (apply f_equal2; try nra).
    + constructor.
  - destruct IHinS as [PQ [IH1 IH2]].
    exists (mmult (scaledM (Z.of_nat e) q) PQ).
    split.
    + rewrite Qmat2Rmat_mul.
      rewrite IH1.
      destruct P as [[[P11 P12] P21] P22].
      cbn -[Z.of_nat].
      repeat (match goal with
              | [ |- (_, _) = (_, _) ] => apply f_equal2
              end).
      * autorewrite with pull_q2r. rewrite !Rmult_0_l, !Rplus_0_l.
        rewrite <- pow_powerRZ. replace (Q2R 2)%Q with 2%R by lra.
        rewrite !pow_add. replace 4%R with (2 * 2)%R by reflexivity.
        rewrite !Rpow_mult_distr. field.
        apply pow_nonzero. lra. left. cbv. lia.
      * autorewrite with pull_q2r. rewrite !Rmult_0_l, !Rplus_0_l.
        rewrite <- pow_powerRZ. replace (Q2R 2)%Q with 2%R by lra.
        rewrite !pow_add. replace 4%R with (2 * 2)%R by reflexivity.
        rewrite !Rpow_mult_distr. field.
        apply pow_nonzero. lra. left. cbv. lia.
      * autorewrite with pull_q2r.
        rewrite <- pow_powerRZ. replace (Q2R 2)%Q with 2%R by lra.
        replace (Q2R (inject_Z q)) with (IZR q).
        rewrite !pow_add. replace 4%R with (2 * 2)%R by reflexivity.
        rewrite !Rpow_mult_distr. field.
        apply pow_nonzero. lra. unfold Q2R. simpl. lra. left. cbv. lia.
      * autorewrite with pull_q2r.
        rewrite <- pow_powerRZ. replace (Q2R 2)%Q with 2%R by lra.
        replace (Q2R (inject_Z q)) with (IZR q).
        rewrite !pow_add. replace 4%R with (2 * 2)%R by reflexivity.
        rewrite !Rpow_mult_distr. field.
        apply pow_nonzero. lra. unfold Q2R. simpl. lra. left. cbv. lia.
    + rewrite Nat2Z.inj_add. constructor. assumption.
      apply negb_true_iff.
      rewrite negb_andb.
      apply orb_true_intro.
      destruct H0.
      * left.
        apply negb_true_iff. apply Z.ltb_ge.
        lia.
      * right.
        apply negb_true_iff.
        apply has_at_most_norm_spec2.
        apply Qmult_le_0_compat. apply Qpower_pos. cbv. congruence.
        apply betaQ_pos.
        rewrite IH1.
        rewrite mat_norm_scmat.
        autorewrite with pull_q2r.
        rewrite <- pow_powerRZ.
        rewrite <- RPow_abs.
        rewrite Rabs_pos_eq by lra.
        replace (Q2R 4%Q) with 4 by lra.
        rewrite Nat2Z.id. rewrite <- beta_betaQ.
        apply Rmult_gt_compat_l.
        apply Rgt_lt.
        apply pow_lt. lra. assumption. left. cbv. congruence.
      *
        apply has_at_most_norm_spec2.
        apply Qmult_le_0_compat. apply Qpower_pos. cbv. congruence.
        apply gammaQ_pos.
        rewrite IH1.
        rewrite mat_norm_scmat.
        autorewrite with pull_q2r.
        rewrite <- pow_powerRZ.
        rewrite <- RPow_abs.
        rewrite Rabs_pos_eq by lra.
        replace (Q2R 4%Q) with 4 by lra.
        rewrite !Nat2Z.id. rewrite <- gamma_gammaQ.
        apply Rmult_gt_compat_l.
        apply Rgt_lt.
        apply pow_lt. lra. assumption. left. cbv. congruence.
      * lia.
      * assumption.
      *
        rewrite Zpower_nat_Z in H4. lia. Qed.

Local Open Scope R.

Ltac qia := unfold Qeq in *; simpl in *; nia.
Ltac qia_goal := unfold Qeq; simpl; nia.

Lemma Qinv_zero (a : Q) : a == 0 <-> / a == 0.
Proof.
  intros. unfold Qeq in *. simpl in *. unfold Qinv.
  destruct (Qnum a). simpl in *. nia. simpl in *. lia. simpl in *. lia. Qed.

Lemma Qpower_nonzero (a : Q) (b : Z) : ~ (a == 0) -> ~ (a ^ b == 0).
Proof.
  intros.
  intros contra.

  destruct b. qia.
  induction p; qia.
  induction p; simpl in *.
  apply Qinv_zero in contra.
  apply IHp.
  apply -> Qinv_zero. qia.

  apply Qinv_zero in contra.
  apply IHp.
  apply -> Qinv_zero. qia.

  apply H. apply Qinv_zero. assumption. Qed.

Lemma alpha31 i : (31 <= i < 67)%nat -> ((alpha i) ^ 49 < 1 / (2 ^ ((34 * i - 23)))).
Proof.
  intros.
  rewrite alpha_alphaQ.
  rewrite Q2R_pow.
  replace (Z.of_nat 49) with 49%Z by lia.
  replace 1 with (Q2R 1).
  replace 2 with (Q2R 2).
  rewrite Q2R_pow.
  rewrite <- Q2R_div.
  replace (Z.of_nat (34 * i - 23)) with (34 * (Z.of_nat i) - 23)%Z.
  apply Qlt_Rlt.
  apply alphaQ31. lia.
  lia. apply Qpower_nonzero.
  apply Qeq_bool_neq. reflexivity. lia. lra. lra. lia. Qed.
