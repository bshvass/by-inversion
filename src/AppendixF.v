Require Import ZArith.
Require Import List Bool Znumtheory Decidable.
Require Import Rbase Reals QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

From BY Require Import Q Rlemmas Rmin_list AppendixFdefs Tactics Matrix AppendixE IZR Zpower_nat Zlemmas Hierarchy Impl Spectral PadicVal Log InductionPrinciples ListLemmas NoMemNew.

Local Open Scope R_scope.

Local Open Scope vec_scope.
Local Open Scope mat_scope.
Local Open Scope ring_scope.
Local Open Scope lmodule_scope.

(* Instance Rinv_RingInv2 : RingInv2 R := Rinv. *)

Local Coercion INR : nat >-> R.
(* Local Coercion IZR : Z >-> R. *)
Local Coercion Q2R : Q >-> R.

(********************************************************************************************************)
(** This file follows AppendixF in the Bernstein Yang paper.                                            *)
(** The file contains a lot of things including some very messy proofs.                                 *)
(** First we define the M matrices and prove some prelimenary results on these and on general matrices. *)
(********************************************************************************************************)

Lemma F6 (v1 v2 : Z) :
  ( IZR v1 , IZR v2 ) ≢ v0 -> 1 <= vec_norm ( IZR v1 , IZR v2 ).
Proof.
  intros vnon0. apply vnonzero in vnon0.
  unfold vec_norm. rewrite <- Rabs_pos_eq by apply sqrt_pos.
  apply (le_pow 2). lia. field_simplify.
  replace 0 with (IZR 0)in vnon0.
  destruct vnon0 as [H|H]; apply neq_IZR in H; apply pow2_IZR in H; rewrite pow2_sqrt; nra. reflexivity.
Qed.

Definition F12 := mat_norm_condition.

Theorem F16 e q (qodd : Z.odd q = true) (qbound : 1 <= q <= 2 ^ (S e) - 1) :
  mat_norm (M e q) < (1 + sqrt 2) / (2 ^ e).
Proof.
  assert (q < 2 * 2 ^ e).
  { rewrite <- tech_pow_Rmult in qbound; lra. }
  assert (2 ^ e <> 0) by (apply pow_nonzero; lra).
  unfold mat_norm; rify; simpl.
  rewrite !Rmult_0_l, !Rplus_0_l, !Rmult_1_r, Nat.add_0_r.
  replace (e + e)%nat with (2 * e)%nat by ring.
  rewrite !mult_pow2. rewrite Rpow_mult_distr, !pow_div, pow1, <- !pow_mult; try (apply pow_nonzero; lra).
  replace ((-1) ^ 2) with R1 by lra.
  replace (2 * e * 2)%nat with (e * 4)%nat by ring.
  field_simplify (1 / 2 ^ (e * 2) * (q ^ 2 / 2 ^ (e * 4)))%R; [|split; apply pow_nonzero; lra].

  assert (q ^ 2 < 4 * 2 ^ (e * 2)).
  { replace (4 * 2 ^ (e * 2))%R with ((2 * 2 ^ e) ^ 2)%R.
    apply pow_maj_Rabs_lt. lia.
    rewrite Rabs_pos_eq. lra. lra.
    rewrite pow_mult, Rpow_mult_distr. lra. }

  assert (q ^ 2 / (2 ^ (e * 4)) < 4 / 2 ^ (e * 2)).
  { replace (Rdiv 4 (2 ^ (e * 2))) with (Rdiv (4 * 2 ^ (e * 2)) (2 ^ (e * 4))).
    unfold Rdiv.
    apply Rmult_lt_compat_r.
    apply Rinv_pos_nonneg. apply pow_lt. lra. assumption.

    replace (Rdiv (4 * 2 ^ (e * 2)) (2 ^ (e * 4))) with (4 * (Rdiv (2 ^ (e * 2)) (2 ^ (e * 4))))%R by (field; try apply pow_nonzero; lra).
    rewrite div_pow_inv.
    replace (e * 4 - e * 2)%nat with (e * 2)%nat by lia. field. apply pow_nonzero; lra. lra. nia. }

  rewrite minus_add_distr, minus_diag, Rminus_0_l.

  assert ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 < (4 / 2 ^ (e * 2)) ^ 2).
  { apply pow_maj_Rabs_lt. lia. rewrite Rabs_Ropp.
    rewrite Rabs_pos_eq. lra. apply Rle_div_r.
    apply pow_lt. lra. rewrite Rmult_0_r. apply pow_le. lra. }

  assert (4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))) <= 16 / 2 ^ (e * 4)).
  { unfold Rdiv. rewrite inv_mul. rewrite (Rmult_comm (/ _)). rewrite <- (Rmult_assoc (q ^ 2)).
  unfold Rdiv.

  transitivity (4 * ((4 / 2 ^ (e * 2)) * / 2 ^ (e * 2)))%R. nra.
  field_simplify. rewrite <- pow_mult.
  replace (e * 2 * 2)%nat with (e * 4)%nat by lia. lra.
  apply pow_nonzero; lra.
  apply pow_nonzero; lra.
  apply pow_nonzero; lra.
  apply pow_nonzero; lra. }

  assert ((4 / 2 ^ (e * 2)) ^ 2 = Rdiv 16 (2 ^ (e * 4))).
  { field_simplify. rewrite <- pow_mult.
    replace (e * 2 * 2)%nat with (e * 4)%nat by lia. lra.
    apply pow_nonzero; lra.
    apply pow_nonzero; lra. }

  assert (((4 / 2 ^ (e * 2)) ^ 2) + 16 / 2 ^ (e * 4) = Rdiv 32 (2 ^ (e * 4)))%R by nra.

  assert (sqrt
    ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + q ^ 2 / 2 ^ (e * 4)) +
              sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))))) / 2) <
  sqrt
    ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
              sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))))) / 2)).
  { apply sqrt_lt_1_alt. split.
    apply div_pos_pos.
    repeat apply add_pos; try apply div_pos_pos; try apply pow_lt; try apply pow_le; try lra.
    apply sqrt_positivity.
    apply add_pos. apply pow2_ge_0.
    repeat apply mul_pos; try lra.
    try apply div_pos; try apply pow_lt; try apply pow_le; try lra.
    apply inv_pos. rewrite <- pow_add. apply pow_le. lra. lra. lra. }
  apply (Rlt_le_trans _ _ _ H7).

  assert
  (sqrt
    ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
              sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))))) / 2) <=
    sqrt
    ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
             sqrt (32 / 2 ^ (e * 4))) / 2)).

  { apply sqrt_le_1_alt. apply Rle_div_r. lra.
    replace (2 *
             ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
                       sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))))) / 2))%R with
        ((1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)) +
                  sqrt ((- (q ^ 2 / 2 ^ (e * 4))) ^ 2 + 4 * (q ^ 2 / (2 ^ (e * 2) * 2 ^ (e * 4))))))%R by lra.
    apply Rplus_le_compat_l.
    apply sqrt_le_1_alt. lra. }

  apply (Rle_trans _ _ _ H8).
  replace (1 / 2 ^ (e * 2) + (1 / 2 ^ (e * 2) + 4 / 2 ^ (e * 2)))%R
    with (Rdiv 6 (2 ^ (e * 2))) by lra.

  right.
  apply sqr_inj. apply sqrt_positivity. apply div_pos_pos. apply add_pos. apply div_pos_pos. lra.
  apply pow_le. lra. apply sqrt_positivity. apply div_pos_pos. lra. apply pow_le. lra. lra.
  apply div_pos_pos. apply add_pos. lra. apply sqrt_positivity. lra. apply pow_le. lra.
  rewrite pow2_sqrt.

  apply eq_div. lra. rewrite sqrt_div.
  rewrite <- (Rpower_sqrt (2 ^ _)).
  rewrite <- (Rpower_pow (_ * 4) _).
  rewrite Rpower_mult.
  replace ((e * 4)%nat * / 2)%R with (INR (e * 2))%R.
  rewrite Rpower_pow.
  rewrite sqrt32.
  rewrite pow_div. rewrite <- pow_mult.
  rewrite <- Rdiv_plus_distr.
  replace ((1 + sqrt 2) ^ 2 / 2 ^ (e * 2) * 2)%R with
      (Rdiv (2 * (1 + sqrt 2) ^ 2) (2 ^ (e * 2)))%R.
  apply f_equal2. field_simplify. rewrite pow2_sqrt. field. lra. reflexivity.
  field. apply pow_nonzero. lra. apply pow_nonzero. lra. lra.

  rewrite !mult_INR. simpl. lra. lra. apply pow_lt. lra. lra. apply pow_lt. lra.
  apply div_pos_pos. apply add_pos. apply div_pos_pos. lra. apply pow_le. lra. apply sqrt_positivity. apply div_pos_pos.
  lra. apply pow_le. lra. lra. Qed.

Local Instance Nat_monoid : Monoid nat.
Proof. split; exact _. Qed.

Lemma fin_dec k (P : nat -> Prop) (Pdec : forall i, { P i } + { ~ P i }) :
   { exists j, (j <= k)%nat /\ P j } + { forall i, (i <= k)%nat -> ~ P i }.
Proof.
  induction k.
  - destruct (Pdec 0%nat). left.
    exists 0%nat. split. lia. assumption.
    right. intros.
    assert (i = 0%nat). lia. subst. assumption.
  - destruct IHk.
    + left. destruct e. exists x. split. lia. tauto.
    + destruct (Pdec (S k)%nat).
      * left. exists (S k). split. lia. assumption.
      * right. intros. destruct (Nat.eq_dec i (S k)); [subst; assumption|].
        apply n. lia. Qed.

Theorem F21 : (forall w P, inS w P -> mat_norm P <= alpha w) ->
              forall (j : nat)
                (e : nat -> nat)
                (He : forall i, (i < j)%nat -> (1 <= e i)%nat)
                (q : nat -> Z)
                (Hq : forall i, (i < j)%nat -> (Z.odd (q i) = true) /\ (1 <= q i < 2 ^+ (S (e i)))%Z),
                mat_norm (big_mmult_rev (fun i => M (e i) (q i)) 0 j) <= alpha (big_sum_nat e 0 j).
Proof.
  intros.
  revert Hq He. revert e q.
  induction j using strong_induction; intros.
  destruct j.
  - rewrite big_op_nil, big_op_rev_nil by lia; simpl.
    rewrite !Rmult_1_r, !Rmult_0_r, !Rplus_0_r, !Rplus_0_l, !minus_diag, !Rmult_0_r, Rplus_0_r.
    rewrite sqrt_0. rewrite <- sqrt_1 at 1. Search Rle. apply sqrt_le_1_alt. rify. lra.
  - destruct (fin_dec j
                      (fun i => (mat_norm (big_mmult_rev (fun i => M (e i) (q i)) 0 (S i))) <= (beta ((big_sum_nat e 0 (S i)))))
                      ltac:(intros; apply Rle_dec)) as [[i[]]|].
    + assert (mat_norm (big_mmult_rev (fun l => M (e ((S i) + l)%nat) (q ((S i) + l)%nat)) 0 (j - i)) <= alpha (big_sum_nat (fun l => e ((S i) + l)%nat) 0 (j - i))).
      { apply H0. lia. intros. apply Hq. lia. intros. apply He. lia. }

      assert (mat_norm (big_mmult_rev (fun i => M (e i) (q i)) 0 (S j)) <= (beta (big_sum_nat e 0 (S i))) * alpha (big_sum_nat e (S i) (S j))).
      {
        setoid_rewrite <- big_op_rev_split with (m:=S i); [|lia].
        eapply Rle_trans.
        apply mat_norm_mmult.

        pose proof mat_norm_nonneg (big_mmult_rev (fun i => M (e i) (q i)) (S i) (S j)).
        pose proof mat_norm_nonneg (big_mmult_rev (fun i => M (e i) (q i)) 0 (S i)).

        pose proof beta_pos (big_sum_nat e 0 i).
        pose proof alpha_pos (big_sum_nat e i j).

        rewrite big_op_rev_shift with (g:=fun i => M (e i) (q i)) (k:= S i) in H3.
        rewrite big_op_shift with (g:=e) (k:= S i) in H3.

        rewrite Nat.add_0_l in H3.
        replace (j - i + S i)%nat with (S j) in H3 by lia. nra.
        intros.
        apply f_equal; lia.
        intros.
        apply f_equal2; apply f_equal; lia.
      }
      etransitivity.

      apply H4. rewrite Rmult_comm. apply Rle_div_r. apply alpha_pos_nonneg.
      rewrite <- (big_op_split _ _ (S i) (S j)).
      apply beta_spec. lia.
    + destruct (fin_dec j
                        (fun i => (mat_norm (big_mmult_rev (fun i => M (e i) (q i)) 0 i)) <= (gamma (big_sum_nat e 0 i) (e i)))
                        ltac:(intros; apply Rle_dec)) as [[i[]]|].

      * epose proof F16 (e i) (q i) _ _.

        assert (mat_norm (big_mmult_rev (fun i0 : nat => M (e i0) (q i0)) 0 (S i)) <= beta (big_sum_nat e 0 (S i))).
        {
          rewrite <- big_op_rev_split with (m:=i) by lia.
          etransitivity. apply mat_norm_mmult.

          rewrite big_op_rev_S_r, big_op_rev_nil by lia.
          rewrite (left_id mon_id mag_op).

          pose proof sqrt2_bound.
          pose proof gamma_spec (big_sum_nat e 0 i) (e i).
          (* replace Nat.add with monoid_op in H5 by reflexivity. *)
          rewrite <- big_op_S_r in H5. by lia.
          (* replace Natadd_monoid_op with Nat.add in H5 by reflexivity. *)
          (* replace monoid_op with Nat.add in H5 by reflexivity. *)

          pose proof sqrt_pos 2.
          pose proof mat_norm_nonneg (M (e i) (q i)).
          pose proof mat_norm_nonneg (big_mmult_rev (fun i0 : nat => M (e i0) (q i0)) 0 i).

          pose proof gamma_pos (big_sum_nat e 0 i) (e i).
          pose proof beta_pos (big_sum_nat e 0 (S i)).

          pose proof pow_le 2 (e i) ltac:(lra).

          apply Rle_div_r in H5.
          apply Rlt_div_r in H4.
          apply Rlt_div_r in H3. nra. apply pow_lt. all: try lra; try lia.
        }
        specialize (n i ltac:(lia)); lra.
      * assert (forall i, (i <= (S j))%nat -> inS (big_sum_nat e 0 i) (big_mmult_rev (fun i0 : nat => M (e i0) (q i0)) 0 i)).
        {
          induction i.
          { intros. rewrite big_op_nil, big_op_rev_nil by lia. constructor. }
          { intros. specialize (IHi ltac:(lia)).
            rewrite <- big_op_split with (m:=i) by lia.
            rewrite <- big_op_rev_split with (m:=i) by lia.
            rewrite big_op_rev_S_l, big_op_rev_nil, mul_1_r by lia.
            rewrite big_op_S_r, (big_op_nil _ i i), Nat.add_0_l by lia.
            rewrite Nat.add_comm.
            constructor.
            assumption.
            destruct i.
            { left. rewrite big_op_nil. reflexivity. lia. }
            { right. specialize (n i ltac:(lia)). lra. }
            { specialize (n0 i ltac:(lia)). lra. }

            apply He. lia. apply Hq. lia. apply Hq. lia.
          }
        }
        apply H. apply H1. lia.
        Unshelve. apply Hq. lia. split. apply IZR_le. apply Hq. lia.
        autorewrite with pull_izr.
        apply IZR_le. specialize (Hq i ltac:(lia)). lia. Qed.

(******************************************************************************)
(** The following theorem is computational and too heavy to carry out in coq. *)
(** See Bernstein and Yangs paper.                                            *)
(** Note that the defined set is finite                                       *)
(******************************************************************************)

Theorem F22 : (forall w P, inS w P -> mat_norm P <= alpha w).
Proof.
  intros.
  apply inSQ_gen_scaled_spec in H.
  destruct H as [PQ [H1 H2]].
  apply F22_Q in H2.
  rewrite Nat2Z.id in H2.
  apply has_at_most_norm_spec in H2.
  rewrite H1 in H2.
  rewrite mat_norm_scmat in H2. rify_in H2.
  autorewrite with pull_q2r in H2.
  rewrite <- alpha_alphaQ_nat in H2.
  pose proof alpha_pos w.
  pose proof mat_norm_nonneg P.
  replace (Q2R 4%Q) with (IZR 4) in H2 by lra.
  assert (Rabs (4 ^ w) = powerRZ 4 (Z.of_nat w)).
  rewrite <- pow_powerRZ.
  rewrite <- RPow_abs.
  rewrite Rabs_pos_eq by lra. reflexivity.
  rewrite H3 in H2.
  assert (0 < powerRZ 4 (Z.of_nat w)) by (apply powerRZ_lt; lra). nra. left. cbv. lia.
  assert (0 <= 4 ^ (Z.of_nat w))%Q.
  apply Qpower.Qpower_pos. cbv. congruence.
  pose proof alphaQ_nat_nonneg w.
  apply Qmult_le_0_compat. assumption. assumption. Qed.

Theorem F24 (j : nat) (e : nat -> nat) (q : nat -> Z) (He : forall i, (i < j)%nat -> (1 <= e i)%nat) (Hq : forall i, (i < j)%nat -> (Z.odd (q i) = true) /\ (1 <= q i < 2 ^+ (S (e i)))%Z) :
  mat_norm (big_mmult_rev (fun i => M (e i) (q i)) 0 j) <= alpha (big_sum_nat e 0 j).
Proof. apply F21. apply F22. assumption. assumption. Qed.

(*********************************************************************************************)
(** The following section wraps the previous theorems together in the termination theorem of *)
(** of the gcd algorithm.                                                                    *)
(*********************************************************************************************)

Section __.
  Context (R0 R1 : Z)
          {R0_odd : Z.odd R0 = true}
          {R1_even : Z.even R1 = true}.

  Notation R_ := (R_ R0 R1).

  Notation e i := (ord2 (R_ (S i))).
  Notation q i := (q (split2 (R_ i)) (R_ (S i))).
  Definition M_ i := M (e i) (q i).

  Lemma E2_cor i (HR0 : R0 <> 0%Z) (H : R_ (S i) <> 0%Z) :
    [ IZR (split2 (R_ (S i))) ; IZR (R_ (S (S i))) ] =
    M (e i) (q i) ⋅ [ IZR (split2 (R_ i)) ; IZR (R_ (S i))].
  Proof.
    unfold M. rewrite E2. cbv [module_left_act vmult_left_act vmult]. apply f_equal2. rify. lra.
    apply f_equal2. reflexivity. apply f_equal2.
    unfold div_2. field_simplify. apply f_equal2. reflexivity.
    rewrite Zpower_nat_IZR. rewrite <- pow_add. apply f_equal2. lra. lia. apply pow_nonzero. lra.
    split. apply IZR_neq. apply Zpower_nat_nonzero. lia. apply pow_nonzero. lra. reflexivity.  assumption. assumption. Qed.

  Lemma E2_cor2 j (H : R_ j <> 0%Z) :
    [ IZR (split2 (R_ j)) ; IZR (R_ (S j)) ] =
    (big_mmult_rev (fun i => M (e i) (q i)) 0 j) ⋅ [ IZR R0 ; IZR R1].
  Proof.
    assert (R0_nonzero : R0 <> 0%Z) by (apply odd_nonzero; assumption).
    induction j.
    - cbv [module_left_act vmult_left_act vmult]. simpl. apply f_equal2.
      rewrite split2_odd. rify. field. assumption.
      rify. field.
    - rewrite big_op_rev_S_l.
      rewrite left_action.
      rewrite <- IHj.
      rewrite E2_cor. reflexivity.
      assumption. assumption. apply R_nonzero_S. assumption. assumption. lia. Qed.

  Ltac assert_norm :=
    repeat match goal with
           | [ |- context[mat_norm ?a] ] => match goal with
                                          | [ _ : 0 <= mat_norm a |- _ ] => fail 1
                                          | [ |- _ ] =>
                                            assert (0 <= mat_norm a) by (apply mat_norm_nonneg)
                                          end
           | [ |- context[vec_norm ?a] ] => match goal with
                                          | [ _ : 0 <= vec_norm a |- _ ] => fail 1
                                          | [ |- _ ] =>
                                            assert (0 <= vec_norm a) by (apply vec_norm_nonneg)
                                          end
           end.

  Theorem F25 j (H : R_ j <> 0%Z) :
    vec_norm [ IZR (split2 (R_ j)) ; IZR (R_ (S j)) ] <=
    (alpha (big_sum_nat (fun i => e i) 0 j)) * vec_norm [ IZR R0 ; IZR R1 ].
  Proof.
    assert (R0_nonzero : (R0 <> 0)%Z) by (apply odd_nonzero; assumption).

    rewrite E2_cor2. rewrite mat_norm_vmult.
    epose proof F24 j (fun i => e i) (fun i => q i) _ _.
    assert_norm. nra. assumption.

    Unshelve. intros.
    apply e_ge_1; assumption.
    split; apply q_spec;
    try apply odd_split2;
    apply (R_nonzero _ _ j); try assumption; lia. Qed.


  Notation log_1024_633 := (log (1024 / 633)).

  Theorem F25_cor j (H : R_ j <> 0%Z)
    : (67 <= big_sum_nat (fun i => e i) 0 j)%nat -> big_sum_nat (fun i => e i) 0 j <= log_1024_633 (vec_norm [ IZR R0 ; IZR R1 ]).
  Proof.
    intros ineq; pose proof F25 j H as F25'.
    rewrite alpha67 in F25' by assumption. unfold alpha_high in F25'.

    assert (1 <= vec_norm [ IZR (split2 (R_ j)) ; IZR (R_ (S j))]).
    apply F6. apply vnonzero. left. apply not_0_IZR. apply psplit_non0; lia.
    pose proof Rle_trans _ _ _ H0 F25'.
    assert (0 < 1 <= ((633 / 1024) ^ (big_sum_nat (fun i : nat => e i) 0 j)) * vec_norm (IZR R0, IZR R1)). lra.
    assert (1 <= 1024/633). nra.
    eapply (log_inc _ _ _ H3) in H2.

    rewrite log_1, log_mult, log_pow in H2; try lra.
    replace (633 / 1024) with (/ (1024 / 633)) in H2 by lra.
    rewrite log_inv, log_n_n in H2 by lra. nra.
    apply pow_lt. lra.

    assert ((IZR R0 , IZR R1) <> v0).
    apply vnonzero. left. apply not_0_IZR.  apply odd_nonzero. assumption.
    apply vnonzero_norm in H4.
    pose proof (vec_norm_nonneg (IZR R0, IZR R1)). rify_all. lra. Qed.

  Lemma IZR_INR_le z n : (Z.to_nat z <= n)%nat -> IZR z <= INR n.
  Proof. intros. rewrite INR_IZR_INZ. apply IZR_le. lia. Qed.

  Theorem F26 j
          (Hj : (max 67 (Z.to_nat (up (log_1024_633 (vec_norm (IZR R0, IZR R1))))) <= j)%nat) :
    (R_ j) = 0%Z.
  Proof.
    destruct (Z.eq_dec (R_ j) 0%Z).
    assumption.

    pose proof F25_cor _ n.

    assert (j <= big_sum_nat (fun i => e i) 0 j)%nat.
    apply big_sum_bound.
    intros. apply e_ge_1. apply odd_nonzero. assumption. assumption.
    assert (67 <= big_sum_nat (fun i => e i) 0 j)%nat. lia.

    apply H in H1.

    assert (log_1024_633 (vec_norm (IZR R0, IZR R1)) < j).
    eapply Rlt_le_trans.
    apply archimed. apply IZR_INR_le.
    etransitivity. shelve. apply Hj.
    apply le_INR in H0. lra.
    Unshelve. apply Max.le_max_r. Qed.

  Theorem F26_cor :
    exists j, (R_ j) = 0%Z.
  Proof. exists (S (max 67 (Z.to_nat (up (log_1024_633 (vec_norm (IZR R0, IZR R1))))))); apply F26; auto. Qed.

  Theorem F26_cor2 :
    exists j, R_ j <> 0%Z /\ R_ (S j) = 0%Z.
  Proof. apply min. apply odd_nonzero; assumption. apply F26_cor; assumption. Qed.
End __.

Notation log_1024_633 := (log (1024 / 633)).
