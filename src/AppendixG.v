Require Import ZArith.
Require Import List Bool Znumtheory Decidable.
Require Import Rbase Reals QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

From BY Require Import AppendixE AppendixF Divstep Zpower_nat Zlemmas BigOp PadicVal Matrix Rlemmas IZR Log Floor Q.

Import Z.
Local Open Scope Z.

Local Coercion of_nat : nat >-> Z.

(******************************************************************)
(** This files relates the gcd algorithm with iterating divsteps. *)
(** Note that it contains one admitted computational lemma.       *)
(******************************************************************)

Section __.
  Context {f g : Z}
          {f_odd : odd f = true}
          {g_even : even g = true}
          {g_non0 : g <> 0}.

  Notation e := (ord2 g).

  Local Fixpoint z i :=
    match i with
    | 0%nat => (split2 g - f) / 2
    | S i => (z i + (z i mod 2) * split2 g) / 2
    end.

  Notation sum j := (1 + big_sum (fun i => 2 * 2 ^+ i * (z i mod 2)) 0%nat j).

  Lemma z_eq j :
    z j = (sum j * split2 g - f) / 2 ^+ (S j).
  Proof.
    induction j; intros.
    - rewrite big_op_nil by lia; simpl.
      apply f_equal2; ring.
    - simpl.
      rewrite big_op_S_r.
      rewrite IHj at 1.
      rewrite (mul_comm 2 (_ * _)). rewrite <- Zdiv_Zdiv.
      replace ((1 + (big_sum _ _ _ + 2 * 2 ^+ j * (z j mod 2))) * split2 g - f) with
          ((1 + big_sum (fun i => 2 * 2 ^+ i * (z i mod 2)) 0%nat j%nat) * split2 g - f + (z j mod 2) * split2 g * (2 * 2 ^+ j))
        by ring.
      rewrite Z.div_add.
      reflexivity.
      rewrite Zpower_nat_mul_l. apply Zpower_nat_nonzero. lia.
      rewrite Zpower_nat_mul_l. apply Zpower_nat_nonneg. lia.
      lia. lia. Qed.

  Lemma divstep_lemma1 i j (i_bound : (1 <= i)%nat) (sum_bound : (1 <= j + i < S e)%nat) :
    divstep_iter i f (g / 2 ^+ i) j = (j + i, f, g / 2 ^+ (j + i)).
  Proof.
    induction j; intros.
    - simpl. reflexivity.
    - simpl.
      rewrite IHj. unfold divstep.
      assert (0 <? j + i = true). apply Z.ltb_lt. lia.
      assert (odd (g / 2 ^+ (j + i)) = false). apply negb_true_iff. rewrite negb_odd.

      apply even_divide. transitivity (2 ^+ (ord2 g - (j + i))). apply Zpower_nat_base_divide. lia.
      apply divide_lemma. apply Zpower_nat_pos_nonneg. lia.
      transitivity (2 ^+ (ord2 g)). apply Zpower_nat_divide. lia. apply pval_spec. apply g_non0. lia.
      rewrite <- Zpower_nat_is_exp. replace ((j + i) + (ord2 g - (j + i)))%nat with (ord2 g) by lia.
      apply pval_spec. apply g_non0. lia.

      rewrite Zmod_even. rewrite <- negb_odd.

      rewrite H, H0. simpl. apply f_equal2; [apply f_equal2|]. lia. lia.

      rewrite mul_0_l, add_0_r, Zdiv_Zdiv. apply f_equal. ring.
      apply Zpower_nat_nonneg; lia. lia. lia. Qed.

  Lemma divstep_lemma2 i j (j_bound : (0 <= j + i < S e)%nat) :
    divstep_iter (1 - e + i) (split2 g) (z i) j = (j + 1 - e + i, split2 g, z (j + i)).
  Proof.
    induction j.
    - reflexivity.
    - simpl; rewrite IHj; unfold divstep.
      assert (0 <? j + 1 - e + i = false). apply Z.ltb_ge. lia.
      rewrite H. simpl. apply f_equal2; [apply f_equal2|]; lia. lia. Qed.

  Lemma divstep_lemma3 :
    divstep e f (split2 g) = (1 - e, split2 g, z 0).
  Proof.
    unfold divstep.
    assert (0 <? e = true) by
        (rewrite <- Nat2Z.inj_0; apply Z.ltb_lt; apply inj_lt; apply ord2_even; apply g_even).
    rewrite H, odd_split2; auto. Qed.

  Lemma z_div j :
    2 ^+ (S j) * z j  = sum j * split2 g - f.
  Proof.
    induction j; intros.
    - rewrite big_op_nil by lia; simpl.
      rewrite mul_1_r, <- Z_div_exact_2. ring. lia.
      rewrite Zmod_even, even_sub, <- !negb_odd.
      rewrite odd_split2, f_odd; auto.
    - simpl.
      replace (2 * (2 * 2 ^+ j) * ((z j + z j mod 2 * split2 g) / 2)) with
          (((2 ^+ S j) * z j) + (2 * 2 ^+ j) * (z j mod 2 * split2 g)).
      rewrite IHj.
      rewrite big_op_S_r. lia. lia.

      rewrite (mul_comm 2 (2 * _)).
      rewrite <- (mul_assoc _ 2).
      rewrite <- Z_div_exact_2. simpl. ring. lia.
      destruct (mod2_dec (z j)).
      + rewrite e, mul_0_l, add_0_r; auto.
      + rewrite <- Zplus_mod_idemp_l. rewrite e. rewrite mul_1_l.
        apply mod_divide. lia. apply even_divide. rewrite even_add.
        rewrite <- (negb_odd (split2 _)). rewrite odd_split2; auto. Qed.

  Lemma sum_odd j :
    odd (sum j) = true.
  Proof.
    induction j.
    - reflexivity.
    - rewrite big_op_S_r, add_assoc, odd_add, IHj, !odd_mul; try reflexivity; lia. Qed.

  Lemma sum_bound j :
    1 <= sum j < 2 ^+ (S j).
  Proof.
    induction j.
    - rewrite big_op_nil; simpl; lia.
    - rewrite big_op_S_r. pose proof mod_pos_bound (z j) 2 ltac:(lia).
      rewrite <- Zpower_nat_mul_l. rewrite add_assoc.
      assert (2 * 2 ^+ j = 2 ^+ (S j)) by reflexivity. nia. lia. Qed.

  Notation q' := (1 + big_sum (fun i => 2 * 2 ^+ i * (z i mod 2)) 0%nat e).

  Lemma q'_div :
    (2 ^+ (S e) | q' * split2 g - f).
  Proof. eexists. symmetry. rewrite mul_comm. apply z_div. Qed.

  Lemma q'_odd :
    odd q' = true.
  Proof. apply sum_odd. Qed.

  Lemma q'_bound :
    1 <= q' < 2 ^+ (S e).
  Proof. apply sum_bound. Qed.

  Lemma q'q : q' = q f g.
  Proof. apply q_unique. apply f_odd. apply g_non0.
         split; [|split]. apply q'_odd. apply q'_bound. apply q'_div. Qed.

  Theorem G1 :
    divstep_iter 1%nat f (g / 2) (2 * e) = (1 , split2 g , (- (f mod2 g)) / 2 ^+ S e).
  Proof.
    unfold mod_2.
    assert (0 < e)%nat. apply ord2_even. apply g_even.
    replace (- (f - q f g * split2 g)) with (q f g * split2 g - f) by ring.

    replace 2 with (2 ^+ 1) at 1 by reflexivity.
    replace (2 * e)%nat with ((e - 1) + (S e))%nat by lia.
    rewrite divstep_iter_add.
    rewrite divstep_lemma1.
    replace ((e - 1)%nat + 1%nat) with (of_nat e) by lia.
    replace ((e - 1) + 1)%nat with e by lia.
    rewrite divstep_iter_S'.
    fold (split2 g).
    rewrite divstep_lemma3.
    replace (1 - e) with (1 - e + of_nat 0) by lia.
    rewrite divstep_lemma2.
    apply f_equal2; [apply f_equal2|]. lia. reflexivity.
    rewrite Nat.add_0_r.
    rewrite z_eq. rewrite q'q. reflexivity. lia. lia. lia. Qed.
End __.

Section __.
  Context (R0 R1 : Z)
          (R0_odd : odd R0 = true)
          (R1_even : even R1 = true)
          (R1_non0 : R1 <> 0).

  Local Notation R_ i := (R_ R0 R1 i).
  Local Notation e i := (ord2 (R_ i)).
  Local Notation w j := (big_sum_nat (fun i => e (S i)) 0 j).

  Theorem G2 j (H : R_ j <> 0) :
    divstep_iter 1 R0 (R1 / 2) (2 * (w j))%nat =
    (1, split2 (R_ j), (R_ (S j)) / 2).
  Proof.
    induction j.
    - simpl. rewrite split2_odd by apply R0_odd. reflexivity.
    - rewrite R_S_S. Compute (10 mod2 0).
      replace (R_ (S j) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite big_op_S_r, Nat.mul_add_distr_l.
      rewrite divstep_iter_add.
      rewrite IHj.
      rewrite Zdiv_Zdiv, Zpower_nat_mul_r.
      eapply G1.
      apply Zpower_nat_nonneg. lia. lia. apply R_nonzero_S. apply odd_nonzero. apply R0_odd.
      assumption. lia.
      Unshelve. apply odd_split2.
      apply R_nonzero_S. apply odd_nonzero. apply R0_odd.
      assumption. apply R_even. apply odd_nonzero. apply R0_odd.
      apply R1_even. assumption. Qed.

  Theorem G3 :
    (exists t G, divstep_iter 1 R0 (R1 / 2) (2 * (big_sum_nat (fun i => e (S i)) 0 t))%nat = (1, G, 0) /\ abs G = gcd R0 R1) /\
    forall d f n, divstep_iter 1 R0 (R1 / 2) n = (d, f, 0) -> abs f = gcd R0 R1.
  Proof. apply and_lemma.
         destruct (@F26_cor2 R0 R1 R0_odd R1_even) as [t [Rt_non0 RSt_0]]. exists t, (split2 (R_ t)); split.
         rewrite G2. rewrite RSt_0. rewrite Z.div_0_l. reflexivity. lia. assumption. apply E3. assumption. assumption.
         apply RSt_0. apply Rt_non0.
         intros.
         destruct H as [t [G [H1 H2]]].
         set (w := big_sum_nat (fun i : nat => e (S i)) 0 t) in *.
         assert ((d + (2 * w)%nat, f, 0) = (1 + n, G, 0)).
         rewrite <- (divstep_iter_0 1 R0 (R1 / 2) 1 G (2 * w)) by assumption.
         rewrite <- (divstep_iter_0 1 R0 (R1 / 2) d f n) by assumption.
         rewrite Nat.add_comm. reflexivity. inversion H. assumption. Qed.

  Local Open Scope R.
  Local Coercion IZR : Z >-> R.
  Local Notation b := (log 2 (vec_norm (IZR R0, IZR R1))).

  Lemma b_spec : Rpower 2 b = vec_norm (IZR R0, IZR R1).
  Proof.
    apply Rpower_log; try lra.
    epose proof (vec_norm_nonneg (IZR R0, IZR R1)).
    epose proof (proj1 (vnonzero R0 R1)) _.
    epose proof (proj1 (vnonzero_norm _)) H0. lra.
    Unshelve. left. apply IZR_neq. apply odd_nonzero. apply R0_odd. Qed.

  (****************************************************************************)
  (** The following lemma is computational. It can almost be done inside coq. *)
  (** We have extracted OCaml code which can run in managable time.           *)
  (****************************************************************************)

  Theorem G4 : b <= 21 -> exists x y, divstep_iter 1 R0 (R1 / 2) (to_nat (floor (19 * b / 17))) = (x, y, 0%Z).
  Proof. Admitted.

  Notation it := (to_nat
                    (if Rle_dec b 21
                     then floor (19 * b / 17)
                     else if Rle_dec b 46
                          then floor ((49 * b + 23) / 17)
                          else floor (49 * b / 17))).


  Lemma IZR_lt_le (a b : Z) : a < b -> a + 1 <= b.
  Proof. intros. apply lt_IZR in H. autorewrite with pull_izr. apply IZR_le. lia. Qed.

  Lemma inv_div_1 a : / a = 1 / a.
  Proof. lra. Qed.

  Local Open Scope R.

  Theorem G6 : exists x y, divstep_iter 1 R0 (R1 / 2) it = (x, y, 0%Z).
  Proof.
    destruct (Rle_dec b 21) eqn:E; [apply G4; assumption|].

    assert (log 2 633 < 456 / 49).
    { apply log_upper_bound. lra. lra.

      rewrite <- Rabs_pos_eq.
      apply (lt_pow 49). replace 0 with (INR 0). lia. reflexivity.

      rewrite <- (Rpower_pow 49 (Rpower _ _)).
      rewrite Rpower_mult. replace (456 / 49 * (INR 49)) with 456.
      replace 456 with (INR 456%nat).
      rewrite Rpower_pow. lra. lra. apply INR_IZR_INZ.
      replace (INR 49%nat) with 49. lra. symmetry; apply INR_IZR_INZ.
      apply Rpower_pos_nonneg.
      apply Rlt_le. apply Rpower_pos_nonneg. }

    assert (ineq1 : (59 < floor ((49 * b) / 17))%Z).
    { apply lt_IZR. apply floor_lower_bound. nra. }
    assert (ineq2 : (floor ((49 * b) / 17) <= it)%Z).
    { rewrite E.
      destruct (Rle_dec b 46); rewrite Z2Nat.id by (apply floor_pos; lra).
      - apply floor_inc. lra.
      - reflexivity. }
    assert (ineq3 : (60 <= it)%Z). lia.

    destruct (@F26_cor2 R0 R1 R0_odd R1_even) as [t [H1 H2]].
    pose proof E3 R0 R1 t R0_odd R1_even H2 H1.
    pose proof G2 t H1.

    enough (2 * w t <= it)%nat.
    { eapply divstep_iter_0'.
      rewrite E in H4. apply H4. rewrite G2. rewrite H2. reflexivity. assumption. }

    destruct (le_dec (2 * w t) it); [assumption|].

    rewrite E in *.

    epose proof F6 (split2 (R_ t)) (R_ (S t)) _. Unshelve.
    pose proof (@F25 R0 R1 R0_odd R1_even t H1).
    pose proof Rle_trans _ _ _ H4 H5.

    assert (31 <= w t)%Z. lia.

    epose proof log_inc 2 _ _ _ (conj _ H6).
    rewrite log_1 in H8. rewrite log_mult in H8.

    assert (log 2 (1 / (alpha (w t))) <= b).
    { rewrite log_div, log_1. lra. lra. apply alpha_pos_nonneg. }

    assert (it + 1 <= 2 * (w t)). rewrite E.
    rewrite <- mult_IZR.
    apply IZR_lt_le. apply IZR_lt. lia.

    assert (34 / 49 < log 2 (1024 / 633)).

    {  rewrite log_div.

       replace 1024 with (2 ^ 10) by lra.
       rewrite log_pow_id.

       replace (INR 10%nat) with 10. lra. symmetry; apply INR_IZR_INZ. lra. lra. lra. lra. }


    destruct (le_dec 67 (w t)).
    - rewrite alpha67 in H9 by assumption.

      assert (w t * log 2 ( 1024 / 633 ) <= b).
      replace (IZR (of_nat (w t))) with (INR (w t)).
      rewrite <- log_pow. replace ((1024 / 633) ^ w t) with (1 / (633 / 1024) ^ w t). assumption.
      rewrite !pow_div. field. split. apply Rfunctions.pow_nonzero. lra. apply Rfunctions.pow_nonzero. lra. lra. lra.
      apply div_pos_nonneg. lra. lra.

      apply INR_IZR_INZ.
      assert (67 <= w t)%Z. lia.
      assert (34 * (w t) / 49 < b). nra.

      assert (2 * (w t) < 49 * b / 17).
      nra. assert (it + 1 < 49 * b / 17). lra.

      assert ((floor (49 * b / 17)) <= floor ((49 * b + 23) / 17))%Z.
      apply floor_inc. nra.

      assert (it <= floor ((49 * b + 23) / 17)).
      rewrite E. destruct (Rle_dec b 46). apply IZR_le. lia.
      apply IZR_le. lia.

      assert (floor (49 * b / 17) + 1 < 49 * b / 17). rewrite E in *. apply IZR_le in ineq2.
      lra.
      pose proof floor_spec (49 * b / 17). lra.

    - pose proof alpha31 (w t) ltac:(lia).

      assert ((alpha (w t) < Rpower 2 (- (34 * (w t) - 23) / 49))).
      rewrite <- Rabs_pos_eq. apply (lt_pow 49). lia.

      Ltac zlra :=
        match goal with
        | _ => progress autorewrite with pull_izr
        | [ |- _ <= _ ] => apply IZR_le
        | [ |- _ < _ ] => apply IZR_lt
        end; lia.

      rewrite <- !Rpower_pow.
      rewrite Rpower_mult. replace (- (34 * w t - 23) / 49 * INR 49) with (- (34 * w t - 23)).

      rewrite !INR_IZR_INZ.
      rewrite Rpower_Ropp.

      rewrite inv_div_1.

      replace (34 * w t - 23) with (INR (34 * w t - 23)).
      rewrite Rpower_pow.
      replace (IZR 49%nat) with (INR 49).
      rewrite Rpower_pow. assumption. apply alpha_pos_nonneg. apply INR_IZR_INZ. lra.
      autorewrite with pull_izr.
      rewrite !INR_IZR_INZ.
      apply IZR_eq. lia.

      rewrite !INR_IZR_INZ. field. apply Rpower_pos_nonneg.
      apply alpha_pos_nonneg.

      apply Rlt_le. apply Rpower_pos_nonneg.

      assert ((34 * w t - 23) / 49 <= b).
      etransitivity. shelve. apply H9.
      assert (2 * (w t) <= (49 * b + 23) / 17). lra.
      assert (it + 1 <= (49 * b + 23) / 17). lra.

      destruct (Rle_dec b 46) eqn:E2.
      rewrite E in *.
      rewrite Z2Nat.id in H10.
      pose proof (floor_spec ((49 * b + 23) / 17)) as [spec1 spec2]. lra.
      apply floor_pos. apply div_pos_pos. lra. lra.
      rewrite E in *.
      assert (floor (49 * 46 / 17) <= it).
      rewrite E, E2. rewrite Z2Nat.id. apply IZR_le. apply floor_inc. lra.
      apply floor_pos. lra. assert (2 * (w t) <= 132). rewrite <- mult_IZR. zlra.

      assert (132 = floor (49 * 46 / 17)). apply IZR_eq.
      apply floor_eq. lra. lra.

      rewrite E, E2 in *. lra.
    - apply alpha_pos_nonneg.
    - epose proof proj1 (vnonzero_norm (IZR R0, IZR R1)) _.
      pose proof vec_norm_nonneg (IZR R0, IZR R1). lra.
    - apply vnonzero. left. apply IZR_neq. apply psplit_non0. lia. assumption.
      Unshelve. lra. lra. apply log_le_lower_bound. lra.
      rewrite <- (Ropp_involutive (_ / _)). rewrite Rpower_Ropp. apply Rle_div_r.
      apply alpha_pos_nonneg.
      apply Rle_div_l. apply Rpower_pos_nonneg. replace (- ((34 * w t - 23) / 49)) with (- (34 * w t - 23) / 49).
      lra.
      lra.

      apply vnonzero. left. apply IZR_neq. apply odd_nonzero. apply R0_odd. Qed.
End __.
