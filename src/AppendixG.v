Require Import ZArith.
Require Import List Bool Znumtheory Decidable.
Require Import Rbase Reals QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

From BY Require Import AppendixE AppendixF Divstep Zpower_nat Zlemmas BigOp PadicVal Matrix.

Import Z.
Local Open Scope Z.

Arguments Z.mul : simpl never.
Arguments Z.sub : simpl never.
Arguments Z.add : simpl never.

Local Coercion of_nat : nat >-> Z.

Notation big_sum := (@big_op _ Z.add 0%Z).
Notation big_sum_nat := (@big_op _ Nat.add 0%nat).

Section __.

  Context {f g : Z}.

  Context {f_odd : odd f = true}
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
      apply Zpower_nat_nonneg. lia. lia.     lia. Qed.
  
  Lemma divstep_lemma2 i j (j_bound : (0 <= j + i < S e)%nat) :
    divstep_iter (1 - e + i) (split2 g) (z i) j = (j + 1 - e + i, split2 g, z (j + i)).
  Proof.
    induction j.
    - reflexivity.
    - simpl.
      rewrite IHj. unfold divstep.
      assert (0 <? j + 1 - e + i = false). apply Z.ltb_ge. lia.
      rewrite H. simpl. apply f_equal2; [apply f_equal2|]. lia. lia. reflexivity. lia. Qed.

  Lemma divstep_lemma3 :
    divstep e f (split2 g) = (1 - e, split2 g, z 0).
  Proof.
    unfold divstep.
    assert (0 <? e = true).
    rewrite <- Nat2Z.inj_0.
    apply Z.ltb_lt. apply inj_lt. apply ord2_even. apply g_even. rewrite H.
    rewrite odd_split2. reflexivity. apply g_non0. Qed.
  
  Lemma z_div j :
    2 ^+ (S j) * z j  = sum j * split2 g - f.
  Proof.
    induction j; intros.
    - rewrite big_op_nil by lia; simpl.
      rewrite mul_1_r. rewrite <- Z_div_exact_2. ring. lia.
      rewrite Zmod_even.
      rewrite even_sub. rewrite <- !negb_odd.
      rewrite odd_split2, f_odd.  reflexivity. apply g_non0.
    - simpl. replace (2 * (2 * 2 ^+ j) * ((z j + z j mod 2 * split2 g) / 2)) with
                 (((2 ^+ S j) * z j) + (2 * 2 ^+ j) * (z j mod 2 * split2 g)).

      rewrite IHj. 
      rewrite big_op_S_r. lia. lia.
      
      rewrite (mul_comm 2 (2 * _)).
      rewrite <- (mul_assoc _ 2).
      rewrite <- Z_div_exact_2. simpl. ring. lia.
      destruct (mod2_dec (z j)).
      + rewrite e. rewrite mul_0_l. rewrite add_0_r. assumption.
      + rewrite <- Zplus_mod_idemp_l. rewrite e. rewrite mul_1_l.
        apply mod_divide. lia. apply even_divide. rewrite even_add.
        rewrite <- (negb_odd (split2 _)). rewrite odd_split2. reflexivity. apply g_non0. Qed.

  Lemma sum_odd j :
    odd (sum j) = true.
  Proof.
    induction j.
    - reflexivity.
    - rewrite big_op_S_r, add_assoc, odd_add, IHj, !odd_mul. reflexivity. lia. Qed.

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

  (* Lemma z_spec : exists q', odd q' = true /\ (1 <= q' < 2 ^+ (S e)) /\ 2 ^+ (S e) * z e = q' * split2 g - f. *)
  (* Proof. *)
  
  (*   induction e eqn:E. *)
  (*   - exists 1. repeat split. lia. rewrite Nat.mul_0_r. unfold z. rewrite Zpower_nat_1. *)
  (*     rewrite <- Z_div_exact_full_2. lia. lia. apply mod_divide. lia. *)
  (*     apply even_divide. rewrite even_sub. *)
  (*     rewrite <- !negb_odd. rewrite f_odd. rewrite odd_split2. reflexivity. apply g_non0. *)
  (*   -  *)

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

Context {R0 R1 : Z}.
Context {R0_odd : odd R0 = true}
        {R1_even : even R1 = true}
        {R1_non0 : R1 <> 0}.

Local Notation R_ i := (R_ R0 R1 i).
Local Notation e i := (ord2 (R_ i)).

Theorem G2 j (H : R_ j <> 0) :
  divstep_iter 1 R0 (R1 / 2) (2 * (big_sum_nat (fun i => e (S i)) 0 j))%nat =
  (1, split2 (R_ j), (R_ (S j)) / 2).
Proof.
  induction j.
  - simpl. rewrite split2_odd by apply R0_odd. reflexivity.
  - rewrite R_S_S. Compute (10 mod2 0).
    replace (R_ (S j) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite big_op_S_r.
    rewrite Nat.mul_add_distr_l.
    rewrite divstep_iter_add.
    rewrite IHj.
    rewrite Zdiv_Zdiv, Zpower_nat_mul_r. 
    eapply G1.

    apply Zpower_nat_nonneg. lia. lia. apply R_nonzero_S. apply odd_nonzero. apply R0_odd.
    assumption. lia. Unshelve. apply odd_split2.
    apply R_nonzero_S. apply odd_nonzero. apply R0_odd.
    assumption. apply R_even. apply odd_nonzero. apply R0_odd.
    apply R1_even. assumption. Qed.

(* Local Notation t := (Nat.max 67 (Z.to_nat (up (log_1024_633 (vec_norm (IZR R0, IZR R1))))))%nat. *)

Theorem G3 :
  (exists t G, divstep_iter 1 R0 (R1 / 2) (2 * (big_sum_nat (fun i => e (S i)) 0 t))%nat = (1, G, 0) /\ abs G = gcd R0 R1) /\
  forall d f n, divstep_iter 1 R0 (R1 / 2) n = (d, f, 0) -> abs f = gcd R0 R1.
Proof. apply and_lemma. 
  destruct (F26_cor2 R0_odd R1_even) as [t [Rt_non0 RSt_0]]. exists t, (split2 (R_ t)); split.
  rewrite G2. rewrite RSt_0. rewrite Z.div_0_l. reflexivity. lia. assumption. apply E3. apply R0_odd. apply R1_even.
  apply RSt_0. apply Rt_non0. 

  intros.
  destruct H as [t [G [H1 H2]]].
  set (w := big_sum_nat (fun i : nat => e (S i)) 0 t) in *.
  assert ((d + (2 * w)%nat, f, 0) = (1 + n, G, 0)).
  rewrite <- (divstep_iter_0 1 R0 (R1 / 2) 1 G (2 * w)) by assumption.
  rewrite <- (divstep_iter_0 1 R0 (R1 / 2) d f n) by assumption.
  rewrite Nat.add_comm. reflexivity. inversion H. assumption. Qed.
