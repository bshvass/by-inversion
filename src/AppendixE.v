From Coq Require Import Bool List.
From Coq Require Import ZArith Znumtheory micromega.Lia.
From Coq Require Import Reals Rbase micromega.Lra.

From BY Require Import Zlemmas PadicVal Zpower_nat ModInv InductionPrinciples Matrix IZR.

Import Z RinvImpl.

Local Coercion IZR : Z >-> R.
Local Open Scope Z.

Lemma and_lemma (P Q : Prop) (H1 : P) (H2 : P -> Q) : P /\ Q.
Proof. tauto. Qed.

Notation ord2 g := (pval 2 g).
Notation split2 g := (psplit 2 g).

Lemma ord2_even g (Hg : even g = true) : (0 < ord2 g)%nat.
Proof.
  destruct (eq_dec g 0) as [e|e]; [rewrite e; cbn; lia|].
  apply pval_lower_bound. assumption. lia.
  simpl. apply even_divide. assumption. Qed.

Lemma ord2_odd g (Hg : odd g = true) : (ord2 g = 0)%nat.
Proof.
  apply pval_unique. apply odd_nonzero. assumption. lia.
  split.
  - apply divide_1_l.
  - simpl; intros H. apply even_div in H. rewrite <- negb_even, H in Hg. inversion Hg. Qed.

Lemma odd_split2 g (Hg : g <> 0) : odd (split2 g) = true.
Proof.
  apply odd_gcd; apply Zgcd_1_rel_prime; apply rel_prime_sym.
  apply prime_rel_prime; [apply prime_2|apply psplit_spec; lia]. Qed.

Lemma split2_odd g (Hg : odd g = true) : split2 g = g.
Proof. unfold split2; rewrite ord2_odd by assumption; apply div_1_r. Qed.

Lemma split2_0 : split2 0 = 0.
Proof. reflexivity. Qed.

Definition q f g := ((f * (mod_inv (split2 g) (2 ^+ (S (ord2 g))))) mod (2 ^+ (S (ord2 g))))%Z.

Lemma q_0_r a : q a 0 = 0.
Proof. unfold q; cbn; rewrite Z.mul_0_r; reflexivity. Qed.

Lemma q_0_l a : q 0 a = 0.
Proof.
  unfold q. rewrite Z.mul_0_l, Z.mod_0_l. reflexivity.
  apply Zpower_nat_nonzero; lia. Qed.

Definition div_2 f g : R :=
  q f g / 2 ^+ ord2 g.

Definition mod_2 f g : Z :=
  (f - q f g * (split2 g)).

Notation "a 'mod2' b" := (mod_2 a b) (at level 50).
Notation "a 'div2' b" := (div_2 a b) (at level 30).

Lemma mod2_0_r a : a mod2 0 = a.
Proof. unfold mod_2; rewrite q_0_r, Z.sub_0_r; reflexivity. Qed.

Lemma mod2_0_l a : 0 mod2 a = 0.
Proof. unfold mod_2; rewrite q_0_l, Z.mul_0_l; reflexivity. Qed.

Lemma div2_mod2 f g (g0 : (g <> 0)%Z) : IZR f = ((f div2 g) * g + (f mod2 g))%R.
Proof.
  unfold div_2, mod_2, split2. rewrite minus_IZR, mult_IZR, div_IZR. field.
  apply IZR_neq. apply Zpower_nat_nonzero. lia.
  apply pval_spec. lia. lia. Qed.

Theorem q_spec f g (Hf : odd f = true) (Hg : g <> 0) :
  (odd (q f g) = true) /\ (1 <= q f g < 2 ^+ (S (ord2 g))) /\ (2 ^+ (S (ord2 g)) | (q f g) * (split2 g) - f).
Proof.
  set (e := ord2 g).
  assert (H1 : 1 < 2 ^+ (S e)) by (apply Zpower_nat_gt1; lia).
  assert (H2 : rel_prime (split2 g) (2 ^+ (S e))).
  { apply rel_prime_pow. lia. apply Zgcd_1_rel_prime. apply odd_gcd. apply odd_split2. assumption. }
  apply and_lemma; [|split].
  - unfold q.
    rewrite odd_mod_pow2.
    rewrite odd_mul, Hf, andb_true_l. apply odd_gcd. apply Zgcd_1_rel_prime.
    apply (rel_prime_pow _ _ (S e)). lia. apply prime_inv. lia.
    exists (split2 g). rewrite mul_comm. apply mod_inv_spec. assumption. lia. lia.
  - assert (q f g <> 0) by (apply odd_nonzero; assumption).
    enough (0 <= q f g < 2 ^+ S e). lia.
    apply mod_pos_bound. lia.
  - unfold q. replace (ord2 g) with e by reflexivity.
    apply Zmod_divide. lia.
    rewrite <- Zminus_mod_idemp_l.
    rewrite Zmult_mod_idemp_l. rewrite <- mul_assoc.
    rewrite <- Zmult_mod_idemp_r.
    rewrite (mul_comm _ (split2 g)). rewrite mod_inv_spec, mul_1_r.
    rewrite Zminus_mod_idemp_l. rewrite sub_diag, mod_0_l. reflexivity. lia. assumption. lia. Qed.

Theorem q_unique f g (Hf : odd f = true) (Hg : g <> 0) q' :
  (odd q' = true) /\ (1 <= q' < 2 ^+ (S (ord2 g))) /\ (2 ^+ (S (ord2 g)) | q' * (split2 g) - f) -> q' = q f g.
Proof.
  pose proof (q_spec f g ltac:(auto) ltac:(auto)) as [q_odd [q_bound q_div]].
  intros [q'_odd [q'_bound q'_div]]. 
  assert (2 ^+ (S (ord2 g)) | (q f g) - q'). 
  apply (Gauss _ (split2 g)). replace ((split2 g) * ((q f g) - q')) with ((q f g) * (split2 g) - f - (q' * (split2 g) - f)) by ring.
  apply divide_sub_r; auto. 
  apply rel_prime_sym. apply rel_prime_pow. lia.
  apply odd_rel_prime. apply odd_split2. assumption.
  apply mod_equiv in H. rewrite !mod_small in H; lia. lia. Qed.

Theorem E1 f (Hf : odd f = true) g (Hg : g <> 0) :
  exists! q, (odd q = true) /\ (1 <= q < 2 ^+ S (ord2 g)) /\ (2 ^+ (S (ord2 g)) | q * (split2 g) - f).
Proof. exists (q f g); split; [apply q_spec; assumption|symmetry; apply q_unique; assumption]. Qed.

Lemma mod2_div f g (Hf : odd f = true) (Hg : g <> 0) : (2 ^+ (S (ord2 g)) | f mod2 g).
Proof.
  unfold mod_2. apply Zdivide_opp_r_rev.
  replace (- (f - q f g * split2 g)) with ((q f g) * (split2 g) - f) by ring.
  apply q_spec; assumption. Qed.

Lemma mod2_div' f g (Hf : odd f = true) (Hg : g <> 0) : (2 ^+ (ord2 g) | f mod2 g).
Proof. transitivity (2 ^+ (S (ord2 g))). exists 2. reflexivity. apply mod2_div; assumption. Qed.

Section __.

  Variables (R0 R1 : Z).

  Fixpoint R_ i :=
    match i with
    | 0%nat => R0
    | S j => match j with
            | 0%nat => R1
            | S k => if R_ j =? 0 then 0 else - ((split2 (R_ k)) mod2 (R_ j)) / 2 ^+ (ord2 (R_ j))
            end
    end.

  Notation e i := (ord2 (R_ i)).

  Lemma R_S_S i :
    R_ (S (S i)) = if R_ (S i) =? 0 then 0 else - ((split2 (R_ i)) mod2 (R_ (S i))) / 2 ^+ (e (S i)).
  Proof. reflexivity. Qed.

  Lemma R_zero_S i (R0_nonzero : R0 <> 0) : R_ i = 0 -> R_ (S i) = 0.
  Proof.
    induction i; intros H.
    - simpl in *; lia.
    - rewrite R_S_S, H; reflexivity. Qed.

  Lemma R_zero_S' i : R_ (S i) = 0 -> R_ (S (S i)) = 0.
  Proof.
    induction i; intros H.
    - simpl in *; rewrite H; simpl; lia.
    - rewrite R_S_S, H; reflexivity. Qed.

  Lemma R_nonzero_S i (R0_nonzero : R0 <> 0) : R_ (S i) <> 0 -> R_ i <> 0.
  Proof. intros H H0; apply R_zero_S in H0; [contradiction|assumption]. Qed.

  Lemma R_zero i j (H : R0 <> 0) : R_ i = 0 -> (i <= j)%nat -> R_ j = 0.
  Proof.
    intros H1; revert j; apply (induction_at i).
    - assumption.
    - intros; apply R_zero_S; assumption. Qed.

  Lemma R_zero' i j : R_ (S i) = 0 -> ((S i) <= j)%nat -> R_ j = 0.
  Proof.
    intros H1; revert j; apply (induction_at (S i)).
    - assumption.
    - intros; destruct m; [lia|apply R_zero_S']; assumption. Qed.

  Lemma R_nonzero i j (R0_nonzero : R0 <> 0) : R_ i <> 0 -> (j <= i)%nat -> R_ j <> 0.
  Proof.
    intros i_nonzero j_le_i j_zero.
    destruct j; [simpl in j_zero; lia|]. apply (R_zero' _ i) in j_zero. contradiction. lia. Qed.

  Lemma R_S_S' i (H : R_ (S i) =? 0 = false) :
    R_ (S (S i)) = - ((split2 (R_ i)) mod2 (R_ (S i))) / 2 ^+ (e (S i)).
  Proof. rewrite R_S_S, H; reflexivity. Qed.

  Lemma R_even i (R0_nonzero : R0 <> 0) (R1_even : even R1 = true) : even (R_ (S i)) = true.
  Proof.
    destruct i; [assumption|].
    rewrite R_S_S.
    destruct (R_ (S i) =? 0) eqn:E; [reflexivity|apply Z.eqb_neq in E].
    assert (2 ^+ S (e (S i)) | - (split2 (R_ i) mod2 (R_ (S i)))).
    { apply Zdivide_opp_r; apply mod2_div; [apply odd_split2|assumption]; apply R_nonzero_S; assumption. }
    apply even_div; apply divide_lemma. apply Zpower_nat_pos_nonneg. lia.
    transitivity (2 ^+ S (e (S i))). exists 2.  reflexivity. assumption. rewrite Zpower_nat_mul_r. assumption. Qed.

  Lemma e_ge_1 i (R0_nonzero : R0 <> 0) (R1_even : even R1 = true) : (1 <= e (S i))%nat.
  Proof. apply ord2_even. apply R_even; assumption. Qed.

  Lemma R_eq i :
    IZR ((split2 (R_ i)) mod2 (R_ (S i))) = (split2 (R_ i) - (split2 (R_ i)) div2 (R_ (S i)) * R_ (S i))%R.
  Proof.
    destruct (Z.eq_dec (R_ (S i)) 0) as [e|e].
    - rewrite e, Rmult_0_r, Rminus_0_r, mod2_0_r. reflexivity.
    - rewrite (div2_mod2 (split2 (R_ i)) (R_ (S i))). field. assumption. Qed.

  Lemma R_recurrence i (H : R_ (S i) <> 0) (R0_nonzero : R0 <> 0) :
    2 ^+ (2 * e (S i) + e i) * (R_ (S (S i)))
    = 2 ^+ (e i) * q (split2 (R_ i)) (R_ (S i)) * (R_ (S i)) - 2 ^+ (e (S i)) * (R_ i).
  Proof.
    rewrite R_S_S, ((proj2 (Z.eqb_neq _ _)) H).
    assert (R_ i <> 0) by (apply R_nonzero_S; assumption).
    assert (2 ^+ (2 * e (S i) + e i)  =
            2 ^+ (e i) * 2 ^+ (e (S i)) * 2 ^+ (e (S i))).
    replace (2 * _)%nat with (e (S i) + e (S i))%nat by ring. rewrite !Zpower_nat_is_exp; ring.
    rewrite H1.
    rewrite <- (mul_assoc _ _ (_ / _)). rewrite <- Z_div_exact_2.
    unfold mod_2. ring_simplify.

    set (q' := q (split2 (R_ i)) (R_ (S i))).

    replace (- 2 ^+ e i * 2 ^+ e (S i) * split2 (R_ i)) with
        (- 2 ^+ e (S i) * (2 ^+ e i * split2 (R_ i))) by ring.
    rewrite <- psplit_spec'.

    replace (2 ^+ e i * 2 ^+ e (S i) * q' * split2 (R_ (S i))) with
        (2 ^+ e i * q' * (2 ^+ e (S i) * split2 (R_ (S i)))) by ring.
    rewrite <- psplit_spec'. ring. assumption. lia. assumption. lia.
    apply lt_gt; apply Zpower_nat_pos_nonneg. lia.

    apply Zdivide_mod. apply Zdivide_opp_r. apply mod2_div'. apply odd_split2. assumption. assumption. Qed.

  Lemma R_recurrence' i (H : R_ (S i) <> 0) (R0_nonzero : R0 <> 0) :
    2 ^+ e (S i) * (R_ i)
    = 2 ^+ e i * q (split2 (R_ i)) (R_ (S i)) * (R_ (S i)) - 2 ^+ (2 * e (S i) + e i) * (R_ (S (S i))).
  Proof. rewrite R_recurrence; lia. Qed.

  Local Open Scope R.
  Local Open Scope mat_scope.

  Theorem E2 i (HR0 : R0 <> 0%Z) (H : R_ (S i) <> 0%Z) :
    [ IZR (split2 (R_ (S i))) ; IZR (R_ (S (S i))) ] =
    [ 0 , 1 / 2 ^ (e (S i)) ; - 1 / 2 ^ (e (S i)) , (split2 (R_ i) div2 (R_ (S i))) / 2 ^ (e (S i))] *v [ IZR (split2 (R_ i)) ; IZR (R_ (S i))].
  Proof.
    rewrite R_S_S, ((proj2 (Z.eqb_neq _ _)) H).
    unfold vmult.
    apply f_equal2.
    - field_simplify; [|apply Rfunctions.pow_nonzero; lra].
      unfold split2. rewrite div_IZR, Zpower_nat_IZR by (apply pval_spec; lia). reflexivity.
    - rewrite div_IZR, Zpower_nat_IZR, opp_IZR, R_eq. field.
      apply Rfunctions.pow_nonzero. lra.
      apply Zdivide_opp_r; apply mod2_div'; [apply odd_split2|assumption]; apply R_nonzero_S; assumption. Qed.

  Local Close Scope R.
  Local Open Scope Z.

  Theorem E3 t (R0_odd : odd R0 = true) (R1_even : even R1 = true) :
    R_ (S t) = 0 -> R_ t <> 0 -> abs (split2 (R_ t)) = gcd R0 R1.
  Proof.
    intros.
    set (g := gcd R0 R1).
    assert (R0_nonzero : R0 <> 0) by (apply odd_nonzero; assumption).
    assert (odd g = true).
    { unfold g; apply gcd_odd_l; assumption. }

    assert (forall i, (g | R_ i)).
    - induction i using induction2.
      + unfold g; simpl. apply gcd_divide_l.
      + unfold g; simpl. apply gcd_divide_r.
      + destruct (eq_dec (R_ (S (S i))) 0).
        * rewrite e. apply divide_0_r.
        * eapply Gauss.
          rewrite R_recurrence.
          apply divide_sub_r.
          apply divide_mul_r. assumption.
          apply divide_mul_r. assumption.  apply R_nonzero_S. assumption. assumption. assumption.
          apply odd_rel_prime_pow.
          pose proof (ord2_even _ (R_even i R0_nonzero R1_even)). lia. assumption.
    - set (g' := split2 (R_ t)).
      assert (g | 2 ^+ e t * g').
      { rewrite <- (psplit_spec' 2). apply H2. assumption. lia. }
      assert (g | g').
      { destruct (e t). rewrite Zpower_nat_0_r in H3. rewrite mul_1_l in H3. assumption.
        apply Gauss in H3. assumption. apply odd_rel_prime_pow. lia. assumption. }

      assert (forall i, (g' | R_ i)).
      intros.
      destruct (le_dec i (S t)).
      + generalize i l. apply rev_2_ind.
        * rewrite H. apply divide_0_r.
        * exists (2 ^+ (e t)). apply psplit_spec. assumption. lia.
        * intros. destruct k as [| [|k] ]; [assumption|assumption|].
          rewrite !Nat.pred_succ in *.
          eapply Gauss.
          rewrite R_recurrence'.
          apply divide_sub_r.
          apply divide_mul_r. assumption.
          apply divide_mul_r. assumption.

          apply R_nonzero with (i := t). assumption. assumption. lia. assumption.

          apply odd_rel_prime_pow.
          pose proof (ord2_even _ (R_even k R0_nonzero R1_even)). lia.
          apply odd_split2. assumption.

      + rewrite R_zero with (i := S t). apply divide_0_r. assumption. assumption. lia.
      + assert (g' | g).
        apply gcd_divide_iff.
        replace R0 with (R_ 0) by reflexivity.
        replace R1 with (R_ 1) by reflexivity.
        split; apply H5.
        rewrite <- abs_eq. apply divide_antisym_abs; assumption.
        unfold g. apply gcd_nonneg. Qed.

End __.
