From Coq Require Import Bool List.
From Coq Require Import ZArith Znumtheory micromega.Lia.
From Coq Require Import Reals Rbase micromega.Lra.

From BY Require Import Zlemmas PadicVal Zpower_nat ModInv InductionPrinciples Matrix IZR.

Import Z RinvImpl.

Local Coercion IZR : Z >-> R.
Local Open Scope Z.


Lemma and_lemma (P Q : Prop) (H1 : P) (H2 : P -> Q) : P /\ Q.
Proof. tauto. Qed.

Local Notation ord2 g := (pval 2 g).
Local Notation split2 g := (psplit 2 g).

Lemma ord2_even g (Hg : even g = true) : (0 < ord2 g)%nat.
Proof.
  destruct (eq_dec g 0) as [e|e]; [rewrite e; cbn; lia|].
  apply pval_lower_bound. assumption. lia.
  simpl. apply even_divide. assumption. Qed.

Lemma split2_odd g (Hg : g <> 0) : odd (split2 g) = true.
Proof.
  apply odd_gcd; apply Zgcd_1_rel_prime; apply rel_prime_sym.
  apply prime_rel_prime; [apply prime_2|apply psplit_spec; lia]. Qed.

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

Local Notation "a 'mod2' b" := (mod_2 a b) (at level 50).
Local Notation "a 'div2' b" := (div_2 a b) (at level 30).

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
  { apply rel_prime_pow. lia. apply Zgcd_1_rel_prime. apply odd_gcd. apply split2_odd. assumption. }
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

Lemma mod2_div f g (Hf : odd f = true) (Hg : g <> 0) : (2 ^+ (S (ord2 g)) | f mod2 g).
Proof.
  unfold mod_2. apply Zdivide_opp_r_rev.
  replace (- (f - q f g * split2 g)) with ((q f g) * (split2 g) - f) by ring.
  apply q_spec; assumption. Qed.

Lemma mod2_div' f g (Hf : odd f = true) (Hg : g <> 0) : (2 ^+ (ord2 g) | f mod2 g).
Proof. transitivity (2 ^+ (S (ord2 g))). exists 2. reflexivity. apply mod2_div; assumption. Qed.

Fixpoint R R0 R1 i {struct i} :=
  match i with
  | 0%nat => R0
  | S j => if R1 =? 0 then 0 else R R1 (- ((split2 R0) mod2 R1) / 2 ^+ (ord2 R1)) j
  end.

Lemma R_0 R0 R1 : R R0 R1 0 = R0.
Proof. reflexivity. Qed.

Lemma R_1 R0 R1 : R R0 R1 1 = R1.
Proof. unfold R; destruct (R1 =? 0) eqn:E; [apply Z.eqb_eq in E|]; lia. Qed.

Fixpoint R_alt R0 R1 i {struct i} :=
  match i with
  | 0%nat => R0
  | S j => match j with
          | 0%nat => R1
          | S k => if R_alt R0 R1 j =? 0 then 0 else - ((split2 (R_alt R0 R1 k)) mod2 (R_alt R0 R1 j)) / 2 ^+ (ord2 (R_alt R0 R1 j))
          end
  end.

Lemma R_alt_S_S R0 R1 i :
  R_alt R0 R1 (S (S i)) = if R_alt R0 R1 (S i) =? 0 then 0 else - ((split2 (R_alt R0 R1 i)) mod2 (R_alt R0 R1 (S i))) / 2 ^+ (ord2 (R_alt R0 R1 (S i))).
Proof. reflexivity. Qed.

Lemma R_alt_zero_S R0 R1 i (H : R0 <> 0) : R_alt R0 R1 i = 0 -> R_alt R0 R1 (S i) = 0.
Proof.
  revert H; revert R0 R1.
  induction i; intros.
  - simpl in *; lia.
  - rewrite R_alt_S_S. rewrite H0. reflexivity. Qed.

Lemma R_alt_zero_S' R0 R1 i : R_alt R0 R1 (S i) = 0 -> R_alt R0 R1 (S (S i)) = 0.
Proof.
  revert R0 R1.
  induction i; intros.
  - simpl in *; rewrite H; simpl; lia.
  - rewrite R_alt_S_S. rewrite H. reflexivity. Qed.

Lemma R_alt_nonzero_S R0 R1 i (R0_nonzero : R0 <> 0) : R_alt R0 R1 (S i) <> 0 -> R_alt R0 R1 i <> 0.
Proof. intros H H0; apply R_alt_zero_S in H0; [contradiction|assumption]. Qed.

Lemma R_alt_zero R0 R1 i j (H : R0 <> 0) : R_alt R0 R1 i = 0 -> (i <= j)%nat -> R_alt R0 R1 j = 0.
Proof.
  intros H1; revert j; apply (induction_at i).
  - assumption.
  - intros; apply R_alt_zero_S; assumption. Qed.

Lemma R_alt_zero' R0 R1 i j : R_alt R0 R1 (S i) = 0 -> ((S i) <= j)%nat -> R_alt R0 R1 j = 0.
Proof.
  intros H1; revert j; apply (induction_at (S i)).
  - assumption.
  - intros; destruct m; [lia|apply R_alt_zero_S']; assumption. Qed.

Lemma R_alt_nonzero R0 R1 i j (R0_nonzero : R0 <> 0) : R_alt R0 R1 i <> 0 -> (j <= i)%nat -> R_alt R0 R1 j <> 0.
Proof.
  intros i_nonzero j_le_i. 
  intros j_zero.
  destruct j; [simpl in j_zero; lia|]. apply (R_alt_zero' _ _ _ i) in j_zero. contradiction. lia. Qed.

Lemma R_S R0 R1 i :
  R R0 R1 (S i) = if R1 =? 0 then 0 else R R1 (- ((split2 R0) mod2 R1) / 2 ^+ (ord2 R1)) i.
Proof. reflexivity. Qed.

Lemma R_alt_S_S' R0 R1 i (H : R_alt R0 R1 (S i) =? 0 = false) :
  R_alt R0 R1 (S (S i)) = - ((split2 (R_alt R0 R1 i)) mod2 (R_alt R0 R1 (S i))) / 2 ^+ (ord2 (R_alt R0 R1 (S i))).
Proof. rewrite R_alt_S_S, H; reflexivity. Qed.

Lemma R_R_alt_aux R0 R1 i j :
  R (R_alt R0 R1 i) (R_alt R0 R1 (S i)) j = R_alt R0 R1 (j + i).
Proof.
  revert R0 R1 i.
  induction j; intros R0 R1 i. 
  - reflexivity.
  - rewrite R_S.
    destruct (R_alt R0 R1 (S i) =? 0) eqn:E.
    + symmetry; eapply R_alt_zero'. apply Z.eqb_eq in E. apply E. lia.
    + rewrite <- R_alt_S_S' by assumption. rewrite IHj. apply f_equal. lia. Qed.

Lemma R_R_alt R0 R1 i :
  R R0 R1 i = R_alt R0 R1 i.
Proof.
  replace R0 with (R_alt R0 R1 0) at 1 by reflexivity.
  replace R1 with (R_alt R0 R1 1) at 2 by reflexivity. rewrite R_R_alt_aux.
  apply f_equal; lia. Qed.

Lemma R_spec R0 R1 i (H : R R0 R1 (S i) <> 0) :
  R R0 R1 (S (S i)) = - (split2 (R R0 R1 i) mod2 (R R0 R1 (S i))) / 2 ^+ (ord2 (R R0 R1 (S i))).
Proof. apply Z.eqb_neq in H; rewrite !R_R_alt in *; apply R_alt_S_S'; assumption. Qed.

Lemma R_even R0 R1 i (R0_nonzero : R0 <> 0) (R1_even : even R1 = true) : even (R R0 R1 (S i)) = true.
Proof.
  revert R0_nonzero R1_even; revert R0 R1.
  induction i; intros R0 R1 R1_even R0_nonzero.
  - unfold R. destruct (R1 =? 0). reflexivity. assumption.
  - rewrite R_S.
    destruct (R1 =? 0) eqn:E. reflexivity.
    apply Z.eqb_neq in E.
    assert (2 ^+ S (ord2 R1) | - (split2 R0 mod2 R1)). apply Zdivide_opp_r. apply mod2_div. apply split2_odd. assumption. assumption.
    apply IHi. assumption.
    apply even_div. apply divide_lemma. apply Zpower_nat_pos_nonneg. lia.
    transitivity (2 ^+ S (ord2 R1)). exists 2. reflexivity. assumption.
    rewrite Zpower_nat_mul_r. assumption. Qed.

Lemma R_alt_even R0 R1 i (R0_nonzero : R0 <> 0) (R1_even : even R1 = true) : even (R_alt R0 R1 (S i)) = true.
Proof. rewrite <- R_R_alt. apply R_even; assumption. Qed.

Lemma R_0_r a n : R a 0 (S n) = 0%Z.
Proof. reflexivity. Qed.

Lemma R_S_0 a b n (Ha : a <> 0) : R a b n = 0 -> R a b (S n) = 0.
Proof. rewrite !R_R_alt. apply R_alt_zero_S. assumption. Qed.

Lemma R_S_0_contra a b n (Ha : a <> 0) : R a b (S n) <> 0 -> R a b n <> 0.
Proof. intros H H0; apply R_S_0 in H0. contradiction. assumption. Qed.

Lemma R_nonzero R0 R1 i j (R0_nonzero : R0 <> 0) : R R0 R1 i <> 0 -> (j <= i)%nat -> R R0 R1 j <> 0.
Proof. rewrite !R_R_alt. apply R_alt_nonzero. assumption. Qed.

Lemma R_zero R0 R1 i j (H : R0 <> 0) : R R0 R1 i = 0 -> (i <= j)%nat -> R R0 R1 j = 0.
Proof. rewrite !R_R_alt. apply R_alt_zero. assumption. Qed.

Lemma R_zero' R0 R1 i j : R R0 R1 (S i) = 0 -> ((S i) <= j)%nat -> R R0 R1 j = 0.
Proof. rewrite !R_R_alt. apply R_alt_zero'. Qed.

Lemma R_eq R0 R1 i :
  IZR ((split2 (R R0 R1 i)) mod2 (R R0 R1 (S i))) = (split2 (R R0 R1 i) - (split2 (R R0 R1 i)) div2 (R R0 R1 (S i)) * R R0 R1 (S i))%R.
Proof.
  destruct (Z.eq_dec (R R0 R1 (S i)) 0).
  - rewrite e. rewrite Rmult_0_r, Rminus_0_r, mod2_0_r. reflexivity.
  - rewrite (div2_mod2 (split2 (R R0 R1 i)) (R R0 R1 (S i))). field. assumption. Qed.

Lemma R_recurrence R0 R1 i (H : R R0 R1 (S i) <> 0) (R0_nonzero : R0 <> 0) :
  2 ^+ (2 * ord2 (R R0 R1 (S i)) + ord2 (R R0 R1 i)) * (R R0 R1 (S (S i)))
  = 2 ^+ (ord2 (R R0 R1 i)) * q (split2 (R R0 R1 i)) (R R0 R1 (S i)) * (R R0 R1 (S i)) - 2 ^+ (ord2 (R R0 R1 (S i))) * (R R0 R1 i).
Proof.
  assert (R R0 R1 i <> 0) by (apply R_S_0_contra; assumption).
  rewrite R_spec.  
  assert (2 ^+ (2 * ord2 (R R0 R1 (S i)) + ord2 (R R0 R1 i))  =
          2 ^+ (ord2 (R R0 R1 i)) * 2 ^+ (ord2 (R R0 R1 (S i))) * 2 ^+ (ord2 (R R0 R1 (S i)))).
  replace (2 * _)%nat with (ord2 (R R0 R1 (S i)) + ord2 (R R0 R1 (S i)))%nat by ring. rewrite !Zpower_nat_is_exp; ring.
  rewrite H1.
  rewrite <- (mul_assoc _ _ (_ / _)). rewrite <- Z_div_exact_2.
  unfold mod_2. ring_simplify. 

  set (q' := q (split2 (R R0 R1 i)) (R R0 R1 (S i))).

  replace (- 2 ^+ ord2 (R R0 R1 i) * 2 ^+ ord2 (R R0 R1 (S i)) * split2 (R R0 R1 i)) with
      (- 2 ^+ ord2 (R R0 R1 (S i)) * (2 ^+ ord2 (R R0 R1 i) * split2 (R R0 R1 i))) by ring.
  rewrite <- psplit_spec'.

  replace (2 ^+ ord2 (R R0 R1 i) * 2 ^+ ord2 (R R0 R1 (S i)) * q' * split2 (R R0 R1 (S i))) with
      (2 ^+ ord2 (R R0 R1 i) * q' * (2 ^+ ord2 (R R0 R1 (S i)) * split2 (R R0 R1 (S i)))) by ring.
  rewrite <- psplit_spec'. ring. assumption. lia. assumption. lia.
  apply lt_gt; apply Zpower_nat_pos_nonneg. lia.

  apply Zdivide_mod. apply Zdivide_opp_r. apply mod2_div'. apply split2_odd. assumption. assumption. assumption. Qed.

Lemma R_recurrence' R0 R1 i (H : R R0 R1 (S i) <> 0) (R0_nonzero : R0 <> 0) :
  2 ^+ (ord2 (R R0 R1 (S i))) * (R R0 R1 i)
  = 2 ^+ (ord2 (R R0 R1 i)) * q (split2 (R R0 R1 i)) (R R0 R1 (S i)) * (R R0 R1 (S i)) - 2 ^+ (2 * ord2 (R R0 R1 (S i)) + ord2 (R R0 R1 i)) * (R R0 R1 (S (S i))).
Proof. rewrite R_recurrence; lia. Qed.

Local Open Scope R.
Theorem E2 R0 R_1 i (HR0 : R0 <> 0%Z) (H : R R0 R_1 (S i) <> 0%Z) :
  [ IZR (split2 (R R0 R_1 (S i))) ; IZR (R R0 R_1 (S (S i))) ] =
  [ 0 , 1 / 2 ^ (ord2 (R R0 R_1 (S i))) ; - 1 / 2 ^ (ord2 (R R0 R_1 (S i))) , (split2 (R R0 R_1 i) div2 (R R0 R_1 (S i))) / 2 ^ (ord2 (R R0 R_1 (S i)))] *col [ IZR (split2 (R R0 R_1 i)) ; IZR (R R0 R_1 (S i))].
Proof.
  unfold colmult.
  apply f_equal2. field_simplify. 
  unfold split2. rewrite div_IZR. rewrite Zpower_nat_IZR. reflexivity.

  destruct (Z.eq_dec (R R0 R_1 (S i)) 0).
  - rewrite e. apply Z.divide_0_r.
  - apply pval_spec. assumption. lia.
  - apply Rfunctions.pow_nonzero. lra.
  - rewrite R_spec.
    
    rewrite div_IZR. rewrite Zpower_nat_IZR. rewrite opp_IZR. rewrite R_eq. field.

    apply Rfunctions.pow_nonzero. lra.

    apply Zdivide_opp_r. apply mod2_div'. apply split2_odd. intro. apply R_S_0 in H0. contradiction. assumption.
    assumption.
    assumption. Qed.
Local Close Scope R.
Local Open Scope Z.



Theorem E3 R0 R1 t (R0_odd : odd R0 = true) (R1_even : even R1 = true) :
  R R0 R1 (S t) = 0 -> R R0 R1 t <> 0 -> abs (split2 (R R0 R1 t)) = gcd R0 R1.
Proof.
  intros.
  set (g := gcd R0 R1).
  assert (R0_nonzero : R0 <> 0) by (apply odd_nonzero; assumption).
  assert (odd g = true).
  { unfold g; apply gcd_odd_l; assumption. }

  assert (forall i, (g | R R0 R1 i)).
  - induction i using induction2.
    + unfold g; simpl. apply gcd_divide_l.
    + unfold g; simpl. destruct (R1 =? 0); [apply divide_0_r|apply gcd_divide_r].
    + destruct (eq_dec (R R0 R1 (S (S i))) 0).
      * rewrite e. apply divide_0_r.
      * eapply Gauss.
        rewrite R_recurrence.
        apply divide_sub_r.
        apply divide_mul_r. assumption.
        apply divide_mul_r. assumption.  apply R_S_0_contra. assumption. assumption. assumption.
        apply odd_rel_prime_pow.
        pose proof (ord2_even _ (R_even _ _ i R0_nonzero R1_even)). lia. assumption.
  - set (g' := split2 (R R0 R1 t)).
    assert (g | 2 ^+ (ord2 (R R0 R1 t)) * g').
    { rewrite <- (psplit_spec' 2). apply H2. assumption. lia. }
    apply Gauss in H3.

    assert (forall i, (g' | R R0 R1 i)).
    intros.
    destruct (le_dec i (S t)).
    + generalize i l. apply rev_2_ind.
      * rewrite H. apply divide_0_r.
      * exists (2 ^+ (ord2 (R R0 R1 t))). apply psplit_spec. assumption. lia.
      * intros. destruct k as [| [|k] ]; [assumption|assumption|].
        rewrite !Nat.pred_succ in *.
        eapply Gauss. 
        rewrite R_recurrence'.
        apply divide_sub_r.
        apply divide_mul_r. assumption.
        apply divide_mul_r. assumption.

        apply R_zero.
        
        apply R_S_0_contra. assumption.

        assumption. assumption.
        apply odd_rel_prime_pow.
        pose proof (ord2_even _ (R_even _ _ i R0_nonzero R1_even)). lia. assumption.        
        
    intros.
    destruct (le_dec i (S t)). generalize i l. apply rev_1_ind.

    
    
    
      
