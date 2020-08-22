From Coq Require Import ZArith Znumtheory micromega.Lia.

From BY Require Import Zpower_nat Zlemmas.

Local Open Scope Z.
Import Z.

Fixpoint pval_aux n p a :=
  match n with
  | 0%nat => 0%nat
  | S n => if a mod p =? 0
          then S (pval_aux n p (a / p))
          else 0%nat
  end.

Lemma pval_aux_spec n p a
      (H : log2 a < of_nat n)
      (Hp : 1 < p)
      (Ha : 0 < a) :
  (p ^+ (pval_aux n p a) | a) /\ ~ (p ^+ (S (pval_aux n p a)) | a).
Proof.
  revert H Hp Ha. revert p a.
  induction n; intros.
  - pose proof Z.log2_nonneg a. lia.
  - cbn [pval_aux]; destruct (Z.eqb_spec (a mod p) 0).
    + pose proof log2_div a p ltac:(lia) ltac:(lia).
      destruct H0. 
      * assert (0 < a / p) by (rewrite mod_eq in e; nia).
        specialize (IHn p (a / p) ltac:(lia) ltac:(lia) ltac:(lia)).
        rewrite !Zpower_nat_succ_r. 
        split.
        ** apply divide_lemma. lia. apply mod_divide; lia. tauto.
        ** intro. apply divide_lemma in H2. tauto. lia. apply mod_divide. lia. lia.
      * subst. rewrite Z.mod_1_l in e. lia. lia.
    + rewrite Zpower_nat_0_r, Zpower_nat_1_r. split.
      * apply Z.divide_1_l.
      * intro. apply mod_divide in H0. lia. lia. Qed.

Definition pval p a :=
  pval_aux (S (to_nat (log2 (abs a)))) p (abs a).

Lemma pval_spec p a (Ha : a <> 0) (Hp : 1 < p) :
  (p ^+ (pval p a) | a) /\ ~ (p ^+ (S (pval p a)) | a).
Proof.
  pose proof Z.log2_nonneg (abs a).
  unfold pval. rewrite <- divide_abs_r, <- (divide_abs_r _ a).
  apply pval_aux_spec; [rewrite <- Z2Nat.inj_succ, Z2Nat.id by lia| |]; lia. Qed.

Lemma pval_unique p a v (Ha : a <> 0) (Hp : 1 < p) :
  (p ^+ v | a) /\ ~ (p ^+ (S v) | a) -> pval p a = v.
Proof.
  pose proof pval_spec p a Ha Hp as [].
  intros [].
  destruct (le_dec (pval p a) v)%nat.
  - destruct (le_dec v (pval p a))%nat; [lia|].
    assert (p ^+ (S (pval p a)) | a).
    { etransitivity. exists (p ^+ (v - S (pval p a))). reflexivity.
      rewrite <- Zpower_nat_is_exp. rewrite Nat.sub_add. assumption. lia. }
    contradiction.
  - assert (p ^+ (S v) | a).
    { etransitivity. exists (p ^+ ((pval p a) - (S v))). reflexivity.
      rewrite <- Zpower_nat_is_exp. rewrite Nat.sub_add. assumption. lia. }
    contradiction. Qed.

Lemma pval_full_spec p a v (Ha : a <> 0) (Hp : 1 < p) :
  pval p a = v <-> (p ^+ v | a) /\ ~ (p ^+ (S v) | a).
Proof. split; [intros <-; apply pval_spec; assumption|apply pval_unique; assumption]. Qed.

Lemma pval_lower_bound p a n (Ha : a <> 0) (Hp : 1 < p) : (p ^+ (S n) | a) -> (n < pval p a)%nat.
Proof.
  intros.
  destruct (lt_dec n (pval p a)); [assumption|].
  pose proof pval_spec p a Ha Hp as [].
  replace (S n) with (S (pval p a) + ((S n) - S (pval p a)))%nat in H.
  rewrite Zpower_nat_is_exp in H. apply divide_mul_l_l in H. contradiction. lia. Qed.
  
Lemma pval_opp p a : pval p (-a) = pval p a.
Proof. unfold pval. rewrite abs_opp. reflexivity. Qed.

Definition psplit p a := a / (p ^+ (pval p a)).

Lemma psplit_opp p a (Ha : a <> 0) (Hp : 1 < p) : - psplit p a = psplit p (-a).
Proof.
  unfold psplit. rewrite Z_div_zero_opp_full, pval_opp. reflexivity.
  rewrite pval_opp. apply mod_divide. apply Zpower_nat_nonzero. lia.
  apply pval_spec. assumption. assumption. Qed.

Lemma psplit_spec p a (Ha : a <> 0) (Hp : 1 < p): a = (p ^+ (pval p a)) * psplit p a /\ ~ (p | psplit p a).
Proof.
  unfold psplit. 
  pose proof pval_spec p a ltac:(assumption) ltac:(assumption).
  destruct H. 
  split.
  - assert (p ^+ pval p a <> 0) by (apply Zpower_nat_nonzero; lia).
    rewrite div_exact by assumption. apply mod_divide; assumption. 
  - rewrite divide_lemma. rewrite Zpower_nat_mul_r. assumption. 
    apply Zpower_nat_pos_nonneg. lia. assumption. Qed.

Lemma psplit_spec' p a (Ha : a <> 0) (Hp : 1 < p) : a = (p ^+ (pval p a)) * psplit p a.
Proof. apply psplit_spec; assumption. Qed.

Lemma psplit_0 p (Hp : p <> 0) : psplit p 0 = 0.
Proof. unfold psplit; rewrite Z.div_0_l. reflexivity. apply Zpower_nat_nonzero. assumption. Qed.
