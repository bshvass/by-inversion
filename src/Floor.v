Require Import Rbase Reals QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

Require Import Rlemmas IZR.

Local Open Scope Z.
Local Open Scope R.
Local Coercion IZR : Z >-> R.

Definition floor a := ((up a) - 1)%Z.

Lemma floor_upper_bound a b : a <= b -> IZR (floor a) <= b.
Proof.
  unfold floor.
  pose proof archimed a. rewrite minus_IZR. lra. Qed.

Lemma floor_lower_bound a b : b <= a - 1 -> b < IZR (floor a).
Proof.
  unfold floor.
  pose proof archimed a. rewrite minus_IZR. lra. Qed.

Lemma floor_spec a : IZR (floor a) <= a /\ (a - 1 < IZR (floor a)).
Proof. split; [apply floor_upper_bound| apply floor_lower_bound]; reflexivity. Qed.

Lemma up0 : up 0 = 1%Z.
Proof. symmetry. apply tech_up. lra. lra. Qed.

Lemma floor0 : floor 0 = 0%Z.
Proof. unfold floor; rewrite up0; lia. Qed.

Lemma floor_eq (r : R) (z : Z) : z <= r -> r < z + 1 -> z = floor r.
Proof. intros. unfold floor. epose proof tech_up r (z + 1) _ _. lia.
       Unshelve. rewrite plus_IZR; lra. rewrite plus_IZR; lra. Qed.

Lemma floor_inc a b : a <= b -> floor a <= floor b.
  intros. pose proof floor_spec a as [? ?]. pose proof floor_spec b as [? ?].
  destruct (Rlt_dec b (floor a + 1)).
  - assert (floor a = floor b).
    apply floor_eq. lra. lra. rewrite H4. lra.
  - lra. Qed.

Lemma floor_incZ a b : a <= b -> (floor a <= floor b)%Z.
  intros. apply le_IZR. apply floor_inc; assumption. Qed.

Lemma floor_inv_inc a b : floor a <= floor b -> a < b + 1.
Proof.
  pose proof floor_spec a as [? ?]. pose proof floor_spec b as [? ?]. lra. Qed.

Lemma floor_pos a : 0 <= a -> 0 <= floor a.
Proof. replace 0 with (IZR (floor 0)) at 2. apply floor_inc. apply IZR_eq. apply floor0. Qed.

Lemma floor_posZ a : 0 <= a -> (0 <= floor a)%Z.
Proof. intros; apply le_IZR; apply floor_pos; assumption. Qed.

Lemma floor_div a b : floor (IZR a / IZR b)%R = (a / b)%Z.
Proof.
  destruct (Z.eq_dec b 0). subst. rewrite div_0_r, Zdiv.Zdiv_0_r. apply floor0.
  assert (IZR b <> 0) by (apply IZR_neq; assumption).

  destruct (Znumtheory.Zdivide_dec b a).
  - symmetry. apply floor_eq. rewrite div_IZR. lra. assumption. rewrite div_IZR. lra. assumption.
  - unfold floor.
    enough (((a / b) + 1)%Z = up (a / b)). lia.
    apply tech_up. apply Rlt_le_trans with (r2 := (a / b) + ((b - a mod b) / b)).
    assert (0 < ((b - a mod b) / b)).
    destruct (Rle_dec 0 b).
    apply div_pos_nonneg. rewrite <- minus_IZR.
    apply IZR_lt. pose proof Z.mod_pos_bound a b ltac:(apply lt_IZR; lra). lia. lra.
    apply div_neg_nonneg. rewrite <- minus_IZR.
    apply IZR_lt. pose proof Z.mod_neg_bound a b ltac:(apply lt_IZR; lra). lia. lra.
  
    lra.
    
    rewrite <- Rdiv_plus_distr. rewrite <- minus_IZR, <- plus_IZR, <- div_IZR. apply IZR_le.
    rewrite Zdiv.Zmod_eq_full.
    replace (a + (b - (a - a / b * b)))%Z with (b + a / b * b)%Z by lia.
    rewrite Z.div_add. rewrite Zdiv.Z_div_same_full. lia. lia. lia. lia.

    rewrite Zdiv.Zmod_eq_full.
    replace (a + (b - (a - a / b * b)))%Z with (b * (1 + a / b))%Z by lia. apply Z.divide_factor_l. lia.
    rewrite plus_IZR. pose proof Rdiv_div a b. lra. Qed.
