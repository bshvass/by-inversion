Require Import ZArith Znumtheory Reals micromega.Lra micromega.Lia.

From BY Require Import Rlemmas Zpower_nat SetoidRewrite.

Import Z.

Local Open Scope Z.
Local Open Scope R.

Local Coercion IZR : Z >-> R.

Lemma div_IZR a b : (b | a) -> IZR (a / b) = a%Z / b%Z.
Proof.
  destruct (Z.eq_dec b 0); intros.
  - now subst; rewrite div_0_r, Zdiv_0_r.
  - symmetry; apply eq_div. apply IZR_neq. assumption.
    rewrite <- mult_IZR, Zmult_comm; apply f_equal.
    apply div_exact. assumption. apply Zdivide_mod; assumption. Qed.



Lemma Zpower_nat_IZR a b : IZR (a ^+ b) = a ^ b.
Proof. now rewrite pow_IZR, Zpower_nat_Z. Qed.

Lemma pow2_IZR (a : Z) : (a <> 0)%Z -> 1 <= a ^ 2.
Proof.
  intros.
  pose proof one_IZR_lt1 a.
  destruct (Rle_dec 1 a). nra.
  destruct (Rle_dec a (-1)). nra.
  exfalso. apply H. apply H0. lra. Qed.

Lemma neq_IZR (a b : Z) : IZR a <> IZR b -> a <> b.
Proof. intros H contra; apply H; apply f_equal; assumption. Qed.

Hint Rewrite <- plus_IZR mult_IZR minus_IZR opp_IZR Zpower_nat_IZR : pull_izr.
Hint Rewrite plus_IZR mult_IZR minus_IZR opp_IZR Zpower_nat_IZR : push_izr.


Lemma Rdiv_div a b : (a / b)%Z <= a / b.
Proof.
  destruct (Z.eq_dec b 0); intros.
  - subst; rewrite div_0_r, Zdiv_0_r; reflexivity.
  - assert (IZR b <> 0) by (apply IZR_neq; assumption).
    destruct (Rle_dec b 0).
    + apply Rle_div_neg_r. lra. rewrite <- mult_IZR. apply IZR_le.
      apply mul_div_ge. apply lt_IZR. lra.
    + apply Rle_div_r. lra. rewrite <- mult_IZR. apply IZR_le.
      apply mul_div_le. apply lt_IZR. lra. Qed.

Lemma div_Rdiv (a b : Z) : a / b - 1 <= (a / b)%Z.
Proof.
  enough (a / b <= (a / b)%Z + 1) by lra.
  destruct (Z.eq_dec b 0); intros.
  - subst; rewrite div_0_r, Zdiv_0_r; lra.
  - assert (IZR b <> 0) by (apply IZR_neq; assumption).
    destruct (Rle_dec b 0).
    + apply Rle_div_neg_l. lra. autorewrite with pull_izr. rewrite mul_add_distr_l.
      pose proof div_mod a b n. replace (b * (a / b))%Z with (a - a mod b)%Z by lia.
      pose proof mod_neg_bound a b (ltac:(apply lt_IZR; lra)).
      destruct H1. apply IZR_le in H2.
      apply IZR_lt in H1. autorewrite with push_izr. lra.
    + apply Rle_div_l. lra. autorewrite with pull_izr. rewrite mul_add_distr_l.
      pose proof div_mod a b n. replace (b * (a / b))%Z with (a - a mod b)%Z by lia.
      pose proof mod_pos_bound a b (ltac:(apply lt_IZR; lra)).
      destruct H1. apply IZR_lt in H2.
      apply IZR_le in H1. autorewrite with push_izr. lra. Qed.
