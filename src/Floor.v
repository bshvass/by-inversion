Require Import Rbase Reals ZArith QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

From BY Require Import Rlemmas IZR.

Local Open Scope Z.
Local Open Scope R.
Local Coercion IZR : Z >-> R.

Definition floor a := ((up a) - 1)%Z.

Ltac lira :=
  lra +
  (autorewrite with push_izr; try apply lt_IZR; lra) +
  (autorewrite with push_izr; try apply le_IZR; lra) +
  (autorewrite with pull_izr;
       match goal with
       | [ |- IZR _ < IZR _ ] => try apply IZR_lt
       | [ |- IZR _ <= IZR _ ] => try apply IZR_le
       end; lia).

Lemma floor_upper_bound a b : a <= b -> IZR (floor a) <= b.
Proof. unfold floor; pose proof archimed a; rewrite minus_IZR; lra. Qed.

Lemma floor_lower_bound a b : b <= a - 1 -> b < IZR (floor a).
Proof. unfold floor; pose proof archimed a; rewrite minus_IZR; lra. Qed.

Lemma floor_spec a : IZR (floor a) <= a /\ (a - 1 < IZR (floor a)).
Proof. split; [apply floor_upper_bound| apply floor_lower_bound]; reflexivity. Qed.

Lemma up0 : up 0 = 1%Z.
Proof. symmetry; apply tech_up; lra. Qed.

Lemma floor0 : floor 0 = 0%Z.
Proof. unfold floor; rewrite up0; lia. Qed.

Lemma floor_eq (r : R) (z : Z) : z <= r -> r < z + 1 -> z = floor r.
Proof. intros. unfold floor. epose proof tech_up r (z + 1) _ _; lia.
       Unshelve. rewrite plus_IZR; lra. rewrite plus_IZR; lra. Qed.

Lemma floor_inc a b : a <= b -> (floor a <= floor b)%Z.
Proof.
  intros; pose proof floor_spec a as [? ?]; pose proof floor_spec b as [? ?].
  apply le_IZR; destruct (Rlt_dec b (floor a + 1)).
  - assert (eq : floor a = floor b) by (apply floor_eq; lra); rewrite eq; lra.
  - lra. Qed.

Lemma floor_inv_inc a b : floor a <= floor b -> a < b + 1.
Proof. pose proof floor_spec a as [? ?]; pose proof floor_spec b as [? ?]; lra. Qed.

Lemma floor_pos a : 0 <= a -> (0 <= floor a)%Z.
Proof. replace 0%Z with (floor 0) at 2 by apply floor0; apply floor_inc. Qed.

Lemma floor_div a b : floor (IZR a / IZR b)%R = (a / b)%Z.
Proof.
  destruct (Z.eq_dec b 0); [subst; rewrite div_0_r, Zdiv.Zdiv_0_r; apply floor0|].
  assert (IZR b <> 0) by (apply IZR_neq; assumption).

  destruct (Znumtheory.Zdivide_dec b a).
  - symmetry; apply floor_eq; rewrite div_IZR; try lra; assumption.
  - unfold floor. enough (((a / b) + 1)%Z = up (a / b)) by lia.
    apply tech_up.
    + apply Rlt_le_trans with (r2 := (a / b) + ((b - a mod b) / b)).
      assert (0 < ((b - a mod b) / b)).
      { destruct (Z_le_dec 0 b).
        { pose proof Z.mod_pos_bound a b ltac:(lia) as [].
          apply div_pos_nonneg; lira. }
        { pose proof Z.mod_neg_bound a b ltac:(lia) as [].
          apply div_neg_nonneg; lira. } }
      lra.
      rewrite <- Rdiv_plus_distr.
      autorewrite with pull_izr. rewrite <- div_IZR.
      rewrite Zdiv.Zmod_eq_full by lia.
      replace (a + (b - (a - a / b * b)))%Z with (b + a / b * b)%Z by lia.
      rewrite Z.div_add, Zdiv.Z_div_same_full by lia. lira.

      rewrite Zdiv.Zmod_eq_full.
      replace (a + (b - (a - a / b * b)))%Z with (b * (1 + a / b))%Z by lia. apply Z.divide_factor_l. lia.
    + pose proof Rdiv_div a b. lira. Qed.
