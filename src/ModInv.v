From Coq Require Import ZArith Znumtheory micromega.Lia.

From BY Require Import InductionPrinciples Zlemmas.

Local Open Scope Z.
Import Z.

Fixpoint eea_aux n r0 x0 y0 r1 x1 y1 :=
  match n with
  | 0%nat => (0,0)
  | S n => if r0 mod r1 =? 0
          then (x1, y1)
          else eea_aux n r1 x1 y1 (r0 mod r1) (x0 - (r0 / r1) * x1) (y0 - (r0 / r1) * y1)
  end.

Definition eea a b :=
  if (a =? 0) then (0, sgn b) else
    if (b =? 0) then (sgn a, 0) else
      if (abs b <=? abs a)
      then let (x, y) := eea_aux (to_nat (2 * log2 (abs b) + 1)) (abs a) 1 0 (abs b) 0 1 in
           ((sgn a) * x, (sgn b) * y)
      else let (y, x) := eea_aux (to_nat (2 * log2 (abs a) + 1)) (abs b) 1 0 (abs a) 0 1 in
           ((sgn a) * x, (sgn b) * y).

Lemma eea_aux_spec n a b r0 x0 y0 r1 x1 y1
      (Hn : 2 * log2 r1 < of_nat n)
      (H : 0 < r1 <= r0)
      (H0 : r0 = a * x0 + b * y0)
      (H1 : r1 = a * x1 + b * y1)
      (Hd : gcd r0 r1 = gcd a b) :
  let (x, y) := eea_aux n r0 x0 y0 r1 x1 y1 in
  a * x + b * y = gcd a b.
Proof.
  revert Hn H H0 H1 Hd.
  revert r0 x0 y0 r1 x1 y1.
  induction n using induction2; intros r0 x0 y0 r1 x1 y1 bound dec inv0 inv1 inv_gcd.
  - pose proof log2_nonneg r1; lia.
  - simpl. destruct (eqb_spec (r0 mod r1) 0).
    + rewrite <- inv1, <- inv_gcd, gcd_comm, <- gcd_mod by lia.
      rewrite e, gcd_0_l; lia.
    + assert (log2 r1 = 0). pose proof log2_nonneg r1; nia.
      apply log2_null in H. assert (r1 = 1) by lia.
      rewrite H0 in *. 
      rewrite mod_1_r in n. contradiction.
  - simpl. destruct (eqb_spec (r0 mod r1) 0).
    + rewrite <- inv1, <- inv_gcd, gcd_comm, <- gcd_mod by lia.
      rewrite e, gcd_0_l; lia.
    + pose proof mod_pos_bound r0 r1 ltac:(lia).
      destruct (eqb_spec (r1 mod (r0 mod r1)) 0).
      * rewrite <- inv_gcd, gcd_comm, <- 2!gcd_mod by lia. 
        rewrite e, gcd_0_l, abs_eq by (pose proof mod_pos_bound r0 r1; lia).
        replace (_ + _) with (r0 - r1 * (r0 / r1)) by lia.
        rewrite mod_eq by lia. reflexivity. 
      * apply IHn.
        ** pose proof mod_half r1 (r0 mod r1) ltac:(lia).
           pose proof log2_half r1 ltac:(lia) as [].
           *** apply log2_le_mono in H0; lia.
           *** rewrite H1, mod_1_r, Zdiv.Zmod_0_r in n1. contradiction.
        ** pose proof mod_pos_bound r1 (r0 mod r1).
           lia.
        ** replace (_ + _) with (r0 - r1 * (r0 / r1)) by lia.
           rewrite mod_eq. reflexivity. lia.
        ** rewrite mod_eq.
           replace (_ + _) with (r1 - (r0 - r1 * (r0 / r1)) * (r1 / (r0 mod r1))) by lia.
           rewrite <- (mod_eq r0). reflexivity. lia. lia.
        ** rewrite gcd_comm, !gcd_mod, gcd_comm. assumption. lia. lia. Qed.

Lemma eea_spec a b :
  let (x, y) := eea a b in a * x + b * y = gcd a b.
Proof.
  unfold eea.
  destruct (eqb_spec a 0), (eqb_spec b 0); subst.
  - reflexivity.
  - rewrite gcd_0_l, (sgn_abs b); lia.
  - rewrite gcd_0_r, (sgn_abs a); lia.
  - destruct (leb_spec (abs b) (abs a)).
    + unshelve epose proof (eea_aux_spec (to_nat (2 * log2 (abs b) + 1))
                                         (abs a)
                                         (abs b)
                                         (abs a) 1 0
                                         (abs b) 0 1
                                         _ _ _ _ _); try lia.
      * destruct eea_aux as [x y]. rewrite <- gcd_abs_l, <- gcd_abs_r, <- H0.
        rewrite !mul_assoc, !sgn_abs. reflexivity.
    + unshelve epose proof (eea_aux_spec (to_nat (2 * log2 (abs a) + 1))
                                         (abs b)
                                         (abs a)
                                         (abs b) 1 0
                                         (abs a) 0 1
                                         _ _ _ _ _); try lia.
      * destruct eea_aux as [y x]. rewrite <- gcd_abs_l, <- gcd_abs_r, gcd_comm, <- H0.
        rewrite !mul_assoc, !sgn_abs. lia. Qed.

Definition mod_inv n m := fst (eea n m).

Lemma mod_inv_spec n m (H : rel_prime n m) (Hm : 1 < m) : n * (mod_inv n m) mod m = 1.
Proof.
  unfold mod_inv; pose proof eea_spec n m.
  apply Zgcd_1_rel_prime in H; rewrite H in *.
  destruct eea as [x y]; simpl; replace (n * x) with (1 - m * y) by lia.
  rewrite <- Zminus_mod_idemp_r, <- Zmult_mod_idemp_l.
  rewrite Z_mod_same_full, mul_0_l, mod_0_l, sub_0_r.
  rewrite mod_small. reflexivity. lia. lia. Qed.

Lemma prime_inv a m (Hm1 : 1 < m) : rel_prime a m <-> exists b, a * b mod m = 1.
Proof.
  split; intro. 
  - apply rel_prime_bezout in H. destruct H.
    exists u. replace (a * u) with (1 + - v * m) by lia.
    rewrite <- add_mod_idemp_r. rewrite <- mul_mod_idemp_r.
    rewrite mod_same. rewrite mul_0_r. simpl. rewrite mod_small. reflexivity.
    lia. lia. lia. lia.
  - destruct H. rewrite Zdiv.Zmod_eq_full in H.
    apply bezout_rel_prime. rewrite <- H. apply Bezout_intro with x (- (a * x / m)). ring. lia. Qed.
