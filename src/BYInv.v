Require Import ZArith micromega.Lia.

From BY Require Import Section11 Divstep BigOp MatrixZ Zpower_nat Zlemmas.

Import Z.
Local Open Scope Z.

Definition iterations d :=
  if d <? 46 then (49 * d + 80) / 17 else (49 * d + 57) / 17.

Definition by_inv f g pc :=
  let bits := max (log2_up (abs f)) (log2_up (abs g)) in
  let i := iterations bits in
  let '(_, fm, _, vm, _) := divstep_full_iter 1 f g 0 1 (to_nat i) in
  let sign := if fm <=? 0 then (-1) else 1 in
  sign * pc * vm mod f.

Theorem by_inv_spec f g pc
        (fg_rel_prime : gcd f g = 1)
        (fodd : odd f = true)
        (gnon0 : g <> 0)
        (pc_correct : pc * 2 ^+ (to_nat (iterations (max (log2_up (abs f)) (log2_up (abs g))))) mod f = 1) :
  by_inv f g pc * g mod f = 1.
Proof.
  unfold by_inv.
  
  set (d:= (max (log2_up (abs f)) (log2_up (abs g)))). fold d in pc_correct.
  set (m:= to_nat (iterations d)). fold m in pc_correct.
  
  pose proof divstep_full_iter_spec 1 f g m.
  pose proof _11_2 f g fodd gnon0 (to_nat d) m.

  assert (f ^+ 2 + 4 * g ^+ 2 <= 5 * 4 ^+ (to_nat d)).
  { unfold d in *. 
    destruct (Z_le_dec (abs f) (abs g)).
    
    {
      assert (log2_up (abs f) <= log2_up (abs g)). apply log2_up_le_mono; assumption.
      rewrite max_r by assumption.
      assert (f ^+ 2 + 4 * g ^+ 2 <= g ^+ 2 + 4 * g ^+ 2).
      simpl. nia.
      
      replace 4 with (2 * 2) at 2 by lia. rewrite Zpower_nat_mul.

      destruct (Z.eq_dec (abs g) 1).
      rewrite e in *.
      rewrite log2_up_1 in H0. assert (log2_up (abs f) = 0). pose proof log2_up_nonneg (abs f).
      rewrite log2_up_1 in H1.
      lia. apply log2_up_null in H3.
      
      simpl. nia.
      
      pose proof Zpower_nat_log2_up (abs g) ltac:(lia).
      simpl. nia. }
   {
      assert (log2_up (abs g) <= log2_up (abs f)). apply log2_up_le_mono; lia.
      rewrite max_l by assumption.
      assert (f ^+ 2 + 4 * g ^+ 2 <= f ^+ 2 + 4 * f ^+ 2).
      simpl. nia.
      
      assert (f <> 0) by (apply odd_nonzero; assumption).
      
      replace 4 with (2 * 2) at 2 by lia. rewrite Zpower_nat_mul.

      destruct (eq_dec (abs f) 1).
      rewrite e in *.
      rewrite log2_up_1 in H0. assert (log2_up (abs g) = 0). pose proof log2_up_nonneg (abs g). lia. apply log2_up_null in H4.
      simpl. nia.

      pose proof Zpower_nat_log2_up (abs f) ltac:(lia).
      simpl. nia. } }
  
  pose proof divstep_divstep_full_iter 1 f g 0 1 m.
  destruct (divstep_full_iter) as [[[[? fm] ?] vm] ?] eqn:E3.
  destruct H as [um [qm]].
  
  cbn -[Zpower_nat] in H0.
  rewrite <- H in H0.
  
  apply H0 in H1.
  
  clear H0. destruct H1.  destruct H1.

  unfold fn, gn in *.
  rewrite H2 in *.

  assert (fm = 1 \/ fm = -1). lia.
  destruct H4.
  { subst.
    simpl. rewrite Zmult_mod_idemp_l.
    rewrite <- mul_assoc.
    rewrite <- Zmult_mod_idemp_r.
    rewrite H3. rewrite mul_1_r, mul_1_l.
    rewrite Zmult_mod_idemp_r. apply pc_correct. }
  { subst.
    simpl. rewrite Zmult_mod_idemp_l.
    rewrite <- mul_assoc.
    rewrite <- Zmult_mod_idemp_r.
    rewrite H3.
    rewrite Zmult_mod_idemp_r.
    replace (-1 * pc * (2 ^+ m * -1)) with (pc * 2 ^+ m) by ring.
    apply  pc_correct. }

  unfold m. unfold iterations.
  rewrite !Z2Nat.id.
  destruct (lt_dec (to_nat d) 46).
  assert (d <? 46 = true). apply Z.ltb_lt. lia. rewrite H3. reflexivity.
  assert (d <? 46 = false). apply Z.ltb_ge. lia. rewrite H3. reflexivity.
  pose proof log2_up_nonneg (abs f).
  pose proof le_max_l (log2_up (abs f)) (log2_up (abs g)).

  destruct (d <? 46);  unfold d;  apply div_pos; lia. unfold d. etransitivity. apply (log2_up_nonneg (abs f)).
  apply le_max_l. Qed.
