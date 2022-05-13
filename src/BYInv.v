Require Import ZArith micromega.Lia Reals micromega.Lra.

From BY Require Import Section11 Divstep Matrix Impl Zpower_nat Zlemmas Spectral Tactics ModInv.
From BY.Hierarchy Require Import Definitions BigOp.

Import Z.
Local Open Scope Z_scope.

Definition by_inv_full f g its pc :=
  let '(_, fm, _, vm, _) := Nat.iter its (divstep_vr_mod f) (1, f, g, 0, 1)  in
  let sign := if fm <? 0 then (-1) else 1 in
  sign * pc * vm mod f.

Definition iterations d :=
  if d <? 46 then (49 * d + 80) / 17 else (49 * d + 57) / 17.
Definition jump_iterations b mw :=
  ((iterations b) / (mw - 2)) + 1.

Definition by_inv_ref f g :=
  let bits := (log2 f) + 1 in
  let its := iterations bits in
  let k := (f + 1) / 2 in
  let pc := (k ^+ (to_nat its)) mod f in
  by_inv_full f g (to_nat its) pc.

Definition by_inv_jump_full mw f g n its pc :=
  let '(_, fm, _, vm, _) := Nat.iter its (jump_divstep n mw f) (1, f, g, 0, 1)  in
  let sign := if fm <? 0 then (-1) else 1 in
  sign * pc * vm mod f.

Definition by_inv_jump_ref mw f g :=
  let bits := (log2 f) + 1 in
  let jump_its := jump_iterations bits mw in
  let total_iterations := jump_its * (mw - 2) in
  let k := (f + 1) / 2 in
  let pc := (k ^+ (to_nat total_iterations)) mod f in
  by_inv_jump_full mw f g (to_nat (mw - 2)%Z) (to_nat jump_its) pc.

Lemma odd_inv2 a (Ha : 1 < a) : odd a = true -> ((a + 1) / 2 * 2) mod a = 1.
Proof.
  intros.
  rewrite Z.mul_comm.
  rewrite <- Znumtheory.Zdivide_Zdiv_eq.
  rewrite <- Zplus_mod_idemp_l.
  rewrite Z.mod_same.
  rewrite Z.add_0_l.
  rewrite Z.mod_1_l.
  reflexivity.
  assumption. lia.
  lia.
  apply even_div.
  rewrite even_add.
  rewrite <- negb_odd.
  rewrite H. reflexivity.
Qed.

Lemma exp_inv n a b c : 1 < c -> (a * b) mod c = 1 -> (a ^+ n) * (b ^+ n) mod c = 1.
Proof.
  intros.
  induction n.
  - simpl.
    rewrite Z.mul_1_l.
    rewrite Z.mod_1_l.
    reflexivity. assumption.
  - simpl.
    replace (a * a ^+ n * (b * b ^+ n)) with ((a * b) * ((a ^+ n) * (b ^+ n))) by lia.
    rewrite <- Zmult_mod_idemp_l.
    rewrite <- Zmult_mod_idemp_r.
    rewrite H0, IHn.
    rewrite Z.mul_1_l.
    rewrite Z.mod_1_l.
    reflexivity. assumption.
Qed.

Lemma Zpower_nat_succ_log2 a : 0 < a -> a < 2 ^+ (Z.to_nat ((Z.log2 a) + 1)).
Proof. rewrite Zpower_nat_Z, Z2Nat.id. apply Z.log2_spec. pose proof Z.log2_nonneg a. lia. Qed.

Lemma bits_lemma f g (fodd : odd f = true) (gnon0 : g <> 0) :
  f ^+ 2 + 4 * g ^+ 2 <= 5 * 4 ^+ (to_nat (max ((log2 (abs f)) + 1) ((log2 (abs g)) + 1))).
Proof.
    destruct (Z_le_dec (abs f) (abs g)).
    {
      assert (log2 (abs f) + 1 <= log2 (abs g) + 1).
      apply Zplus_le_compat_r.
      apply log2_le_mono. assumption.
      rewrite max_r by assumption.
      assert (f ^+ 2 + 4 * g ^+ 2 <= g ^+ 2 + 4 * g ^+ 2).
      simpl. nia.

      replace 4 with (2 * 2) at 2 by lia. rewrite Zpower_nat_mul.

      destruct (Z.eq_dec (abs g) 1).
      rewrite e in *.
      rewrite log2_1 in H. assert (log2 (abs f) = 0).
      pose proof log2_nonneg (abs f).
      (* rewrite log2_up_1 in H. *)
      lia. apply log2_null in H1.

      simpl. nia.
      pose proof Zpower_nat_succ_log2 (abs g) ltac:(lia).
      simpl. nia. }
   {
      assert (log2 (abs g) + 1 <= log2 (abs f) + 1).
      apply Zplus_le_compat_r.
      apply log2_le_mono. lia.
      rewrite max_l by assumption.
      assert (f ^+ 2 + 4 * g ^+ 2 <= f ^+ 2 + 4 * f ^+ 2).
      simpl. nia.

      assert (f <> 0) by (apply odd_nonzero; assumption).

      replace 4 with (2 * 2) at 2 by lia. rewrite Zpower_nat_mul.

      destruct (eq_dec (abs f) 1).
      rewrite e in *.
      rewrite log2_1 in H. assert (log2 (abs g) = 0). pose proof log2_nonneg (abs g). lia. apply log2_null in H2.
      simpl. nia.

      pose proof Zpower_nat_succ_log2 (abs f) ltac:(lia).
      simpl. nia. }
Qed.

Lemma vec_norm_lower_bound_l (a b : R) :
  (0 <= a -> a <= vec_norm (a, b))%R.
Proof.
  unfold vec_norm. intros.
  rewrite <- (sqrt_pow2 a) at 1 by assumption.
  apply sqrt_le_1_alt.
  pose proof pow2_ge_0 b.
  lra.
Qed.

Lemma vec_norm_Rabs_l (a b : R) :
  (vec_norm (a, b) = vec_norm (Rabs a, b))%R.
Proof. unfold vec_norm. rewrite pow2_abs. reflexivity. Qed.

Lemma weaken_g4 f g :
  (22 < log2 (abs f) + 1) -> (21 < Log.log 2 (vec_norm (IZR f, (IZR (2 * g)))))%R.
Proof.
  intros.
  eapply Rlt_le_trans with (r2:=IZR (log2 (abs f))).
  apply IZR_lt. lia.
  apply Log.Rpower_le_inv with (n:=2%R). lra.
  rewrite <- powerRZ_Rpower.

  rewrite Log.Rpower_log.
  eapply Rle_trans.
  replace (log2 (abs f)) with (of_nat (to_nat (log2 (abs f)))).

  replace 2%R with (INR 2).

  rewrite <- Zpower_nat_powerRZ.
  replace (of_nat 2) with 2 by lia.
  eapply IZR_le.
  eapply Zpower_nat_log2.
  destruct (decide (abs f <= 0)).
  - apply log2_nonpos in l. lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite vec_norm_Rabs_l. eapply Rle_trans. 2: apply vec_norm_lower_bound_l.
    rewrite abs_IZR. lra.
    apply Rabs_pos.
  - apply vec_norm_pos_nonneg.
    cbn.
    simpl. unfold prod_equiv.
    unfold prod_relation.
    simpl.
    intros [H2 H3].
    assert (f = 0).
    apply eq_IZR. lra.
    rewrite H0 in H.
    pose proof log2_null (abs 0).
    lia.
  - lra.
  - lra.
  - lra.
Qed.

Lemma iterations_lemma f g :
  let bits := (max ((log2 (abs f)) + 1) ((log2 (abs g)) + 1)) in
  (if lt_dec
        (to_nat bits) 46
   then (49 * of_nat
                (to_nat bits) + 80) / 17 <=
          of_nat (to_nat (iterations bits))
   else (49 * of_nat (to_nat bits) + 57) / 17 <=
          of_nat (to_nat (iterations bits))).
Proof.
  unfold iterations.
  set (d := (max (log2 (abs f) + 1) (log2 (abs g) + 1))).
  rewrite !Z2Nat.id.
  destruct (lt_dec (to_nat d) 46).
  assert (d <? 46 = true). apply Z.ltb_lt. lia.
  rewrite H. reflexivity.
  assert (d <? 46 = false). apply Z.ltb_ge. lia.
  rewrite H. reflexivity.
  pose proof log2_nonneg (abs f).
  pose proof le_max_l (log2 (abs f)) (log2 (abs g)).

  destruct (d <? 46); unfold d; apply div_pos; lia.
  unfold d. etransitivity. apply (log2_nonneg (abs f)). lia.
Qed.

Lemma iterations_pos i :
  (0 <= i) -> 0 <= iterations i.
Proof.
  intros.
  unfold iterations.
  destruct (i <? 46).
  - apply Z_div_pos. lia. lia.
  - apply Z_div_pos. lia. lia.
Qed.

Lemma jump_iterations_lemma f g mw
      (mw_bound : (2 < mw)) :
  if lt_dec (to_nat (max (log2 (abs f) + 1) (log2 (abs g) + 1))) 46
  then
   (49 * of_nat (to_nat (max (log2 (abs f) + 1) (log2 (abs g) + 1))) + 80) / 17 <=
   of_nat (to_nat (iterations (max (log2 (abs f) + 1) (log2 (abs g) + 1)) / (mw - 2) + 1) * to_nat (mw - 2))
  else
   (49 * of_nat (to_nat (max (log2 (abs f) + 1) (log2 (abs g) + 1))) + 57) / 17 <=
   of_nat (to_nat (iterations (max (log2 (abs f) + 1) (log2 (abs g) + 1)) / (mw - 2) + 1) * to_nat (mw - 2)).
Proof.
  unfold iterations.
  set (d := (max (log2 (abs f) + 1) (log2 (abs g) + 1))).
  assert (0 <= d).
  { unfold d. apply max_le_iff. left.
    pose proof log2_nonneg (abs f). lia. }
  assert (0 <= ((49 * d + 80) / 17 / (mw - 2))).
  {  apply Z_div_pos. lia.
     apply Z_div_pos. lia. nia. }
  assert (0 <= (49 * d + 57) / 17 / (mw - 2)).
  {  apply Z_div_pos. lia.
     apply Z_div_pos. lia. lia. }
  destruct (lt_dec (to_nat d) 46).
  assert (d <? 46 = true). apply Z.ltb_lt. lia.
  rewrite H2.
  rewrite <- Z2Nat.inj_mul.
  rewrite add_1_r.
  rewrite (Z.mul_comm _ (mw - 2)).
  rewrite !Z2Nat.id.
  apply lt_le_incl.
  apply mul_succ_div_gt. lia. nia. lia. lia.  lia.

  assert (d <? 46 = false). apply Z.ltb_ge. lia.
  rewrite H2.
  rewrite <- Z2Nat.inj_mul.
  rewrite add_1_r.
  rewrite (Z.mul_comm _ (mw - 2)).
  rewrite !Z2Nat.id.
  apply lt_le_incl.
  apply mul_succ_div_gt. lia. nia. lia. lia. lia.
Qed.

Theorem by_inv_full_spec f g its pc
        (G4 : (21 < Log.log 2 (vec_norm (IZR f, (IZR (2 * g)))))%R)
        (f_bound : 1 < f)
        (its_bound :   (if lt_dec (to_nat (max (log2 (abs f) + 1) (log2 (abs g) + 1))) 46
                        then (49 * of_nat (to_nat (max (log2 (abs f) + 1) (log2 (abs g) + 1))) + 80) / 17 <=
                               of_nat its
                        else (49 * of_nat (to_nat (max (log2 (abs f) + 1) (log2 (abs g) + 1))) + 57) / 17 <=
                               of_nat its))
        (fodd : odd f = true)
        (fg_rel_prime : gcd f g = 1)
        (gnon0 : g <> 0)
        (pc_correct : pc * 2 ^+ its mod f = 1) :
  by_inv_full f g its pc * g mod f = 1.
Proof.
  unfold by_inv_full.
  pose proof bits_lemma f g fodd gnon0.

  set (d:= (max (log2 (abs f) + 1) (log2 (abs g) + 1))) in *.

  rewrite iter_divstep_vr_iter_divstep_vr_mod.

  pose proof divstep_full_iter_spec 1 f g its.
  pose proof _11_2 f g fodd gnon0 (to_nat d) its ltac:(lra).
  pose proof iter_divstep_vr_iter_divstep 1 f g 0 1 its.
  unfold fn, gn in *.
  destruct (Nat.iter _ _ _) as [[[[? fm] ?] vm] ?].
  rewrite Zmult_mod_idemp_r.
  destruct H0 as [um [qm]].
  split_pairs.
  apply H1 in H.
  split_pairs.
  cbn in *. subst.

  assert (fm = 1 \/ fm = -1) as [] by lia.
  { subst; cbn. rewrite Zmult_mod_idemp_l, <- mul_assoc, <- Zmult_mod_idemp_r, H2, mul_1_r, mul_1_l, Zmult_mod_idemp_r. apply pc_correct. }
  { subst; cbn. rewrite Zmult_mod_idemp_l, <- mul_assoc, <- Zmult_mod_idemp_r, H2, Zmult_mod_idemp_r.
    replace (-1 * pc * (2 ^+ its * -1)) with (pc * 2 ^+ its) by ring.
    apply pc_correct. }
  assumption. lia. lia.
Qed.

Theorem by_inv_spec f g
        (f_bound : (21 < log2 f))
        (g_bound : 0 < g <= f)
        (fg_rel_prime : gcd f g = 1)
        (fodd : odd f = true) :
  by_inv_ref f g * g mod f = 1.
Proof.
  unfold by_inv_ref.
  assert (1 < f).
  { apply log2_lt_cancel. simpl. lia. }
  replace (log2 f) with (log2 (abs f)) by (f_equal; lia).
  assert (log2 (abs f) + 1 = max (log2 (abs f) + 1) (log2 (abs g) + 1)).
  { symmetry. apply max_l.
    apply Zplus_le_compat_r.
    apply log2_le_mono.
    rewrite !abs_eq. lia. lia. lia. }
  rewrite H0.
  apply by_inv_full_spec.
  apply weaken_g4. rewrite abs_eq. lia. lia. lia.
  apply iterations_lemma. 1-2: assumption. lia.
  rewrite Zmult_mod_idemp_l.
  eapply exp_inv. lia.
  rewrite odd_inv2. reflexivity. lia. assumption.
Qed.

Theorem by_inv_jump_full_spec f g n mw its pc
        (G4 : (21 < Log.log 2 (vec_norm (IZR f, (IZR (2 * g)))))%R)
        (f_bound : 1 < f)
        (mw_bouns : of_nat n < mw)
        (its_bound :   (if lt_dec (to_nat (max (log2 (abs f) + 1) (log2 (abs g) + 1))) 46
                        then (49 * of_nat (to_nat (max (log2 (abs f) + 1) (log2 (abs g) + 1))) + 80) / 17 <=
                               of_nat (its * n)
                        else (49 * of_nat (to_nat (max (log2 (abs f) + 1) (log2 (abs g) + 1))) + 57) / 17 <=
                               of_nat (its * n)))
        (fodd : odd f = true)
        (fg_rel_prime : gcd f g = 1)
        (gnon0 : g <> 0)
        (pc_correct : pc * 2 ^+ (its * n) mod f = 1) :
  by_inv_jump_full mw f g n its pc * g mod f = 1.
Proof.
  unfold by_inv_jump_full.
  rewrite iter_jump_divstep_spec. all: try lia; try assumption.
  apply by_inv_full_spec. all: assumption.
Qed.

Theorem by_inv_jump_spec f g mw
        (f_bound : (21 < log2 f))
        (g_bound : 0 < g <= f)
        (mw_bound : 2 < mw)
        (fg_rel_prime : gcd f g = 1)
        (fodd : odd f = true) :
  by_inv_jump_ref mw f g * g mod f = 1.
Proof.
  unfold by_inv_jump_ref.
  assert (1 < f).
  { apply log2_lt_cancel. simpl. lia. }
  replace (log2 f) with (log2 (abs f)) by (f_equal; lia).
  assert (log2 (abs f) + 1 = max (log2 (abs f) + 1) (log2 (abs g) + 1)).
  { symmetry. apply max_l.
    apply Zplus_le_compat_r.
    apply log2_le_mono.
    rewrite !abs_eq. lia. lia. lia. }
  rewrite H0.
  apply by_inv_jump_full_spec.
  apply weaken_g4. rewrite abs_eq. lia. lia. lia. lia.
  apply jump_iterations_lemma. lia. assumption. assumption. lia.
  rewrite Zmult_mod_idemp_l.
  rewrite <- Z2Nat.inj_mul.
  eapply exp_inv. lia.
  rewrite odd_inv2. reflexivity. lia. assumption.

  rewrite <- H0.
  assert (0 <= iterations (log2 (abs f) + 1) / (mw - 2)).
  { apply Z_div_pos. lia.
    apply iterations_pos.
    rewrite abs_eq. pose proof log2_nonneg f. lia. lia. }
  unfold jump_iterations.
  lia.
  lia.
Qed.

Print Assumptions by_inv_spec.
