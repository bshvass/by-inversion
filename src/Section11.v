Require Import ZArith.
Require Import List Bool Znumtheory Decidable.
Require Import Rbase Reals QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

From BY Require Import AppendixE AppendixF AppendixG Divstep Zpower_nat Zlemmas Rlemmas IZR Section9 Matrix Spectral Log Floor Section9 Impl.
From BY.Hierarchy Require Import Definitions BigOp.

Import Z.

Local Open Scope Z.

Local Coercion of_nat : nat >-> Z.

Section __.

  Variable f g : Z.
  Hypothesis fodd : odd f = true.
  Hypothesis gnon0 : g <> 0.

  Ltac Rpos :=
    repeat match goal with
           | [ |- (0 <= _ + _)%R] => apply add_pos
           | [ |- (0 <= _ / _)%R] => apply div_pos_pos
           | [ |- (0 <= _ * _)%R] => apply Rlemmas.mul_pos
           | [ |- (0 <= log ?n ?x)%R] => apply log_pos
           end; try lra.

  Ltac Rle_log :=
    repeat match goal with
           | [ |- (_ <= log _ _)%R] => apply log_le_lower_bound
           end; try lra.

  Ltac destruct_if :=
    repeat match goal with
           | [ |- context[if ?x then _ else _]] => destruct x
           end.

  Lemma log45 : (49 * log 4 5 <= 57)%R.
  Proof.
    apply Rle_div_r. lra. apply log_le_upper_bound. lra. lra.
    rewrite <- Rabs_pos_eq. apply le_pow with (n := 49%nat). lia.
    rewrite <- (Rpower_pow _ (Rpower _ _)).
    rewrite Rpower_mult. replace (57 / 49 * INR 49)%R with (INR 57).
    rewrite Rpower_pow. lra. lra. rewrite !INR_IZR_INZ. field. apply Rpower_pos_nonneg. apply Rpower_pos.
  Qed.

  Lemma iterations_bound d :
    floor ((49 * IZR d + 57) / 17) <= (49 * d + 80) / 17.
  Proof.
    apply le_IZR. apply floor_upper_bound.
    assert ((49 * d + 57) / 17 <= ((49 * d + 80) / 17) - 1)%R by lra.
    etransitivity. apply H.
    autorewrite with pull_izr.
    apply div_Rdiv.
  Qed.

  Theorem _11_2 d m (G4 : (log 2 (vec_norm (IZR f, IZR (2 * g)%Z)) > 21)%R) :
    let '(um, vm, qm, rm) := big_mul_rev (fun i => Tn 1 f g i) 0 m in
    f ^+ 2 + 4 * g ^+ 2 <= 5 * 4 ^+ d ->
    (if (lt_dec d 46)%nat then
       (49 * d + 80) / 17 <= m else (49 * d + 57) / 17 <= m) ->
    gn 1 f g m = 0 /\
    abs (fn 1 f g m) = gcd f g /\
    vm * g mod f = 2 ^+ m * (fn 1 f g m) mod f.
  Proof.
    pose proof _9_1_1 1 f g m 0 ltac:(lia) fodd as _911.
    destruct (big_mul_rev (fun i => Tn 1 f g i) 0 m) as [[[um vm] qm] rm] eqn:E.
    intros fgbound mbound.
    pose proof log45.
    pose proof iterations_bound d.
    assert (mbound1 : floor ((49 * d + 57) / 17) <= m).
    { destruct (lt_dec d 46)%nat. lia.
      autorewrite with pull_izr.
      rewrite floor_div. assumption. }

    set (R0 := f). change f with R0 in G4.
    set (R1 := 2 * g). change (2 * g) with R1 in G4.
    assert (gcdeq : gcd R0 g = gcd R0 R1). { unfold R1. rewrite <- gcd_rel_prime. reflexivity. apply odd_gcd. apply fodd. }
    assert (R0_odd : odd R0 = true). { apply fodd. }
    assert (R1_even : even R1 = true). { apply even_mul_2_l. }
    assert (R1_non0 : R1 <> 0). { assert (g <> 0) by (apply gnon0). lia. }
    set (b := (log 2 (vec_norm (IZR R0, IZR R1)))).
    set (n := (to_nat
                 (if Rle_dec b 21
                  then floor (19 * b / 17)
                  else if Rle_dec b 46
                       then floor ((49 * b + 23) / 17)
                       else floor (49 * b / 17)))).


    assert (bpos : (0 <= b)%R).
    { unfold b. Rpos. apply F6. apply vnonzero. right. cbn. change RbaseSymbolsImpl.R0 with (IZR Z0). apply IZR_neq. assumption. }

    assert (eq1 : (Rpower 4 b = (f ^+ 2 + 4 * g ^+ 2)%Z)%R).
    { replace 4%R with (2 * 2)%R by lra. rewrite <- Rpower_mult_distr by lra. unfold b. rewrite Rpower_log. unfold vec_norm.
      rewrite sqrt_sqrt. unfold R0, R1.
      autorewrite with push_izr. lra. nra.
      apply vec_norm_pos_nonneg. apply vnonzero. right. cbn. change RbaseSymbolsImpl.R0 with (IZR Z0). apply IZR_neq. assumption. lra. lra. }

    assert (bbound : (b <= IZR d + log 4 5)%R).
    { apply IZR_le in fgbound. rewrite <- eq1 in fgbound.
      apply log_le_lower_bound in fgbound.
      etransitivity. apply fgbound. autorewrite with push_izr. rewrite log_mult.
      rewrite log_pow. rewrite log_n_n. rewrite INR_IZR_INZ. lra. lra. lra. lra. lra. apply pow_lt. lra. lra. }

    assert (nlem : (n <= m)%nat).
    { replace m with (to_nat (of_nat m)) by lia. apply Z2Nat.inj_le.
      destruct_if; try apply floor_pos.
      Rpos. Rpos. Rpos. lia.
      destruct_if.
      { assert (H1 : floor (19 * b / 17) <= floor (49 * b / 17)).
        { apply floor_inc. nra. }
        assert (H2 : (floor (49 * b / 17)) <= floor (49 * (d + log 4 5) / 17)).
        { apply floor_inc. nra. }
        assert (H3 : floor (49 * (d + log 4 5) / 17) <= floor ((49 * d + 57) / 17)).
        { apply floor_inc. lra. }
        lia. }
      { destruct (lt_dec d 46)%nat.
        { assert (H1 : floor ((49 * b + 23) / 17) <= floor ((49 * (d + log 4 5) + 23) / 17)).
          { apply floor_inc. lra. }
          assert (H2 : floor ((49 * (d + log 4 5) + 23) / 17) <= floor ((49 * d + 80) / 17)).
          { apply floor_inc. lra. }
          rewrite <- floor_div in mbound. autorewrite with push_izr in mbound. lia. }
        { apply Nat.nlt_ge in n1. apply le_INR in n1. rewrite !INR_IZR_INZ in n1. replace (IZR 46%nat) with (IZR 46) in n1 by reflexivity.
          assert (H1 : floor ((49 * b + 23) / 17) <= floor ((49 * d + 23) / 17)).
          { apply floor_inc. lra. }
          assert (floor ((49 * d + 23) / 17) <= floor ((49 * d + 57) / 17)).
          { apply floor_inc. lra. }
          lia. } }
      { assert (floor (49 * b / 17) <= floor (49 * (d + log 4 5) / 17)).
        { apply floor_inc. lra. }
        assert (floor (49 * (d + log 4 5) / 17) <= floor ((49 * d + 57) / 17)).
        { apply floor_inc. lra. }
        lia. } }

    destruct (G6 R0 R1 R0_odd R1_even G4 (* R1_non0 *)) as [x [y eq]]. fold b in eq.
    apply divstep_iter_0' with (m:=m) in eq; [|assumption]. destruct eq as [d'' [f'' eq]].
    assert (f''eq : f'' = fn 1 R0 g m).
    { unfold fn. replace g with (R1 / 2) by (unfold R1; rewrite mul_comm, Z_div_mult_full; lia).
      rewrite eq. reflexivity. }

    - repeat split.
      + unfold gn. replace g with (R1 / 2) by (unfold R1; rewrite mul_comm, Z_div_mult_full; lia).
        rewrite eq. reflexivity.
      + rewrite gcdeq.
        rewrite <- f''eq.
        eapply (proj2 (G3 _ _ R0_odd R1_even)). apply eq.
      + assert (2 ^+ m * fn 1 R0 g m = um * R0 + vm * g).
        rewrite Nat.sub_0_r in _911. inversion_mat _911.
        assumption.
        rewrite H1.
        rewrite <- Zplus_mod_idemp_l.
        rewrite <- (Zmult_mod_idemp_r R0). rewrite mod_same.
        rewrite Z.mul_0_r, mod_0_l, Z.add_0_l.  reflexivity. apply odd_nonzero. assumption.
        apply odd_nonzero. assumption.
  Qed.
End __.
