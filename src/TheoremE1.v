Theorem E1 e f (Hf : odd f = true) g (Hg : odd g = true) :
  exists! q, (odd q = true) /\ (1 <= q <= 2 ^+ (S e) - 1) /\ (2 ^+ (S e) | q * g - f).
Proof.
  assert (H1 : 1 < 2 ^+ (S e)) by (apply Zpower_nat_gt1; lia).
  assert (H2 : rel_prime g (2 ^+ (S e))).
  { apply rel_prime_pow; [lia|]; apply Zgcd_1_rel_prime; apply odd_gcd; assumption. }
  apply prime_inv in H2; [destruct H2|lia].
  set (q := (f * x mod 2 ^+ (S e))).
  assert (odd q = true).
  { unfold q. rewrite odd_mod_pow2.
    rewrite odd_mul, Hf, andb_true_l. apply odd_gcd. apply Zgcd_1_rel_prime.
    apply (rel_prime_pow _ _ (S e)). lia. apply prime_inv. lia. exists g. rewrite mul_comm. assumption. lia. }
  exists q. apply and_lemma. 
  - split; [|split].
    + assumption. 
    + assert (q <> 0) by (intro; rewrite H2 in H0; inversion H0).
      assert (q <> 2 ^+ (S e)). intro; rewrite H3 in H0; rewrite odd_pow2 in H0; inversion H0. lia.
      pose proof (mod_pos_bound (f * x) (2 ^+ (S e))); lia.
    + unfold q. apply Zmod_divide. lia.
      rewrite <- Zminus_mod_idemp_l.
      rewrite Zmult_mod_idemp_l. rewrite <- mul_assoc.
      rewrite <- Zmult_mod_idemp_r. rewrite (mul_comm x), H, mul_1_r. 
      rewrite Zminus_mod_idemp_l. rewrite sub_diag, mod_0_l. reflexivity. lia.
  - intros Hq q' Hq'. destruct Hq. destruct H3. destruct Hq'. destruct H6.
    assert (2 ^+ (S e) | q - q'). 
    apply (Gauss _ g). replace (g * (q - q')) with (q * g - f - (q' *g - f)) by ring.
    apply divide_sub_r; assumption. apply rel_prime_sym. apply rel_prime_pow. lia.
    apply Zgcd_1_rel_prime. apply odd_gcd. assumption.
    apply mod_equiv in H8. rewrite !mod_small in H8. assumption. lia. lia. lia. Qed.
