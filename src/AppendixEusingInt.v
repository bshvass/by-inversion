Module using_integers.

Local Notation "f 'div2' g" :=
  ((f * (mod_inv (split2 g) (2 ^ ((ord2 g) + 1)))) mod (2 ^ ((ord2 g) + 1))) (at level 50).

Notation "f 'mod2' g" :=
  (2 ^ (ord2 g) * f - (f div2 g) * g) (at level 50).

Notation "f 'div2_Z' g" :=
  ((f * (mod_inv (split2_Z g) (2 ^ ((ord2_Z g) + 1)))) mod (2 ^ ((ord2_Z g) + 1))) (at level 50).

Notation "f 'mod2_Z' g" :=
  (2 ^ (ord2_Z g) * f - (f div2_Z g) * g) (at level 50).

Lemma div2_mod2 f g :
  (f div2 g) * g = (2 ^ (ord2 g)) * f - (f mod2 g).
Proof. lia. Qed.

Lemma mod2_div2 f g :
  f mod2 g = (2 ^ (ord2 g)) * f - (f div2 g) * g.
Proof. reflexivity. Qed.

Theorem E1 e f (He : 0 <= e) (Hf : odd f = true) g (Hg : odd g = true) :
  exists! q, (odd q = true) /\ (1 <= q <= 2^(e + 1) - 1) /\ (2 ^ (e + 1) | q * g - f).
Proof.
  assert (H1 : 1 < 2 ^ (e + 1)) by (apply pow_gt_1; lia).
  assert (H2 : rel_prime g (2 ^ (e + 1))).
  { apply rel_prime_pow; [lia|]; apply Zgcd_1_rel_prime; apply odd_gcd; assumption. }
  apply prime_inv in H2; [destruct H2|lia].
  set (q := (f * x mod 2 ^ (e + 1))).
  assert (odd q = true).
  { unfold q. rewrite odd_mod_pow2.
    rewrite odd_mul, Hf, andb_true_l. apply odd_gcd. apply Zgcd_1_rel_prime.
    apply (rel_prime_pow _ _ (e + 1)). lia. apply prime_inv. lia. exists g. rewrite mul_comm. assumption. lia. }
  exists q. apply and_lemma. 
  - split; [|split].
    + assumption. 
    + assert (q <> 0) by (intro; rewrite H2 in H0; inversion H0).
      assert (q <> 2 ^ (e + 1)). intro; rewrite H3 in H0; rewrite odd_pow2 in H0; inversion H0. lia.
      pose proof (mod_pos_bound (f * x) (2 ^ (e + 1))); lia.
    + unfold q. apply Zmod_divide. lia.
      rewrite <- Zminus_mod_idemp_l.
      rewrite Zmult_mod_idemp_l. rewrite <- mul_assoc.
      rewrite <- Zmult_mod_idemp_r. rewrite (mul_comm x), H, mul_1_r. 
      rewrite Zminus_mod_idemp_l. rewrite sub_diag, mod_0_l. reflexivity. lia.
  - intros Hq q' Hq'. destruct Hq. destruct H3. destruct Hq'. destruct H6.
    assert (2 ^ (e + 1) | q - q'). 
    apply (Gauss _ g). replace (g * (q - q')) with (q * g - f - (q' *g - f)) by ring.
    apply divide_sub_r; assumption. apply rel_prime_sym. apply rel_prime_pow. lia.
    apply Zgcd_1_rel_prime. apply odd_gcd. assumption.
    apply mod_equiv in H8. rewrite !mod_small in H8. assumption. lia. lia. lia. Qed.

Compute split2 1231231231231232. Compute 4809496996997 * 2 ^ (ord2 1231231231231232).
Compute mod_inv 1231232133 2^123.
Compute 123124 div2 0.

Fixpoint R (R0 R1 : Z) i {struct i} :=
  match i with
  | 0%nat => R0
  | S j => R R1 (- ((split2 R0) mod2 R1)) j
  end.

Fixpoint R_alt (R0 R1 : Z) i {struct i} :=
  match i with
  | 0%nat => R0
  | S j => if (- (split2 R0) mod2 R1 =? 0)
          then R0
          else R R1 (- ((split2 R0) mod2 R1)) j
  end.

Lemma R_S R0 R1 i :
  R R0 R1 (S i) = R R1 (- ((split2 R0) mod2 R1)) i.
Proof. reflexivity. Qed.

Lemma R_S_S R0 R1 i :
  R R0 R1 (S (S i)) = - ((split2 (R R0 R1 i)) mod2 (R R0 R1 (S i))).
Proof.
  revert R0 R1. induction i; intros.
  - simpl; reflexivity.
  - rewrite R_S, IHi; reflexivity. Qed.
  
(* Theorem E2 R0 R1 i : *)
(*   (* 2 ^ (ord2 (R R0 R1 (S i))) * *) *)
(*   R R0 R1 (S (S i)) = *)
(*   - (split2 (R R0 R1 i)) + ((split2 (R R0 R1 i)) div2 R R0 R1 (S i)) * R R0 R1 (S i). *)
(* Proof. *)
(*   rewrite R_S_S.  *)

Theorem E3 R0 R1 t :
  (forall i, (1 <= i)%nat -> even (R R0 R1 i) = true) /\
  (R R0 R1 (t + 1) = 0 -> R R0 R1 = gcd R0 R1).

  
(*   rewrite div2_mod2. simpl. *)
(*   induction i. simpl. rewrite (div2_mod2 R0 (split2 R1)). *)
  
Compute split2 (R 9919 628 8).

Compute gcd 9919 628.

Compute 9919 mod 3.

Compute gcd (13 * 7 * 5 * 123123) (13 * 1234).
Compute split2 (R (13 * 7 * 5 * 123123) (13 * 1234) 9).

Compute gcd 99123123123999 661312312398.

Compute gcd 99999 661398.
Compute R_tail 16 12 11232.
                        

)
          | 0%nat => R1
                    | S k => R_tail ()
            | S (S j)

            |

Compute R 15 28 10.
