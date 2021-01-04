From Coq Require Import Bool ZArith Znumtheory micromega.Lia.

From BY Require Import Zpower_nat InductionPrinciples.

Local Open Scope Z.

Import Z.

Lemma mod_pos a b (H : 0 <= b) : 0 <= a mod b.
  destruct (Z.eq_dec 0 b); [subst; rewrite Zmod_0_r|apply mod_pos_bound]; lia. Qed.

Lemma mod_pos_wbound a b (H : 0 <= b) : 0 <= a mod b <= b.
  split; [apply mod_pos; lia|].
  destruct (Z.eq_dec 0 b); [subst; rewrite Zmod_0_r|pose proof mod_pos_bound a b ltac:(lia)]; lia. Qed.

Lemma mod_neg a b (H : b <= 0) : a mod b <= 0.
  destruct (Z.eq_dec 0 b); [subst; rewrite Zmod_0_r|apply mod_neg_bound]; lia. Qed.

Lemma mod_neg_wbound a b (H : b <= 0) : b <= a mod b <= 0.
  split; [|apply mod_neg; lia].
  destruct (Z.eq_dec 0 b); [subst; rewrite Zmod_0_r|pose proof mod_neg_bound a b ltac:(lia)]; lia. Qed.

Lemma mod_lemma a b (H : b <= a < 2*b) : a mod b = a - b.
Proof.
  symmetry; destruct (Z_le_dec b 0); [apply mod_unique_neg with 1|apply mod_unique_pos with 1]; lia. Qed.

Lemma mod_half a b (H : 0 <= b <= a) : a mod b <= a / 2.
Proof.
  destruct (eq_dec b 0) as [->|?].
  - rewrite Zdiv.Zmod_0_r. apply div_pos; lia.
  - pose proof (mod_pos_bound a b ltac:(lia)).
    pose proof (mul_succ_div_gt a 2 ltac:(lia)).
    destruct (ltb_spec b (succ (a / 2))).
    + lia.
    + assert (a < 2*b) by lia.
      rewrite mod_lemma; lia. Qed.

Lemma log2_half a (H : 0 < a) : log2 (a / 2) = log2 a - 1 \/ a = 1.
Proof.
  rewrite <- div2_div, div2_spec, log2_shiftr by assumption.
  unfold max; destruct (compare_spec 0 (log2 a - 1)); auto.
  - right; assert (log2 a = 0) by (pose proof log2_nonneg a; lia).
    apply log2_null in H1; lia. Qed.

Lemma even_mul_2_l a : even (2 * a) = true.
Proof. rewrite even_mul; reflexivity. Qed.

Lemma even_mul_2_r a : even (a * 2) = true.
Proof. rewrite mul_comm; apply even_mul_2_l. Qed.

Lemma even_divide a : even a = true <-> (2 | a).
Proof.
  split.
  - intros. apply even_spec in H. destruct H as [x]. exists x; lia.
  - intros [x ->]. apply even_mul_2_r. Qed.

Lemma odd_gcd a : odd a = true <-> gcd a 2 = 1.
Proof.
  split; intros.
  - rewrite odd_spec in H. rewrite <- Zodd_equiv in H. apply Zodd_ex in H.
    destruct H. rewrite H. rewrite gcd_comm.
    rewrite add_comm, mul_comm. rewrite gcd_add_mult_diag_r. reflexivity.
  - apply gcd_bezout in H. destruct H. destruct H.
    apply (f_equal odd) in H.
    rewrite odd_add, !odd_mul in H. simpl in H.
    destruct (odd a); rewrite !andb_false_r in H; easy. Qed.

Lemma odd_rel_prime a : odd a = true <-> rel_prime a 2.
Proof. pose proof Zgcd_1_rel_prime a 2; pose proof odd_gcd a; tauto. Qed.

Lemma rel_prime_pow a b n (Hn : (1 <= n)%nat) : rel_prime a b <-> rel_prime a (b ^+ n).
Proof.
  split; intro.
  - induction n.
    + apply rel_prime_sym; apply rel_prime_1.
    + destruct n.
      * rewrite Zpower_nat_1_r; assumption.
      * rewrite Zpower_nat_succ_r; apply rel_prime_mult. assumption.
        apply IHn; lia.
  - apply rel_prime_sym. apply rel_prime_div with (b ^+ n). apply rel_prime_sym.
    assumption. red. exists (b ^+ (n - 1)). rewrite mul_comm, mul_base_pull. reflexivity. lia. Qed.

Lemma odd_rel_prime_pow a n (Hn : (1 <= n)%nat): odd a = true <-> rel_prime a (2 ^+ n).
Proof. pose proof rel_prime_pow a 2 n Hn. pose proof odd_rel_prime a. tauto. Qed.

Lemma odd_pow2 n (H : (0 < n)%nat) : odd (2 ^+ n) = false.
Proof.
  rewrite mul_base_pull; [|lia]; rewrite odd_mul; reflexivity. Qed.

Lemma odd_mod_pow2 a n (H : (0 < n)%nat) : odd (a mod 2 ^+ n) = odd a.
Proof.
  rewrite Zdiv.Zmod_eq_full, odd_sub, odd_mul, odd_pow2, andb_false_r, xorb_false_r. reflexivity.
  lia. apply Zpower_nat_nonzero. lia. Qed.

Lemma mod_equiv a b m (H : m <> 0) : a mod m = b mod m <-> (m | a - b).
Proof.
  split; intros.
  - apply Zmod_divide. lia.
    rewrite Zminus_mod. replace (a mod m - (b mod m)) with 0 by lia.
    reflexivity.
  - destruct H0. replace b with (a - x * m) by lia.
    rewrite <- Zminus_mod_idemp_r, mod_mul, sub_0_r. reflexivity. lia. Qed.

Lemma even_div a : even a = true <-> (2 | a).
Proof.
  split; intros.
  - apply  Zeven_bool_iff in H; apply Zeven_ex in H. destruct H as [x]; exists x; lia.
  - destruct H as [x]; rewrite H, even_mul, orb_true_r; reflexivity. Qed.

Lemma divide_lemma a b c (Hc : 0 < c) (Hcb : (c | b)) : (a | b / c) <-> (c * a | b).
Proof.
  split; intros Habc.
  - unfold divide in Habc. unfold divide.
    destruct Habc as [k H]. exists k. replace (k * _) with (c * (b / c)) by lia.
    rewrite <- Zdivide_Zdiv_eq by assumption. reflexivity.
  - unfold divide in Habc. unfold divide.
    destruct Habc as [k H]. exists k. replace b with (k * a * c) by lia.
    rewrite Z.div_mul. reflexivity. lia. Qed.

Lemma log2_div a p (Ha : 0 < a) (Hp : 1 < p) : log2 (a / p) <= log2 a - 1 \/ a = 1.
Proof.
  pose proof log2_half a ltac:(lia).
  destruct H; [left|right; assumption].
  pose proof div_le_compat_l a 2 p ltac:(lia) ltac:(lia).
  pose proof log2_le_mono (a / p) (a / 2) ltac:(assumption). lia. Qed.

Lemma odd_nonzero g : odd g = true -> g <> 0.
Proof. intros H Hg; subst; inversion H. Qed.

Lemma odd_divide a b : odd b = true -> (a | b) -> odd a = true.
Proof.
  intros.
  destruct (odd a) eqn:E.
  - reflexivity.
  - rewrite <- negb_even in E. apply negb_false_iff in E. apply even_div in E.
    destruct E as [x]. destruct H0 as [z].
    assert (2 | b).  exists (z * x).  lia. apply even_div in H2. rewrite <- negb_odd in H2.
    apply negb_true_iff in H2. congruence. Qed.

Lemma gcd_odd_r a b : odd b = true -> odd (gcd a b) = true.
Proof. intros; eapply odd_divide. apply H. apply gcd_divide_r. Qed.

Lemma gcd_odd_l a b : odd a = true -> odd (gcd a b) = true.
Proof. intros; eapply odd_divide. apply H. apply gcd_divide_l. Qed.

Lemma divide_mul_l_l a b c : (a * b | c) -> (a | c).
Proof. intros [x]; exists (b * x); lia. Qed.

Lemma divide_mul_l_r a b c : (a * b | c) -> (b | c).
Proof. intros [x]; exists (a * x); lia. Qed.

Lemma mod2_dec a : { a mod 2 = 0 } + { a mod 2 = 1 }.
Proof. pose proof Zmod_even a; destruct (even a); auto. Qed.

Lemma min (f : nat -> Z) (H0 : f 0%nat <> 0) (H : exists N, f N = 0) :
  exists K, f K <> 0 /\ f (S K) = 0.
Proof.
  destruct H as [N].
  induction N.
  - lia.
  - destruct (eqb_spec (f N) 0).
    + apply IHN. assumption.
    + exists N. split.
      * assumption.
      * apply H. Qed.

Lemma gcd_rel_prime a b c : gcd a b = 1 -> gcd a c = gcd a (b * c).
Proof.
  intros. symmetry. apply gcd_unique.
  - apply gcd_nonneg.
  - apply gcd_divide_l.
  - apply divide_mul_r. apply gcd_divide_r.
  - intros q qa qbc.
    apply gauss in qbc.
    + apply gcd_greatest; assumption.
    + apply Zgcd_1_rel_prime. apply rel_prime_div with (p:=a).
      apply Zgcd_1_rel_prime. assumption. assumption. Qed.
