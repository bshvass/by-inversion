Require Import ZArith Znumtheory Reals.

From BY Require Import Rlemmas Zpower_nat.

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
