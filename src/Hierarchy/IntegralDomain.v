From Coq Require Import Ring.
From BY Require Export Hierarchy.Definitions.
From BY.Hierarchy Require Import AbelianGroup CommutativeRing CommutativeMonoid.

Section IntegralDomain.

  Local Open Scope ring_scope.

  Class IntegralDomain A `{Equiv A, Op1 A, Op2 A, Id1 A, Id2 A, Inv1 A} :=
    {
      dom_ab_grp :> @AbelianGroup _ _ (+) 0 (-);
      dom_mon :> @CommutativeMonoid _ _ [*] 1;
      dom_distr_l :> LeftDistr (≡) [*] (+);
      dom_distr_r :> RightDistr (≡) [*] (+);
      dom_non_trivial : 0 ≢ 1;
      dom_zero_rule :> ZeroRule1 (≡) 0 [*]
    }.

  Context `{IntegralDomain A}.

  Global Instance domain_cring : CommutativeRing A. sub_class_tac. Qed.

End IntegralDomain.
