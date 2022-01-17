From Coq Require Import Ring.
From BY Require Import Hierarchy.Definitions.

Section IntegralDomain.

  Context `{IntegralDomain A}.

  Global Instance domain_cring : CommutativeRing A. sub_class_tac. Qed.

End IntegralDomain.
