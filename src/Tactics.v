Require Import Rbase Reals QArith micromega.Lia micromega.Lra.

Local Open Scope R.

Ltac assert_pow :=
    repeat match goal with
    | [ |- context[?a ^ 2] ] => match goal with
                               | [ _ : 0 <= a ^ 2 |- _ ] => fail 1
                               | [ |- _ ] =>
                                 assert (0 <= a ^ 2) by (apply pow2_ge_0; nra)
                               end
           end.

Ltac assert_sqrt :=
    repeat match goal with
    | [ |- context[sqrt ?a] ] => match goal with
                               | [ _ : 0 <= sqrt a |- _ ] => fail 1
                               | [ |- _ ] =>
                                 assert (0 <= sqrt a) by (apply sqrt_positivity; nra)
                               end
           end.
