From Coq Require Import List Rbase Reals QArith micromega.Lia micromega.Lra.

From BY Require Import Rlemmas Tactics.

Local Open Scope R_scope.
Local Open Scope list_scope.

Definition matrix := (R * R * R * R)%type.
Definition col := (R * R)%type.
Notation "[ a , b ; c , d ]" := ((((a, b), c), d) : matrix).
Notation "[ a ; b ]" := ((a, b) : col).

Definition I := [ 1 , 0 ; 0 , 1 ].

Definition matmult m1 m2 :=
  let '(a11, a12, a21, a22) := m1 in
  let '(b11, b12, b21, b22) := m2 in
  [ a11 * b11 + a12 * b21,
    a11 * b12 + a12 * b22 ;
      a21 * b11 + a22 * b21 ,
      a21 * b12 + a22 * b22 ].  
Definition colmult m c :=
  let '(a11, a12, a21, a22) := m in
  let '(c1, c2) := c in
  [ a11 * c1 + a12 * c2 ; a21 * c1 + a22 * c2 ].

Notation "m *col c" := (colmult m c) (at level 45).
Notation "m *mat n" := (matmult m n) (at level 40).

Definition norm (m : matrix) :=
  let '(m11, m12, m21, m22) := m in
  let a := m11 ^ 2 + m12 ^ 2 in
  let b := m11 * m12 + m21 * m22 in
  let c := m11 * m12 + m21 * m22 in
  let d := m21 ^ 2 + m22 ^ 2 in
  sqrt ((a + d + sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2).

Lemma norm_nonneg m :
  0 <= norm m.
Proof.   destruct m as [[[P11 P12] P21] P22]. unfold norm.
         apply sqrt_positivity. assert_pow; assert_sqrt.
         apply Rle_div; lra. Qed.

