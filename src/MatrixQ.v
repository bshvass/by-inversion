From Coq Require Import List QArith micromega.Lia.

(* From BY Require Import Rlemmas Tactics SetoidRewrite. *)

Local Open Scope Q_scope.
Local Open Scope list_scope.

Declare Scope mat_scope.
Declare Scope vec_scope.

Definition mat := (Q * Q * Q * Q)%type.
Definition vec := (Q * Q)%type.
Notation "[ a , b ; c , d ]" := ((((a, b), c), d) : mat) : mat_scope.
Notation "[ a ; b ]" := ((a, b) : vec) : mat_scope.

Bind Scope mat_scope with mat.
Bind Scope vec_scope with vec.

Local Open Scope mat_scope.

Definition v0 := [ 0 ; 0]%Q.
Definition m0 := [ 0 , 0 ; 0 , 0]%Q.
Definition I := [ 1 , 0 ; 0 , 1 ]%Q.

Definition mplus (m1 m2 : mat) :=
  let '(a11, a12, a21, a22) := m1 in
  let '(b11, b12, b21, b22) := m2 in
  [ a11 + b11, a12 + b12;
      a21 + b21, a22 + b22 ]%Q.

Definition mopp (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  [ -m11 , -m12 ; -m21 , -m22 ]%Q.

Definition mminus (m1 m2 : mat) :=
  mplus m1 (mopp m2).

Definition mmult (m1 m2 : mat) :=
  let '(a11, a12, a21, a22) := m1 in
  let '(b11, b12, b21, b22) := m2 in
  [ a11 * b11 + a12 * b21,
    a11 * b12 + a12 * b22 ;
      a21 * b11 + a22 * b21 ,
      a21 * b12 + a22 * b22 ]%Q.

Definition mtrans (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  [ m11 , m21 ; m12 , m22 ]%Q.
