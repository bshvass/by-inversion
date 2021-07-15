From Coq Require Import List QArith micromega.Lia.

(* From BY Require Import Rlemmas Tactics SetoidRewrite. *)

Local Open Scope Q_scope.
Local Open Scope list_scope.

Declare Scope matQ_scope.
Declare Scope vec_scope.

Definition matQ := (Q * Q * Q * Q)%type.
Definition vec := (Q * Q)%type.
Notation "[ a , b ; c , d ]" := ((((a, b), c), d) : matQ) : matQ_scope.
Notation "[ a ; b ]" := ((a, b) : vec) : matQ_scope.

Bind Scope matQ_scope with matQ.
Bind Scope vec_scope with vec.

Local Open Scope matQ_scope.

Definition v0 := [ 0 ; 0]%Q.
Definition m0 := [ 0 , 0 ; 0 , 0]%Q.
Definition I := [ 1 , 0 ; 0 , 1 ]%Q.

Definition mplus (m1 m2 : matQ) :=
  let '(a11, a12, a21, a22) := m1 in
  let '(b11, b12, b21, b22) := m2 in
  [ a11 + b11, a12 + b12;
      a21 + b21, a22 + b22 ]%Q.

Definition mopp (m : matQ) :=
  let '(m11, m12, m21, m22) := m in
  [ -m11 , -m12 ; -m21 , -m22 ]%Q.

Definition mminus (m1 m2 : matQ) :=
  mplus m1 (mopp m2).

Definition mmult (m1 m2 : matQ) :=
  let '(a11, a12, a21, a22) := m1 in
  let '(b11, b12, b21, b22) := m2 in
  [ a11 * b11 + a12 * b21,
    a11 * b12 + a12 * b22 ;
      a21 * b11 + a22 * b21 ,
      a21 * b12 + a22 * b22 ]%Q.

Definition mtrans (m : matQ) :=
  let '(m11, m12, m21, m22) := m in
  [ m11 , m21 ; m12 , m22 ]%Q.
