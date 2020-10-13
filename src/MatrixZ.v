From Coq Require Import List ZArith micromega.Lia.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Declare Scope mat_scope.
Declare Scope vec_scope.

Definition mat := (Z * Z * Z * Z)%type.
Definition vec := (Z * Z)%type.
Notation "[ a , b ; c , d ]" := ((((a, b), c), d) : mat) : mat_scope.
Notation "[ a ; b ]" := ((a, b) : vec) : mat_scope.

Bind Scope mat_scope with mat.
Bind Scope vec_scope with vec.

Local Open Scope mat_scope.
Local Open Scope vec_scope.

Definition v0 := [ 0 ; 0]%Z.
Definition m0 := [ 0 , 0 ; 0 , 0]%Z.
Definition I := [ 1 , 0 ; 0 , 1 ]%Z.

Definition mplus (m1 m2 : mat) :=
  let '(a11, a12, a21, a22) := m1 in
  let '(b11, b12, b21, b22) := m2 in
  [ a11 + b11, a12 + b12;
      a21 + b21, a22 + b22 ]%Z.

Definition mopp (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  [ -m11 , -m12 ; -m21 , -m22 ]%Z.

Definition mminus (m1 m2 : mat) :=
  mplus m1 (mopp m2).

Definition mmult (m1 m2 : mat) :=
  let '(a11, a12, a21, a22) := m1 in
  let '(b11, b12, b21, b22) := m2 in
  [ a11 * b11 + a12 * b21,
    a11 * b12 + a12 * b22 ;
      a21 * b11 + a22 * b21 ,
      a21 * b12 + a22 * b22 ]%Z.

Definition mtrans (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  [ m11 , m21 ; m12 , m22 ]%Z.

Definition scmat a (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  [ a * m11 , a * m12 ; a * m21 , a * m22 ]%Z.

Definition vplus (v w : vec) :=
  let '(v1, v2) := v in
  let '(w1, w2) := w in
  [ v1 + w1 ; v2 + w2 ]%Z.

Definition vopp (v : vec) :=
  let '(v1, v2) := v in
  [ - v1 ; - v2 ]%Z.

Definition vminus (v w : vec) :=
  vplus v (vopp w).

Definition vmult (m : mat) (v : vec) :=
  let '(m11, m12, m21, m22) := m in
  let '(v1, v2) := v in
  [ m11 * v1 + m12 * v2 ; m21 * v1 + m22 * v2 ]%Z.

Definition scvec a (v : vec) :=
  let '(v1, v2) := v in
  [ a * v1 ; a * v2 ].

Definition inner (v w : vec) :=
  let '(v1, v2) := v in
  let '(w1, w2) := w in
  v1 * w1 + v2 * w2.

Notation "a ** m" := (scmat a m) (at level 35) : mat_scope.
Notation "a **v v" := (scvec a v) (at level 35) : vec_scope.

Infix "*" := mmult : mat_scope.
Infix "+" := mplus : mat_scope.
Infix "-" := mminus : mat_scope.

Infix "*v" := vmult (at level 35) : mat_scope.
Infix "+v" := vplus (at level 40) : vec_scope.
Infix "-v" := vminus (at level 40) : vec_scope.

Ltac auto_mat :=
  repeat match goal with
         | [ m : mat |- _ ] => destruct m as [[[? ?] ?] ?]
         | [ v : vec |- _ ] => destruct v as [? ?]
         | [ |- (_, _) = (_, _) ] => apply f_equal2
         | [ |- context[mmult]] => unfold mmult; cbn -[Z.mul Z.sub Z.add]
         | [ |- context[mplus]] => unfold mplus; cbn -[Z.mul Z.sub Z.add]
         | [ |- context[mopp]] => unfold mopp; cbn -[Z.mul Z.sub Z.add]
         | [ |- context[mminus]] => unfold mminus; cbn -[Z.mul Z.sub Z.add]
         | [ |- context[scmat]] => unfold scmat; cbn -[Z.mul Z.sub Z.add]
         | [ |- context[vmult]] => unfold vmult; cbn -[Z.mul Z.sub Z.add]
         | [ |- context[scvec]] => unfold scvec; cbn -[Z.mul Z.sub Z.add]
         | [ |- context[vplus]] => unfold vplus; cbn -[Z.mul Z.sub Z.add]
         | [ |- context[inner]] => unfold inner; cbn -[Z.mul Z.sub Z.add]
         | [ |- context[v0]] => unfold v0; cbn -[Z.mul Z.sub Z.add]
         | _ => nia
         end.

Ltac inversion_mat H :=
  repeat match goal with
         | [ m : mat |- _ ] => destruct m as [[[? ?] ?] ?]
         | [ v : vec |- _ ] => destruct v as [? ?]
         | [ H : context[mmult] |- _ ] => unfold mmult in H; cbn -[Z.mul Z.sub Z.add] in H
         | [ H : context[mplus] |- _ ] => unfold mplus in H; cbn -[Z.mul Z.sub Z.add] in H
         | [ H : context[mopp] |- _ ] => unfold mopp in H; cbn -[Z.mul Z.sub Z.add] in H
         | [ H : context[mminus] |- _ ] => unfold mminus in H; cbn -[Z.mul Z.sub Z.add] in H
         | [ H : context[scmat] |- _ ] => unfold scmat in H; cbn -[Z.mul Z.sub Z.add] in H
         | [ H : context[vmult] |- _ ] => unfold vmult in H; cbn -[Z.mul Z.sub Z.add] in H
         | [ H : context[scvec] |- _ ] => unfold scvec in H; cbn -[Z.mul Z.sub Z.add] in H
         | [ H : context[vplus] |- _ ] => unfold vplus in H; cbn -[Z.mul Z.sub Z.add] in H
         | [ H : context[v0] |- _ ] => unfold v0 in H; cbn -[Z.mul Z.sub Z.add] in H
         | [ H : (_, _) = (_, _) |- _ ] => destruct H
         | _ => nia
         end; inversion H.

Lemma mmult_I_l m : I * m = m.
Proof. auto_mat. Qed.

Lemma mmult_I_r m : m * I = m.
Proof. auto_mat. Qed.

Lemma mmult_assoc (a b c : mat) :
  (a * b) * c = a * (b * c).
Proof. auto_mat. Qed.

Hint Resolve mmult_I_l mmult_I_r mmult_assoc : matrix.

Lemma mmult_vmult m1 m2 v :
  (m1 * m2) *v v = m1 *v (m2 *v v).
Proof. auto_mat. Qed.

Lemma scvec_scvec μ ν v :
  μ **v (ν **v v) = (μ * ν) **v v.
Proof. auto_mat. Qed.

Lemma scmat_vmult l v m  :
  l ** m *v v = l **v (m *v v).
Proof. auto_mat. Qed.

Lemma vmult_scvec l v m :
  m *v (l **v v) = l ** m *v v.
Proof. auto_mat. Qed.

Lemma vmult_I_l v : I *v v = v.
Proof. auto_mat. Qed.

Lemma vmult_mminus_distr_r m1 m2 v :
  (m1 - m2) *v v = m1 *v v -v m2 *v v.
Proof. auto_mat. Qed.

Lemma scvec_vmult_com l v m :
  l **v (m *v v) = m *v (l **v v).
Proof. auto_mat. Qed.

Lemma vnonzero v1 v2 :
  v1 <> 0 \/ v2 <> 0 <-> [v1 ; v2] <> v0.
Proof. split. intros [v10n | v20] v_not0; inversion v_not0; contradiction.
       destruct (Z.eq_dec v1 0); destruct (Z.eq_dec v2 0); subst; try tauto. Qed.

Require Import BigOp.

Instance Mat_mult_associative : Associative mmult.
Proof. split; auto with matrix. Qed.

Instance Mat_monoid : Monoid mmult I.
Proof. split; auto with matrix. Qed.

Notation big_mmult_rev := (fun n m f => @big_op_rev _ mmult I f n m).
