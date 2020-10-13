From Coq Require Import List Rbase Reals QArith micromega.Lia micromega.Lra.

From BY Require Import Rlemmas Tactics SetoidRewrite.

Local Open Scope R_scope.
Local Open Scope list_scope.

Declare Scope mat_scope.
Declare Scope vec_scope.

Definition mat := (R * R * R * R)%type.
Definition vec := (R * R)%type.
Notation "[ a , b ; c , d ]" := ((((a, b), c), d) : mat) : mat_scope.
Notation "[ a ; b ]" := ((a, b) : vec) : mat_scope.

Bind Scope mat_scope with mat.
Bind Scope vec_scope with vec.

Local Open Scope mat_scope.

Definition v0 := [ 0 ; 0]%R.
Definition m0 := [ 0 , 0 ; 0 , 0]%R.
Definition I := [ 1 , 0 ; 0 , 1 ]%R.

Definition mplus (m1 m2 : mat) :=
  let '(a11, a12, a21, a22) := m1 in
  let '(b11, b12, b21, b22) := m2 in
  [ a11 + b11, a12 + b12;
      a21 + b21, a22 + b22 ]%R.

Definition mopp (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  [ -m11 , -m12 ; -m21 , -m22 ]%R.

Definition mminus (m1 m2 : mat) :=
  mplus m1 (mopp m2).

Definition mmult (m1 m2 : mat) :=
  let '(a11, a12, a21, a22) := m1 in
  let '(b11, b12, b21, b22) := m2 in
  [ a11 * b11 + a12 * b21,
    a11 * b12 + a12 * b22 ;
      a21 * b11 + a22 * b21 ,
      a21 * b12 + a22 * b22 ]%R.

Definition mtrans (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  [ m11 , m21 ; m12 , m22 ]%R.

Definition scmat a (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  [ a * m11 , a * m12 ; a * m21 , a * m22 ]%R.

Definition vplus (v w : vec) :=
  let '(v1, v2) := v in
  let '(w1, w2) := w in
  [ v1 + w1 ; v2 + w2 ]%R.

Definition vopp (v : vec) :=
  let '(v1, v2) := v in
  [ - v1 ; - v2 ]%R.

Definition vminus (v w : vec) :=
  vplus v (vopp w).

Definition vmult (m : mat) (v : vec) :=
  let '(m11, m12, m21, m22) := m in
  let '(v1, v2) := v in
  [ m11 * v1 + m12 * v2 ; m21 * v1 + m22 * v2 ]%R.

Definition scvec a (v : vec) :=
  let '(v1, v2) := v in
  [ a * v1 ; a * v2 ]%R.

Definition inner (v w : vec) : R :=
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

Notation "⟨ v , w ⟩" := (inner v w).
Notation "m ^T" := (mtrans m) (at level 35).

Local Open Scope mat_scope.
Local Open Scope vec_scope.

Definition det (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  (m11 * m22 - m12 * m21)%R.

Definition vec_norm (v : vec) :=
  let '(v1, v2) := v in
  sqrt(v1 ^ 2 + v2 ^ 2).

Definition mat_norm (m : mat) :=
  let '(m11, m12, m21, m22) := m in
  let a := (m11 ^ 2 + m12 ^ 2)%R in
  let b := (m11 * m21 + m12 * m22)%R in
  let c := (m11 * m21 + m12 * m22)%R in
  let d := (m21 ^ 2 + m22 ^ 2)%R in
  sqrt ((a + d + sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2).

Definition normal_vec v := (/ vec_norm v) **v v.

Definition eig_vec l v m :=
  v <> v0 /\ m *v v = l **v v.

Definition eig_val l m := exists v, eig_vec l v m.

Definition ort v w := ⟨ v , w ⟩ = 0.

Definition sym m := m = m ^T.

Definition scalar_matrix m := exists k, m = k ** I.

Ltac auto_mat :=
  repeat match goal with
         | [ m : mat |- _ ] => destruct m as [[[? ?] ?] ?]
         | [ v : vec |- _ ] => destruct v as [? ?]
         | [ |- (_, _) = (_, _) ] => apply f_equal2
         | [ |- context[mmult]] => unfold mmult; simpl
         | [ |- context[mplus]] => unfold mplus; simpl
         | [ |- context[mopp]] => unfold mopp; simpl
         | [ |- context[mminus]] => unfold mminus; simpl
         | [ |- context[scmat]] => unfold scmat; simpl
         | [ |- context[vmult]] => unfold vmult; simpl
         | [ |- context[scvec]] => unfold scvec; simpl
         | [ |- context[vplus]] => unfold vplus; simpl
         | [ |- context[inner]] => unfold inner; simpl
         | [ |- context[v0]] => unfold v0; simpl
         | _ => nra
         end.

Ltac inversion_mat H :=
  repeat match goal with
         | [ m : mat |- _ ] => destruct m as [[[? ?] ?] ?]
         | [ v : vec |- _ ] => destruct v as [? ?]
         | [ H : context[mmult] |- _ ] => unfold mmult in H; simpl in H
         | [ H : context[mplus] |- _ ] => unfold mplus in H; simpl in H
         | [ H : context[mopp] |- _ ] => unfold mopp in H; simpl in H
         | [ H : context[mminus] |- _ ] => unfold mminus in H; simpl in H
         | [ H : context[scmat] |- _ ] => unfold scmat in H; simpl in H
         | [ H : context[vmult] |- _ ] => unfold vmult in H; simpl in H
         | [ H : context[scvec] |- _ ] => unfold scvec in H; simpl in H
         | [ H : context[vplus] |- _ ] => unfold vplus in H; simpl in H
         | [ H : context[v0] |- _ ] => unfold v0 in H; simpl in H
         (* | [ H : (_, _) = (_, _) |- _ ] => destruct H *)
         | _ => nra
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

Lemma vnonzero v1 v2 :
  v1 <> 0 \/ v2 <> 0 <-> [v1 ; v2] <> v0.
Proof. split. intros [v10n | v20] v_not0; inversion v_not0; contradiction.
       destruct (Req_dec v1 0); destruct (Req_dec v2 0); subst; try tauto. Qed.

Lemma vnonzero_norm v :
  v <> v0 <-> vec_norm v <> 0.
Proof.
  split.
  intros. unfold vec_norm.
  destruct v as [ v1 v2 ].
  apply vnonzero in H. intros contra. apply sqrt_eq_0 in contra. nra. nra.

  destruct v as [ v1 v2 ].
  intros. unfold vec_norm in H.
  intros contra.
  inversion_mat contra. subst.
  replace (0 ^ 2 + 0 ^ 2)%R with 0 in H by nra. rewrite sqrt_0 in H. contradiction. Qed.

Lemma mat_norm_vmult m v :
  vec_norm (m *v v) <= mat_norm m * vec_norm v.
Proof.
  destruct m as [[[m11 m12] m21] m22].
  destruct v as [v1 v2].
  unfold vmult.
  unfold vec_norm.
  unfold mat_norm.

  rewrite <- sqrt_mult_alt by (assert_pow; assert_sqrt; nra).
  apply sqrt_le_1_alt.

  replace ((m11 ^ 2 + m12 ^ 2 + (m21 ^ 2 + m22 ^ 2) + sqrt ((m11 ^ 2 + m12 ^ 2 - (m21 ^ 2 + m22 ^ 2)) ^ 2 + 4 * (m11 * m21 + m12 * m22) ^ 2)) / 2 * (v1 ^ 2 + v2 ^ 2))%R
    with ((m11 ^ 2 + m12 ^ 2 + (m21 ^ 2 + m22 ^ 2) + sqrt ((m11 ^ 2 + m12 ^ 2 - (m21 ^ 2 + m22 ^ 2)) ^ 2 + 4 * (m11 * m21 + m12 * m22) ^ 2)) * (v1 ^ 2 + v2 ^ 2) / 2) by nra.

  apply Rle_div_r. nra.

  enough (2 * ((m11 * v1 + m12 * v2) ^ 2 + (m21 * v1 + m22 * v2) ^ 2) - (m11 ^ 2 + m12 ^ 2 + (m21 ^ 2 + m22 ^ 2)) * (v1 ^ 2 + v2 ^ 2) <=
          sqrt ((m11 ^ 2 + m12 ^ 2 - (m21 ^ 2 + m22 ^ 2)) ^ 2 + 4 * (m11 * m21 + m12 * m22) ^ 2) * (v1 ^ 2 + v2 ^ 2)).
  nra.

  rewrite <- Rabs_pos_eq by (assert_pow; assert_sqrt; nra).

  apply (le_pow 2). lia. 

  rewrite Rpow_mult_distr, pow2_sqrt by (assert_pow; nra).
 
  psatz R. Qed.

Lemma mat_norm_nonneg m :
  0 <= mat_norm m .
Proof. auto_mat. apply sqrt_pos. Qed.

Lemma vec_norm_nonneg v :  0 <= vec_norm v.
Proof. auto_mat. apply sqrt_pos. Qed.

Lemma vec_norm_pos_nonneg v (vnon0 : v <> v0) : 0 < vec_norm v.
Proof. pose proof vnonzero_norm v. pose proof vec_norm_nonneg v. apply H in vnon0. lra. Qed.
