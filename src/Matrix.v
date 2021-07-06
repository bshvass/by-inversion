Require Import Ring.
From BY Require Import Hierarchy.

Section __.
  Context
    {R}
    `{commutative_ring R}.

  Add Ring R_ring : ring_ring_theory.

  Local Open Scope ring_scope.
  Local Open Scope group_scope.
  Local Open Scope lmodule_scope.

  (* Local Declare Scope R_scope. *)
  (* Local Delimit Scope R_scope with R. *)

  (* Local Open Scope R_scope. *)

  (* Local Infix "+" := o1 : R_scope. *)
  (* Local Infix "*" := o2 : R_scope. *)
  (* Local Notation "- a" := (inv1 a) : R_scope. *)
  (* Local Infix "-" := (fun x y => x + (- y)) : R_scope. *)
  (* Local Notation "0" := (i1 : A): R_scope. *)
  (* Local Notation "1" := (i2 : A) : R_scope. *)

  (* Local Open Scope list_scope. *)

  Declare Scope mat_scope.
  Declare Scope vec_scope.

  Delimit Scope mat_scope with M.
  Delimit Scope vec_scope with V.

  Local Open Scope mat_scope.
  Local Open Scope vec_scope.

  Definition mat := (R * R * R * R)%type.
  Definition vec := (R * R)%type.
  Notation "[ a , b ; c , d ]" := ((((a, b), c), d) : mat) (only parsing) : mat_scope.
  Notation "[ a b ] [ c d ]" := ((((a, b), c), d) : mat) (only printing, format "[ a  b ] '//' [ c  d ]") : mat_scope.
  Notation "[ a ; b ]" := ((a, b) : vec) (only parsing) : mat_scope.
  Notation "[ a ] [ b ]" := ((a, b) : vec) (only printing, format "[ a ] '//' [ b ]") : mat_scope.

  Bind Scope mat_scope with mat.
  Bind Scope vec_scope with vec.

  Local Open Scope mat_scope.
  Local Open Scope vec_scope.

  Definition v0 := [ 0 ; 0 ].
  Definition m0 := [ 0 , 0 ; 0 , 0].
  Definition I := [ 1 , 0 ; 0 , 1 ].

  Definition mplus (m1 m2 : mat) :=
    let '(a11, a12, a21, a22) := m1 in
    let '(b11, b12, b21, b22) := m2 in
    [ a11 + b11, a12 + b12;
        a21 + b21, a22 + b22 ].

  Definition mopp (m : mat) :=
    let '(m11, m12, m21, m22) := m in
    [ -m11 , -m12 ; -m21 , -m22 ].

  Definition mminus (m1 m2 : mat) :=
    mplus m1 (mopp m2).

  Definition mmult (m1 m2 : mat) :=
    let '(a11, a12, a21, a22) := m1 in
    let '(b11, b12, b21, b22) := m2 in
    [ a11 * b11 + a12 * b21,
      a11 * b12 + a12 * b22 ;
        a21 * b11 + a22 * b21 ,
        a21 * b12 + a22 * b22 ].

  Definition mtrans (m : mat) :=
    let '(m11, m12, m21, m22) := m in
    [ m11 , m21 ; m12 , m22 ].

  Definition scmat a (m : mat) :=
    let '(m11, m12, m21, m22) := m in
    [ a * m11 , a * m12 ; a * m21 , a * m22 ].

  Definition vplus (v w : vec) :=
    let '(v1, v2) := v in
    let '(w1, w2) := w in
    [ v1 + w1 ; v2 + w2 ].

  Definition vopp (v : vec) :=
    let '(v1, v2) := v in
    [ - v1 ; - v2 ].

  Definition vminus (v w : vec) :=
    vplus v (vopp w).

  Definition vmult (m : mat) (v : vec) :=
    let '(m11, m12, m21, m22) := m in
    let '(v1, v2) := v in
    [ m11 * v1 + m12 * v2 ; m21 * v1 + m22 * v2 ].

  Definition scvec a (v : vec) :=
    let '(v1, v2) := v in
    [ a * v1 ; a * v2 ].

  Definition inner (v w : vec) :=
    let '(v1, v2) := v in
    let '(w1, w2) := w in
    v1 * w1 + v2 * w2.

  Definition det (m : mat) :=
    let '(m11, m12, m21, m22) := m in
    (m11 * m22 - m12 * m21).

  Ltac auto_mat :=
    repeat match goal with
           | [ m : mat |- _ ] => destruct m as [[[? ?] ?] ?]
           | [ v : vec |- _ ] => destruct v as [? ?]
           | [ |- (_, _) = (_, _) ] => apply f_equal2
           | [ |- context[monoid_op]] => unfold monoid_op; simpl
           | [ |- context[mmult]] => unfold mmult; simpl
           | [ |- context[mplus]] => unfold mplus; simpl
           | [ |- context[mopp]] => unfold mopp; simpl
           | [ |- context[mminus]] => unfold mminus; simpl
           | [ |- context[scmat]] => unfold scmat; simpl
           | [ |- context[vmult]] => unfold vmult; simpl
           | [ |- context[scvec]] => unfold scvec; simpl
           | [ |- context[vplus]] => unfold vplus; simpl
           | [ |- context[inner]] => unfold inner; simpl
           | [ |- context[v0]] => unfold v0; cbn
           | [ |- context[m0]] => unfold m0; cbn
           | _ => progress cbn
           | _ => ring
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
           | [ |- context[m0]] => unfold m0; cbn
           | _ => ring
           end; inversion H.

  Compute mplus I I.

  Global Instance mplus_abelian_group_op : Abelian_group_op mat := mplus.
  Global Instance mmult_ring_op : Ring_op mat := mmult.
  Global Instance m0_abelian_group_id : Abelian_group_id mat := m0.
  Global Instance I_ring_id : Ring_id mat := I.
  Global Instance mopp_abelian_group_opp : Abelian_group_opp mat := mopp.

  Global Instance vplus_abelian_group_op : Abelian_group_op vec := vplus.
  Global Instance v0_abelian_group_id : Abelian_group_id vec := v0.
  Global Instance vopp_abelian_group_opp : Abelian_group_opp vec := vopp.

  Global Instance scvec_left_act : Module_left_act vec R := scvec.
  Global Instance scmat_left_act : Module_left_act mat R := scmat.
  Global Instance vmult_left_act : Module_left_act vec mat := vmult.

  Global Instance matrix_ring : @ring mat mplus mmult m0 I mopp.
  Proof. repeat split; red; intros; try change monoid_id with m0; auto_mat. Qed.

  Global Instance vec_abelian_group : @abelian_group _ vplus v0 vopp.
  Proof. repeat split; red; intros; try change monoid_id with v0; auto_mat. Qed.

  Global Instance vec_R_module : @left_module vec R vplus v0 vopp _ _ _ _ _ scvec.
  Proof. split. 2: { apply H4. } all: repeat split; red; intros; try change monoid_id with v0; auto_mat. Qed.

  Global Instance mat_R_module : @left_module mat R mplus m0 mopp _ _ _ _ _ scmat.
  Proof. split. 2: { apply H4. } all: repeat split; red; intros; try change monoid_id with m0; auto_mat. Qed.

  Global Instance vec_mat_module : @left_module vec mat _ _ _ _ _ _ _ _ vmult.
  Proof. split. 2: { apply matrix_ring. } all: repeat split; red; intros; try change monoid_id with v0; auto_mat. Qed.

  (* Notation "a ** m" := (scmat a m) (at level 35) : mat_scope. *)
  (* Notation "a **v v" := (scvec a v) (at level 35) : vec_scope. *)

  (* Infix "*" := mmult : mat_scope. *)
  (* Infix "+" := mplus : mat_scope. *)
  (* Infix "-" := mminus : mat_scope. *)

  (* Infix "*v" := vmult (at level 35) : mat_scope. *)
  (* Infix "+v" := vplus (at level 40) : vec_scope. *)
  (* Infix "-v" := vminus (at level 40) : vec_scope. *)

  Notation "⟨ v , w ⟩" := (inner v w).
  Notation "m 'ᵀ'" := (mtrans m) (at level 35).

  Definition eig_vec (l : R) (v : vec) (m : mat) :=
    v <> v0 /\ m ⋅ v = l ⋅  v.

  Definition eig_val (l : R) (m : mat) := exists v, eig_vec l v m.

  Definition ort v w := ⟨ v , w ⟩ = 0.

  Definition sym m := m = m ᵀ.

  Definition scalar_matrix (m : mat) := exists k, m = k ⋅ I.

  Lemma scmat_vmult (l : R) (v : vec) (m : mat) :
    l ⋅ m ⋅ v = l ⋅ (m ⋅ v).
  Proof. auto_mat. Qed.

  Lemma vmult_scvec (l : R) (v : vec) (m : mat) :
    m ⋅ (l ⋅ v) = l ⋅ m ⋅ v.
  Proof. auto_mat. Qed.

  Lemma scvec_vmult (l : R) (v : vec) (m : mat) :
    l ⋅ (m ⋅ v) = l ⋅ m ⋅ v.
  Proof. auto_mat. Qed.

  Definition vmult_I_l : forall v, I ⋅ v = v := left_identity.

  Lemma vmult_mminus_distr_r (m1 m2 : mat) (v : vec) :
    (m1 - m2) ⋅ v = m1 ⋅ v - m2 ⋅ v.
  Proof. auto_mat. Qed.

  Lemma inner_mult_r (μ : R) (v w : vec) :
    ⟨ v , μ ⋅ w ⟩ = μ * ⟨ v , w ⟩.
  Proof. auto_mat. Qed.

  Lemma inner_mult_l ν v w :
    ⟨ ν ⋅ v , w ⟩ = ν * ⟨ v , w ⟩.
  Proof. auto_mat. Qed.

  Lemma inner_plus_r u v w :
    ⟨ u , v + w ⟩ = ⟨ u , v ⟩ + ⟨ u , w ⟩.
  Proof. auto_mat. Qed.

  Lemma inner_plus_l u v w :
    ⟨ u + v , w ⟩ = ⟨ u , w ⟩ + ⟨ v , w ⟩.
  Proof. auto_mat. Qed.

  Lemma inner_sym u v :
    ⟨ u , v ⟩ = ⟨ v , u ⟩.
  Proof. auto_mat. Qed.

  Lemma ort_scvec_r u v (ν : R) : ort u v -> ort u (ν ⋅ v).
  Proof. unfold ort; intros. rewrite inner_mult_r. rewrite H5, mul_0_r. reflexivity. Qed.

  Lemma ort_scvec_l u v (μ : R) : ort u v -> ort (μ ⋅ u) v.
  Proof. unfold ort; intros; rewrite inner_mult_l; rewrite H5, mul_0_r. reflexivity. Qed.

  Lemma ort_scvec u v (μ ν : R) : ort u v -> ort (μ ⋅ u) (ν ⋅ v).
  Proof. unfold ort; intros; rewrite inner_mult_l, inner_mult_r, H5.
         rewrite !mul_0_r. reflexivity. Qed.

  Lemma scvec_scvec (μ ν : R) (v : vec) :
    μ ⋅ (ν ⋅ v) = (μ * ν) ⋅ v.
  Proof. auto_mat. Qed.

  Lemma trans_adj m v w : ⟨ v , m ⋅ w ⟩ = ⟨ m ᵀ ⋅ v , w ⟩.
  Proof. auto_mat. Qed.

  Lemma sym_self_adj m v w : sym m -> ⟨ v , m ⋅ w ⟩ = ⟨ m ⋅ v , w ⟩.
  Proof. unfold sym; intros msym. rewrite msym at 2. apply trans_adj. Qed.

  Context
    `{forall x y : R, decidable (x = y)}.

  Lemma vnonzero v1 v2 :
    v1 <> 0 \/ v2 <> 0 <-> [v1 ; v2] <> v0.
  Proof.
    split. intros [v10 | v20] v_not0; inversion v_not0; contradiction.
    intros. destruct (H5 v1 0); destruct (H5 v2 0); subst; try tauto. Qed.

  Lemma vec_eq_dec (v w : vec) : {v = w} + {v <> w}.
  Proof.
    auto_mat. destruct (H5 r1  r); destruct (H5 r2 r0).
    1: left; subst; reflexivity. 1, 2, 3: right; intros contra; inversion contra; tauto.
  Qed.

  Lemma mnonzero m11 m12 m21 m22 :
    m11 <> 0 \/ m12 <> 0 \/ m21 <> 0 \/ m22 <> 0 <-> [ m11 , m12 ; m21 , m22 ] <> m0.
  Proof. split. intros [m110 | [m120 | [m210 | m220]]] m_not0; inversion m_not0; contradiction.
         destruct (H5 m11 0); destruct (H5 m12 0); destruct (H5 m21 0); destruct (H5 m22 0); subst; try tauto.
  Qed.

  Context `{@integral_domain R H H0 H1 H2 H3}.

  Lemma eig_sym_ort (μ ν : R) v w m :
    sym m -> μ <> ν -> eig_vec μ v m -> eig_vec ν w m -> ort v w.
  Proof.
    intros msym neq [vnon0 veig] [wnon0 weig]. auto_mat.
    unfold ort.
    assert (ν * ⟨ (r5, r6), (r3, r4) ⟩ = μ * ⟨ (r5, r6), (r3, r4) ⟩).
    now rewrite <- inner_mult_r, <- weig, sym_self_adj, veig, inner_mult_l.
    symmetry in H7.
    assert ((μ - ν) * ⟨ (r5, r6), (r3, r4) ⟩ = 0). rewrite mul_add_distr_r, H7. ring.
    apply zero_rule1 in H8.
    destruct H8; [apply opp_unique_l in H8; rewrite opp_invol in H8; contradiction|assumption].
  Qed.

  Lemma eig_vec_scvec l v m (x : R) (xnon0 : x <> 0) :
    eig_vec l v m -> eig_vec l (x ⋅ v) m.
  Proof.
    intros [vnon0 eig]. split.
    intros contra. inversion_mat contra. rewrite H8 in H9.
    apply zero_rule1 in H8. destruct H8.
    - contradiction.
    - apply zero_rule1 in H9. destruct H9.
      + contradiction.
      + apply vnon0. subst. reflexivity.
    - rewrite vmult_scvec.
      rewrite scmat_vmult. rewrite eig.
      rewrite scvec_scvec. rewrite mul_comm.
      rewrite scvec_scvec. reflexivity.
  Qed.

Lemma det_zero m :
  det m = 0 -> exists v, v <> v0 /\ m ⋅ v = v0.
Proof.
  destruct m as [[[m11 m12] m21] m22].
  unfold det. intros.
  destruct (H5 m22 0) as [eq|neq].
  assert (m12 = 0 \/ m21 = 0).
  { rewrite eq, mul_0_r, add_0_l in H7. apply zero_rule1. apply opp_0. assumption. }
  destruct (H5 m12 0).
  - exists [ 0 ; 1]. split. apply vnonzero. right. intros contra. apply non_trivial. symmetry. exact contra.
    subst. auto_mat.
  - assert (m21 = 0) by tauto.
    exists [ m12 ; -m11]. split. apply vnonzero. left; assumption. subst; auto_mat.
  - exists [ m22 ; - m21 ]. split. apply vnonzero; left; assumption. auto_mat. rewrite <- opp_mul_r. assumption.
Qed.

Lemma eig_pol l m :
  det (m - l ⋅ 1) = 0 -> eig_val l m.
Proof.
  intros. apply det_zero in H7.
  destruct H7 as [v [vnon0 eq]].
  unfold det. exists v. split. assumption.
  rewrite right_distributive in eq.
  apply opp_unique_r in eq. rewrite <- opp_act in eq.
  apply opp_inj in eq.
  rewrite scmat_vmult in eq.
  rewrite act_1_l in eq.
  symmetry. assumption.
Qed.

End __.

Declare Scope mat_scope.
Declare Scope vec_scope.

Delimit Scope mat_scope with M.
Delimit Scope vec_scope with V.

Local Open Scope mat_scope.
Local Open Scope vec_scope.

Notation "[ a , b ; c , d ]" := ((((a, b), c), d) : mat) (only parsing) : mat_scope.
Notation "[ a b ] [ c d ]" := ((((a, b), c), d) : mat) (only printing, format "[ a  b ] '//' [ c  d ]") : mat_scope.
Notation "[ a ; b ]" := ((a, b) : vec) (only parsing) : mat_scope.
Notation "[ a ] [ b ]" := ((a, b) : vec) (only printing, format "[ a ] '//' [ b ]") : mat_scope.

(* Notation "a ** m" := (scmat a m) (at level 35) : mat_scope. *)
(* Notation "a **v v" := (scvec a v) (at level 35) : vec_scope. *)

(* Infix "*" := mmult : mat_scope. *)
(* Infix "+" := mplus : mat_scope. *)
(* Infix "-" := mminus : mat_scope. *)

(* Infix "*v" := vmult (at level 35) : mat_scope. *)
(* Infix "+v" := vplus (at level 40) : vec_scope. *)
(* Infix "-v" := vminus (at level 40) : vec_scope. *)

Notation "⟨ v , w ⟩" := (inner v w) : mat_scope.
Notation "m ^T" := (mtrans m) (at level 35) : mat_scope.

Ltac auto_mat :=
  repeat match goal with
         | [ m : mat |- _ ] => destruct m as [[[? ?] ?] ?]
         | [ v : vec |- _ ] => destruct v as [? ?]
         | [ |- (_, _) = (_, _) ] => apply f_equal2
         (* | [ |- context[monoid_op]] => unfold monoid_op; simpl *)
         | [ |- context[mmult]] => unfold mmult; simpl
         | [ |- context[mplus]] => unfold mplus; simpl
         | [ |- context[mopp]] => unfold mopp; simpl
         | [ |- context[mminus]] => unfold mminus; simpl
         | [ |- context[scmat]] => unfold scmat; simpl
         | [ |- context[vmult]] => unfold vmult; simpl
         | [ |- context[scvec]] => unfold scvec; simpl
         | [ |- context[vplus]] => unfold vplus; simpl
         | [ |- context[inner]] => unfold inner; simpl
         | [ |- context[mtrans]] => unfold mtrans; simpl
         | [ |- context[v0]] => unfold v0; cbn
         | [ |- context[m0]] => unfold m0; cbn
         | _ => ring
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
         | [ H : context[mtrans] |- _ ] => unfold mtrans in H; simpl in H
         | [ H : context[v0] |- _ ] => unfold v0 in H; simpl in H
         | [ |- context[m0]] => unfold m0; cbn
         | _ => ring
         end; inversion H.

Notation big_mmult_rev := (@big_op_rev mat mmult I).
(* Notation big_mmult_rev0 := (fun n f => @big_op_rev _ mmult I f 0 n). *)
