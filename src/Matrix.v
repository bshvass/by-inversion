From Coq Require Import Ring ZArith.
From BY.Hierarchy Require Export Definitions.
From BY.Hierarchy Require Import CommutativeRing Ring IntegralDomain LeftModule Group AbelianGroup Monoid.
From stdpp Require Import base.
From stdpp Require Import decidable.

(* Parameter (R : Type). *)

Declare Scope mat_scope.
Declare Scope vec_scope.

Delimit Scope mat_scope with M.
Delimit Scope vec_scope with V.

Local Open Scope mat_scope.
Local Open Scope vec_scope.

Notation mat R := (R * R * R * R)%type.
Notation vec R := (R * R)%type.
Notation "[ a , b ; c , d ]" := ((((a, b), c), d) : mat _) (only parsing) : mat_scope.
Notation "[ a b ] [ c d ]" := ((((a, b), c), d) : mat _) (only printing, format "[ a  b ] '//' [ c  d ]") : mat_scope.
Notation "[ a , b ]" := ((a, b) : vec _) (only parsing) : vec_scope.
Notation "[ a ] [ b ]" := ((a, b) : vec _) (only printing, format "[ a ] '//' [ b ]") : vec_scope.

Bind Scope mat_scope with mat.
Bind Scope vec_scope with vec.

Section __.
  Context
    `{CommutativeRing R}.

  Add Ring R_ring : cring_ring_theory.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope mat_scope.
  Local Open Scope vec_scope.

  Local Notation mat := (mat R).
  Local Notation vec := (vec R).

  Definition v0 := [ 0 , 0 ] : vec.
  Definition m0 := [ 0 , 0 ; 0 , 0] : mat.
  Definition I := [ 1 , 0 ; 0 , 1 ] : mat.

  Definition mplus (m1 m2 : mat) : mat :=
    let '(a11, a12, a21, a22) := m1 in
    let '(b11, b12, b21, b22) := m2 in
    [ a11 + b11, a12 + b12;
        a21 + b21, a22 + b22 ].

  Definition mopp (m : mat) : mat :=
    let '(m11, m12, m21, m22) := m in
    [ -m11 , -m12 ; -m21 , -m22 ].

  (* Definition mminus (m1 m2 : mat) : mat := *)
  (*   mplus m1 (mopp m2). *)

  Definition mmult (m1 m2 : mat) : mat :=
    let '(a11, a12, a21, a22) := m1 in
    let '(b11, b12, b21, b22) := m2 in
    [ a11 * b11 + a12 * b21,
      a11 * b12 + a12 * b22 ;
        a21 * b11 + a22 * b21 ,
        a21 * b12 + a22 * b22 ].

  Definition mtrans (m : mat) : mat :=
    let '(m11, m12, m21, m22) := m in
    [ m11 , m21 ; m12 , m22 ].

  Definition scmat a (m : mat) : mat :=
    let '(m11, m12, m21, m22) := m in
    [ a * m11 , a * m12 ; a * m21 , a * m22 ].

  Definition vplus (v w : vec) : vec :=
    let '(v1, v2) := v in
    let '(w1, w2) := w in
    [ v1 + w1 , v2 + w2 ].

  Definition vopp (v : vec) : vec :=
    let '(v1, v2) := v in
    [ - v1 , - v2 ].

  (* Definition vminus (v w : vec) : vec := *)
  (*   vplus v (vopp w). *)

  Definition vmult (m : mat) (v : vec) : vec :=
    let '(m11, m12, m21, m22) := m in
    let '(v1, v2) := v in
    [ m11 * v1 + m12 * v2 , m21 * v1 + m22 * v2 ].

  Definition scvec a (v : vec) : vec :=
    let '(v1, v2) := v in
    [ a * v1 , a * v2 ].

End __.


Ltac inversion_mat H :=
  repeat match goal with
         | [ m : mat _ |- _ ] => destruct m as [[[? ?] ?] ?]
         | [ v : vec _ |- _ ] => destruct v as [? ?]
         | [ H : context[mmult] |- _ ] => unfold mmult in H; simpl in H
         | [ H : context[mplus] |- _ ] => unfold mplus in H; simpl in H
         | [ H : context[mopp] |- _ ] => unfold mopp in H; simpl in H
         (* | [ H : context[mminus] |- _ ] => unfold mminus in H; simpl in H *)
         | [ H : context[scmat] |- _ ] => unfold scmat in H; simpl in H
         | [ H : context[vmult] |- _ ] => unfold vmult in H; simpl in H
         | [ H : context[scvec] |- _ ] => unfold scvec in H; simpl in H
         | [ H : context[vplus] |- _ ] => unfold vplus in H; simpl in H
         | [ H : context[v0] |- _ ] => unfold v0 in H; simpl in H
         | [ |- context[m0]] => unfold m0; cbn
         | _ => ring
         end; inversion H.

Ltac invert_mat :=
  repeat match goal with
         | M : prod _ _ |- _ => destruct M
         | H : (@equiv _ (@prod_equiv _ _ _ _)) _ _ |- _ ?a ?b => inversion H; clear H
         end.

Ltac setoid_substitute H :=
  match type of H with
    ?x ≡ ?y => setoid_rewrite H; clear H x
  end.

Ltac setoid_subst :=
  match goal with
  | [ H : ?x ≡ ?y |- _ ] => setoid_substitute H ; setoid_subst
  | _ => idtac
  end.

Ltac auto_mat2 :=
  invert_mat; simpl in *; setoid_subst; auto.

Ltac auto_mat :=
  invert_mat;
  repeat match goal with
         | [ |- (@equiv _ (@prod_equiv _ _ _ _)) _ _ ] => split
         | _ => progress cbn -[Z.mul Z.add Z.to_nat Z.of_nat] in *; setoid_subst
         | _ => ring
         end; auto.

Section Instances.

  Context
    `{CommutativeRing R}.

  Local Open Scope grp_scope.
  Local Open Scope ab_grp_scope.
  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope lmod_scope.
  Local Open Scope mat_scope.
  Local Open Scope vec_scope.

  Add Ring R_ring : cring_ring_theory.

  Local Notation mat := (mat R).
  Local Notation vec := (vec R).

  Global Instance mplus_op1 : Op1 mat := mplus.
  Global Instance mmult_op2 : Op2 mat := mmult.
  Global Instance m0_id1 : Id1 mat := m0.
  Global Instance I_id2 : Id2 mat := I.
  Global Instance mopp_ring_inv1 : Inv1 mat := mopp.

  Global Instance mplus_Proper : Proper ((≡) ==> (≡) ==> (≡)) mplus.
  Proof. intros ? ? ? ? ? ?; auto_mat. Qed.
  Global Instance mplus_Assoc : Assoc (≡) mplus.
  Proof. intros ? ? ?; auto_mat. Qed.
  Global Instance mplus_Comm : Comm (≡) mplus.
  Proof. intros ? ?; auto_mat. Qed.

  Global Instance mmult_Proper : Proper ((≡) ==> (≡) ==> (≡)) mmult.
  Proof. intros ? ? ? ? ? ?; auto_mat. Qed.
  Global Instance mmult_Assoc : Assoc (≡) mmult.
  Proof. intros ? ? ?; auto_mat. Qed.

  Global Instance mopp_Proper : Proper ((≡) ==> (≡)) mopp.
  Proof. split; auto_mat. Qed.

  Global Instance m0_LeftId : LeftId (≡) m0 (+).
  Proof. split; auto_mat. Qed.
  Global Instance m0_RightId : RightId (≡) m0 (+).
  Proof. split; auto_mat. Qed.

  Global Instance m0_LeftInv : LeftInv (≡) m0 (-) (+).
  Proof. split; auto_mat. Qed.
  Global Instance m0_RightInv : RightInv (≡) m0 (-) (+).
  Proof. split; auto_mat. Qed.

  Global Instance I_LeftId : LeftId (≡) I [*].
  Proof. split; auto_mat. Qed.
  Global Instance I_RightId : RightId (≡) I [*].
  Proof. split; auto_mat. Qed.

  Global Instance mmult_mopp_LeftDistr : LeftDistr (≡) mmult mplus.
  Proof. split; auto_mat. Qed.
  Global Instance mmult_mopp_RightDistr : RightDistr (≡) mmult mplus.
  Proof. split; auto_mat. Qed.

  Global Instance mat_setoid : Setoid mat := prod_equivalence _ _.
  Global Instance mat_abgrp : @AbelianGroup mat _ (+) 0 (-).
  Proof. split; exact _. Qed.
  Global Instance mat_mon : @Monoid mat _ [*] 1.
  Proof. split; exact _. Qed.
  Global Instance mat_ring : Ring mat.
  Proof. split; exact _. Qed.

  Global Instance vplus_op1 : Op1 vec := vplus.
  Global Instance v0_id1 : Id1 vec := v0.
  Global Instance vopp_inv1 : Inv1 vec := vopp.

  Global Instance vplus_Proper : Proper ((≡) ==> (≡) ==> (≡)) vplus.
  Proof. intros ? ? ? ? ? ?; auto_mat. Qed.
  Global Instance vplus_Assoc : Assoc (≡) vplus.
  Proof. intros ? ? ?; auto_mat. Qed.
  Global Instance vplus_Comm : Comm (≡) vplus.
  Proof. intros ? ?; auto_mat. Qed.

  Global Instance vopp_Proper : Proper ((≡) ==> (≡)) vopp.
  Proof. split; auto_mat. Qed.

  Global Instance v0_LeftId : LeftId (≡) v0 vplus.
  Proof. split; auto_mat. Qed.
  Global Instance v0_RightId : RightId (≡) v0 vplus.
  Proof. split; auto_mat. Qed.

  Global Instance v0_LeftInv : LeftInv (≡) v0 vopp vplus.
  Proof. split; auto_mat. Qed.
  Global Instance v0_RightInv : RightInv (≡) v0 vopp vplus.
  Proof. split; auto_mat. Qed.

  Global Instance vec_setoid : Setoid vec := prod_equivalence _ _.
  Global Instance vec_abelian_group : AbelianGroup vec.
  Proof. split; exact _. Qed.

  Global Instance scvec_left_act : LeftAct vec R := scvec.
  Global Instance scmat_left_act : LeftAct mat R := scmat.
  Global Instance vmult_left_act : LeftAct vec mat := vmult.

  Global Instance scvec_Proper : Proper ((≡) ==> (≡) ==> (≡)) scvec. intros ? ? ? ? ? ?; auto_mat. Qed.
  Global Instance scmat_Proper : Proper ((≡) ==> (≡) ==> (≡)) scmat. intros ? ? ? ? ? ?; auto_mat. Qed.
  Global Instance vmult_Proper : Proper ((≡) ==> (≡) ==> (≡)) vmult. intros ? ? ? ? ? ?; auto_mat. Qed.
  Global Instance scvec_Proper2 : forall x, Proper ((≡) ==> (≡)) (scvec x). intros ? ? ? ?; auto_mat. Qed.
  Global Instance scmat_Proper2 : forall x, Proper ((≡) ==> (≡)) (scmat x). intros ? ? ? ?; auto_mat. Qed.
  Global Instance vmult_Proper2 : forall x, Proper ((≡) ==> (≡)) (vmult x). intros ? ? ? ?; auto_mat. Qed.

  Global Instance : LeftActAssoc (≡) scvec [*]. intros ? ? ?; auto_mat. Qed.
  Global Instance : LeftActId (≡) 1 scvec. intros ?; auto_mat. Qed.
  Global Instance : LeftActDistr (≡) scvec (+). intros ? ? ?; auto_mat. Qed.
  Global Instance : LeftActExch (≡) scvec (+) (+). intros ? ? ?; auto_mat. Qed.

  Global Instance : LeftActAssoc (≡) scmat [*]. intros ? ? ?; auto_mat. Qed.
  Global Instance : LeftActId (≡) 1 scmat. intros ?; auto_mat. Qed.
  Global Instance : LeftActDistr (≡) scmat (+). intros ? ? ?; auto_mat. Qed.
  Global Instance : LeftActExch (≡) scmat (+) (+). intros ? ? ?; auto_mat. Qed.

  Global Instance : LeftActAssoc (≡) vmult [*]. intros ? ? ?; auto_mat. Qed.
  Global Instance : LeftActId (≡) 1 vmult. intros ?; auto_mat. Qed.
  Global Instance : LeftActDistr (≡) vmult (+). intros ? ? ?; auto_mat. Qed.
  Global Instance : LeftActExch (≡) vmult (+) (+). intros ? ? ?; auto_mat. Qed.

  Global Instance vec_R_module : LeftModule vec R.
  Proof. split; exact _. Qed.
  Global Instance mat_R_module : LeftModule mat R.
  Proof. split; exact _. Qed.
  Global Instance vec_mat_module : LeftModule vec mat.
  Proof. split; exact _. Qed.

End Instances.

Section Definitions.
  Context
    `{CommutativeRing R}.

  Local Open Scope grp_scope.
  Local Open Scope ab_grp_scope.
  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope lmod_scope.
  Local Open Scope mat_scope.
  Local Open Scope vec_scope.

  Add Ring R_ring : cring_ring_theory.

  Local Notation mat := (mat R).
  Local Notation vec := (vec R).

  Definition eig_vec (l : R) (v : vec) (m : mat) :=
    v ≢ v0 /\ m ⋅ v ≡ l ⋅ v.
  Definition eig_val (l : R) (m : mat) := exists v, eig_vec l v m.
  Definition scalar_matrix (m : mat) := exists k, m ≡ k ⋅ I.
  Definition inner (v w : vec) : R :=
    let '(v1, v2) := v in
    let '(w1, w2) := w in
    v1 * w1 + v2 * w2.

  Definition det (m : mat) : R :=
    let '(m11, m12, m21, m22) := m in
    m11 * m22 - m12 * m21.

  Definition ort (v w : vec) := inner v w ≡ 0.

  Definition sym m := m ≡ mtrans m.

  Global Instance : Proper ((≡) ==> (≡) ==> (≡)) inner. intros ? ? ? ? ? ?; auto_mat. Qed.
  Global Instance : Proper ((≡) ==> (≡)) mtrans. intros ? ? ?; auto_mat. Qed.
  Global Instance : Proper ((≡) ==> (≡)) det. intros ? ? ?; auto_mat. Qed.

End Definitions.

Arguments inner { _ _ _ } _ _ : assert.

Notation "v ⟂ w" := (ort v w) (at level 20).
Notation "⟨ v , w ⟩" := (inner v w).
Notation "m 'ᵀ'" := (mtrans m) (at level 0).

Section Inner.

  Context
    `{CommutativeRing R}.
  Add Ring R_ring : cring_ring_theory.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope lmod_scope.
  Local Open Scope vec_scope.

  Local Notation vec := (vec R).
  Local Notation mat := (mat R).

  Lemma inner_mult_r (μ : R) (v w : vec) :
    ⟨ v , μ ⋅ w ⟩ ≡ μ * ⟨ v , w ⟩.
  Proof. auto_mat. Qed.

  Lemma inner_mult_l ν v w :
    ⟨ ν ⋅ v , w ⟩ ≡ ν * ⟨ v , w ⟩.
  Proof. auto_mat. Qed.

  Lemma inner_plus_r (u v w : vec) :
    ⟨ u , v + w ⟩ ≡ ⟨ u , v ⟩ + ⟨ u , w ⟩.
  Proof. auto_mat. Qed.

  Lemma inner_plus_l u v w :
    ⟨ u + v , w ⟩ ≡ ⟨ u , w ⟩ + ⟨ v , w ⟩.
  Proof. auto_mat. Qed.

  Lemma inner_sym u v :
    ⟨ u , v ⟩ ≡ ⟨ v , u ⟩.
  Proof. auto_mat. Qed.

  Lemma ort_scvec_r u v (ν : R) : u ⟂ v -> u ⟂ (ν ⋅ v).
  Proof. unfold ort; intros H01. rewrite inner_mult_r, H01, mul_0_r. reflexivity. Qed.

  Lemma ort_scvec_l u v (μ : R) : u ⟂ v -> (μ ⋅ u) ⟂ v.
  Proof. unfold ort; intros  H01; rewrite inner_mult_l, H01, mul_0_r. reflexivity. Qed.

  Lemma ort_scvec u v (μ ν : R) : u ⟂ v -> (μ ⋅ u) ⟂ (ν ⋅ v).
  Proof. unfold ort; intros H01; rewrite inner_mult_l, inner_mult_r, H01.
         rewrite !mul_0_r. reflexivity. Qed.

  Lemma trans_adj m v w : ⟨ v , m ⋅ w ⟩ ≡ ⟨ m ᵀ ⋅ v , w ⟩.
  Proof. auto_mat. Qed.

  Lemma sym_self_adj m v w : sym m -> ⟨ v , m ⋅ w ⟩ ≡ ⟨ m ⋅ v , w ⟩.
  Proof. unfold sym; intros H01. rewrite H01 at 2. apply trans_adj. Qed.

  Lemma det_mul m n : det (m * n) ≡ det m * det n.
  Proof. auto_mat. Qed.
End Inner.

Section Matrix.
  Context
    `{CommutativeRing R}.
  Add Ring R_ring : cring_ring_theory.

  Local Open Scope ab_grp_scope.
  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope lmod_scope.
  Local Open Scope vec_scope.
  Local Open Scope mat_scope.

  Local Notation vec := (vec R).
  Local Notation mat := (mat R).

  Lemma scmat_vmult (l : R) (v : vec) (m : mat) :
    l ⋅ m ⋅ v ≡ l ⋅ (m ⋅ v).
  Proof. auto_mat. Qed.

  Lemma vmult_scvec (l : R) (v : vec) (m : mat) :
    m ⋅ (l ⋅ v) ≡ l ⋅ (m ⋅ v).
  Proof. auto_mat. Qed.

  Lemma scvec_vmult (l : R) (v : vec) (m : mat) :
    l ⋅ (m ⋅ v) ≡ l ⋅ m ⋅ v.
  Proof. auto_mat. Qed.

  Lemma scmat_vmult_swap (l : R) (v : vec) (m : mat) :
    (l ⋅ m) ⋅ v ≡ m ⋅ (l ⋅ v).
  Proof. auto_mat. Qed.

  Lemma vmult_mminus_distr_r (m1 m2 : mat) (v : vec) :
    (m1 - m2) ⋅ v ≡ m1 ⋅ v - m2 ⋅ v.
  Proof. auto_mat. Qed.

  Lemma scvec_scvec (μ ν : R) (v : vec) :
    μ ⋅ (ν ⋅ v) ≡ (μ * ν) ⋅ v.
  Proof. auto_mat. Qed.

  Lemma scvec_swap (μ ν : R) (v : vec) :
    μ ⋅ (ν ⋅ v) ≡ ν ⋅ (μ ⋅ v).
  Proof. auto_mat. Qed.

  Context
    `{!RelDecision (≡@{R})}.

  Lemma vnonzero (v1 v2 : R) :
    v1 ≢ 0 \/ v2 ≢ 0 <-> [ v1 , v2 ] ≢ 0.
  Proof.
    split. intros [? | ?] []; contradiction.
    intros H01. destruct (decide (v1 ≡ 0)); destruct (decide (v2 ≡ 0)); auto.
    exfalso; apply H01. auto_mat; auto. Qed.

  Global Instance : RelDecision (≡@{vec}).
  intros [x1 x2] [y1 y2].
  destruct (decide (x1 ≡ y1)); destruct (decide (x2 ≡ y2)).
  1: left; rewrite e, e0; reflexivity.
  1, 2, 3: right; intros []; auto. Qed.

  Lemma mnonzero m11 m12 m21 m22 :
    m11 ≢ 0 \/ m12 ≢ 0 \/ m21 ≢ 0 \/ m22 ≢ 0 <-> [ m11 , m12 ; m21 , m22 ] ≢ 0.
  Proof. split. intros [m110 | [m120 | [m210 | m220]]] [[[]]]; contradiction.
         destruct (decide (m11 ≡ 0)); destruct (decide (m12 ≡ 0)); destruct (decide (m21 ≡ 0)); destruct (decide (m22 ≡ 0)); try tauto.
         intros contra.  exfalso; apply contra. rewrite e, e0, e1, e2. reflexivity.
  Qed.
End Matrix.

Section Eigen.

  Context
    `{IntegralDomain R}
    `{!RelDecision (≡@{R})}.
  Add Ring R_ring : cring_ring_theory.

  Local Open Scope sr_scope.
  Local Open Scope ring_scope.
  Local Open Scope lmod_scope.
  Local Open Scope ab_grp_scope.
  Local Open Scope mat_scope.
  Local Open Scope vec_scope.

  Local Notation mat := (mat R).
  Local Notation vec := (vec R).

  Lemma eig_sym_ort (μ ν : R) :
    forall v w m, sym m -> μ ≢ ν -> eig_vec μ v m -> eig_vec ν w m -> ort v w.
  Proof.
    intros v w m (* [v1 v2] [w1 w2] [[[m11 m12] m21] m22] *) msym neq [vnon0 veig] [wnon0 weig].
    unfold ort.
    assert (ν * ⟨ v, w ⟩ ≡ μ * ⟨ v, w ⟩).
    now rewrite <- inner_mult_r, <- weig, sym_self_adj, veig, inner_mult_l.
    (* symmetry in H7. *)
    assert ((μ - ν) * ⟨ v, w ⟩ ≡ 0)%SR.
    rewrite (right_distr [*] (+)%SR), <- H6. ring.
    apply (zero_rule1 0 [*]) in H7.
    destruct H7; [apply grp_inv_unique_l in H7; rewrite grp_inv_inv in H7; contradiction|assumption].
  Qed.

  Lemma eig_vec_scvec l v m (x : R) (xnon0 : x ≢ 0) :
    eig_vec l v m -> eig_vec l (x ⋅ v) m.
  Proof.
    intros [vnon0 eig]. split.
    intros contra. inversion contra. simpl in *.
    apply vnonzero in vnon0.
    destruct v as [v1 v2].
    destruct vnon0; simpl in *.
    apply (zero_rule1 0 [*]) in H6. tauto.
    apply (zero_rule1 0 [*]) in H7. tauto.
    rewrite vmult_scvec.
    rewrite scvec_swap.
    apply lmod_proper. reflexivity. assumption. (* fixme: rewrite eig. runs into the weeds *)
  Qed.

  Lemma det_zero (m : mat) :
    det m ≡ 0 -> exists v : vec, v ≢ 0 /\ m ⋅ v ≡ 0.
  Proof.
    destruct m as [[[m11 m12] m21] m22].
    unfold det. intros.
    destruct (decide ((m22 ≡ 0))) as [eq|neq].
    assert ((m12 ≡ 0 \/ m21 ≡ 0)).
    { rewrite eq in H6. ring_simplify in H6. apply (zero_rule1 0 [*]). apply opp_0. rewrite opp_mul_l. assumption. }
    destruct (decide (m12 ≡ 0)).
    - exists [ 0 , 1]. split. apply vnonzero. right. intros contra. apply dom_non_trivial. symmetry. assumption.
      rewrite eq, e. auto_mat.
    - assert (m21 ≡ 0) by tauto.
      exists [ m12 , -m11]. split. apply vnonzero. left; assumption. rewrite eq, H8; auto_mat.
    - exists [ m22 , - m21 ]. split. apply vnonzero; left; assumption. auto_mat. rewrite <- opp_mul_r. assumption.
  Qed.

  Lemma eig_pol (l : R) (m : mat) :
    det (m - l ⋅ 1) ≡ 0 -> eig_val l m.
  Proof.
    intros. apply det_zero in H6.
    destruct H6 as [v [vnon0 eq]].
    unfold det. exists v. split. assumption.
    rewrite (left_act_exch (⋅) (+) (+)) in eq.
    apply opp_unique_r in eq. rewrite <- opp_act in eq.
    apply opp_inj in eq.
    rewrite scmat_vmult_swap in eq.
    rewrite (left_act_id (1 : mat) (⋅)) in eq.
    symmetry. assumption.
  Qed.

End Eigen.

Require Import Hierarchy.BigOp.

(* Notation big_mul_rev := (@big_op_rev _ op2 id2). *)
(* Notation big_mmult_rev := (@big_op_rev (mat _) mmult I). *)
(* Notation big_mmult_rev0 := (fun n f => @big_op_rev _ mmult I f 0 n). *)
