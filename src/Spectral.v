From Coq Require Import List Rbase Reals QArith micromega.Lia micromega.Lra.

From BY Require Import Rlemmas Tactics Hierarchy Matrix Impl.

Local Open Scope R_scope.

Local Open Scope group_scope.
Local Open Scope ring_scope.
Local Open Scope lmodule_scope.

Local Open Scope list_scope.

Local Open Scope mat_scope.
Local Open Scope vec_scope.

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

Definition normal_vec v := (/ vec_norm v) ⋅ v.

Ltac rify_all := cbv [ring_op abelian_group_op Rplus_abelian_group_op abelian_group_opp Rmult_ring_op
                          Ropp_abelian_group_opp abelian_group_id Rzero_abelian_group_id ring_id Rone_ring_id] in *.
Ltac rify_in H := cbv [ring_op abelian_group_op Rplus_abelian_group_op abelian_group_opp Rmult_ring_op
                               Ropp_abelian_group_opp abelian_group_id Rzero_abelian_group_id ring_id Rone_ring_id] in H.
Ltac rify := cbv [ring_op abelian_group_op Rplus_abelian_group_op abelian_group_opp Rmult_ring_op
                          Ropp_abelian_group_opp abelian_group_id Rzero_abelian_group_id ring_id Rone_ring_id].

Lemma inner_nonzero v : v <> v0 -> ⟨ v , v ⟩ <> 0.
Proof. intros; auto_mat; apply vnonzero in H; simpl. cbv in *. nra. Qed.

Lemma ort_span v w (Hv : v <> v0) (Hw : w <> v0) : ort v w -> forall u, exists μ ν, μ ⋅ v + ν ⋅ w = u.
Proof.
  intros.
  exists (⟨ u , v ⟩ / ⟨ v , v ⟩), (⟨ u , w ⟩ / ⟨ w , w ⟩).

  unfold ort in H. auto_mat. unfold inner in *; cbv; cbv in H. apply f_equal2. field_simplify. apply eq_div.

  apply vnonzero in Hv.
  apply vnonzero in Hw.

  change 0 with R0 in *.
  destruct Hv; destruct Hw.

  assert (0 < r3 ^ 2 * r1 ^ 2). apply Rmult_lt_0_compat; nra. nra.
  assert (0 < r3 ^ 2 * r2 ^ 2). apply Rmult_lt_0_compat; nra. nra.
  assert (0 < r4 ^ 2 * r1 ^ 2). apply Rmult_lt_0_compat; nra. nra.
  assert (0 < r4 ^ 2 * r2 ^ 2). apply Rmult_lt_0_compat; nra. nra.

  simpl in H; psatz R.

  split; apply vnonzero in Hv; apply vnonzero in Hw; change 0 with R0 in *.
  nra. nra.

  field_simplify. apply eq_div.

  apply vnonzero in Hv.
  apply vnonzero in Hw.

  change 0 with R0 in *.
  destruct Hv; destruct Hw.

  assert (0 < r3 ^ 2 * r1 ^ 2). apply Rmult_lt_0_compat; nra. nra.
  assert (0 < r3 ^ 2 * r2 ^ 2). apply Rmult_lt_0_compat; nra. nra.
  assert (0 < r4 ^ 2 * r1 ^ 2). apply Rmult_lt_0_compat; nra. nra.
  assert (0 < r4 ^ 2 * r2 ^ 2). apply Rmult_lt_0_compat; nra. nra.

  simpl in H; psatz R.

  split; apply vnonzero in Hv; apply vnonzero in Hw; change 0 with R0 in *; nra. Qed.

Lemma vnonzero_norm v :
  v <> v0 <-> vec_norm v <> 0.
Proof.
  split.
  intros. unfold vec_norm.
  destruct v as [ v1 v2 ].
  apply vnonzero in H. intros contra. apply sqrt_eq_0 in contra. rify_all. nra. nra.

  destruct v as [ v1 v2 ].
  intros. unfold vec_norm in H.
  intros contra.
  inversion_mat contra. subst. rify_all.
  replace (R0 ^ 2 + R0 ^ 2)%R with 0%R in H by nra. rewrite sqrt_0 in H. contradiction. Qed.

Lemma mat_norm_nonneg m :
  0 <= mat_norm m .
Proof. auto_mat. apply sqrt_pos. Qed.

Lemma vec_norm_nonneg v :  0 <= vec_norm v.
Proof. auto_mat. apply sqrt_pos. Qed.

Lemma vec_norm_pos_nonneg v (vnon0 : v <> v0) : 0 < vec_norm v.
Proof. pose proof vnonzero_norm v. pose proof vec_norm_nonneg v. apply H in vnon0. rify_all. lra. Qed.

(************************************************************************************************)
(** This files contains a formal proof of the spectral theorem of 2x2 matrices over the R type  *)
(** It furthermore contains proofs of properties of the operator norm on 2x2 matrices which use *)
(** eigenvalues and the spectral theorem.                                                       *)
(************************************************************************************************)

Lemma inner_vec_norm v :
  (vec_norm v) ^ 2 = ⟨ v , v ⟩.
Proof. unfold vec_norm.
       destruct v as [v1 v2].
       rewrite pow2_sqrt; cbv. nra. nra. Qed.

Lemma vec_norm_scvec a v : vec_norm (a ⋅ v) = (Rabs a * vec_norm v)%R.
Proof.
  unfold vec_norm. destruct v as [v1 v2]. simpl. cbv [ring_op Rmult_ring_op].
  replace (a * v1 * (a * v1 * 1) + a * v2 * (a * v2 * 1))%R with (a ^ 2 * (v1 ^ 2 + v2 ^ 2))%R by nra.
  rewrite sqrt_mult_alt.
  rewrite <- Rsqr_pow2.
  rewrite sqrt_Rsqr_abs.
  apply f_equal2. reflexivity.
  apply f_equal. nra. nra. Qed.

Definition sym_eig1 (m : mat) :=
  let '(a, b, c, d) := m in
  (a + d + sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2.

Definition sym_eig2 (m : mat) :=
  let '(a, b, c, d) := m in
  (a + d - sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2.

Lemma sym_eig1_eig m :
  sym m -> eig_val (sym_eig1 m) m.
Proof.
  intros. auto_mat.
  inversion H. apply eig_pol. simpl. rify. field_simplify. apply eq_div. lra.
  rewrite pow2_sqrt. nra. psatz R. Qed.

Lemma sym_eig2_eig m :
  sym m -> eig_val (sym_eig2 m) m.
Proof.
  intros. auto_mat.
  inversion H. apply eig_pol. simpl. rify. field_simplify. apply eq_div. lra.
  rewrite pow2_sqrt. nra. psatz R. Qed.

Lemma mat_norm_eig m :
  (mat_norm m) ^ 2 = sym_eig1 (m ^T * m).
Proof.
  destruct m as [[[m11 m12] m21] m22].
  unfold mat_norm.

  rewrite pow2_sqrt.
  auto_mat. rify. rewrite !Rmult_1_r.

  apply f_equal2. apply f_equal2. lra.

  apply sqr_inj. apply sqrt_positivity. psatz R.
  apply sqrt_positivity. psatz R.
  rewrite !pow2_sqrt.  nra. psatz R. psatz R. lra.
  assert_pow. assert_sqrt. nra. Qed.

Lemma m0_scalar_matrix m : ~ scalar_matrix m -> m <> m0.
Proof. intros. intros contra. apply H. exists 0. auto_mat; inversion contra. rewrite act_0_l. reflexivity. Qed.

Lemma sym_eig12 m :
  ~ scalar_matrix m -> sym m -> sym_eig1 m <> sym_eig2 m.
Proof.
  intros not_sc_mat msym.
  pose proof m0_scalar_matrix m not_sc_mat as mnon0.
  unfold sym_eig1, sym_eig2. auto_mat.
  apply mnonzero in mnon0. unfold sym in msym. inversion msym. subst.
  intros contra.
  assert (sqrt ((r - r2) ^ 2 + 4 * r1 ^ 2) = R0). rify. nra.
  apply sqrt_eq_0 in H.
  assert (r - r2 = 0). rify. nra.
  assert (r1 = 0). rify_all. nra. assert (r = r2)%R. nra. subst.
  apply not_sc_mat. exists r2. cbv; auto_mat. psatz R. Qed.

Lemma sym_eig12_ineq m :
  sym_eig2 m <= sym_eig1 m.
Proof. auto_mat. unfold sym_eig1, sym_eig2.
       apply Rle_div_r. nra. field_simplify. assert_pow; assert_sqrt. nra. Qed.

Lemma is_scalar_matrix m : scalar_matrix m \/ ~ scalar_matrix m.
Proof.
  destruct m as [[[m11 m12] m21] m22].
  destruct (Req_dec m11 m22).
  destruct (Req_dec m12 0).
  destruct (Req_dec m21 0).
  - left; exists m11. subst; cbv; auto_mat.
  - right; intros contra. destruct contra. inversion_mat H2. nra.
  - right; intros contra. destruct contra. inversion_mat H1. rify_all. cbv [ring_op R] in *. nra.
  - right; intros contra. destruct contra. inversion_mat H0. nra. Qed.

Lemma normal_vec_norm v (vnon0 : v <> v0) : vec_norm (normal_vec v) = 1.
Proof.
  pose proof vec_norm_nonneg v.
  pose proof (proj1 (vnonzero_norm v)) vnon0.
  unfold normal_vec. rewrite vec_norm_scvec. rewrite Rabs_pos_eq. rify. field. assumption.
  apply inv_pos. nra. Qed.

Lemma normal_vec_nonzero v (vnon0 : v <> v0) : normal_vec v <> v0.
Proof. apply vnonzero_norm. rewrite normal_vec_norm. intros contra. apply non_trivial. symmetry; assumption. assumption. Qed.

Theorem spectral m :
  sym m -> exists u v , eig_vec (sym_eig1 m) u m /\ eig_vec (sym_eig2 m) v m /\ ort u v /\ vec_norm u = 1 /\ vec_norm v = 1.
Proof.
  destruct (is_scalar_matrix m) as [[x]|]; intros msym.
  - inversion_mat H.
    exists [ 1 ; 0 ], [ 0 ; 1 ]. repeat split.
    + apply vnonzero. rify. nra.
    + cbv [module_left_act scvec_left_act vmult_left_act].
      auto_mat.
       rify. rewrite !Rmult_1_r, !Rmult_0_r, !Rplus_0_r. replace (x - x)%R with 0%R.
        rewrite Rmult_0_r.
        rewrite sqrt_0. nra. nra. rify. nra.
    + auto_mat. intros contra. inversion contra. rify_all. nra.
    + cbv [module_left_act scvec_left_act vmult_left_act]. auto_mat.
      rify. nra.  rewrite !Rmult_1_r, !Rmult_0_r, !Rplus_0_r. replace (x - x)%R with 0%R.
      rewrite Rmult_0_r.
      rewrite sqrt_0. rify. nra. nra.
    + unfold ort, inner. rify. nra.
    + unfold vec_norm. rify. replace (R1 ^ 2 + R0 ^ 2)%R with 1%R by nra. apply sqrt_1.
    + unfold vec_norm. rify. replace (R0 ^ 2 + R1 ^ 2)%R with 1%R by nra. apply sqrt_1.
  - pose proof sym_eig1_eig m msym as [u eig1].
    pose proof sym_eig2_eig m msym as [v eig2].
    exists (normal_vec u), (normal_vec v).
    split; [|split; [|split; [|split]]].
    unfold normal_vec.
    apply eig_vec_scvec. apply Rinv_neq_0_compat.
    apply vnonzero_norm. apply eig1. assumption.
    apply eig_vec_scvec. apply Rinv_neq_0_compat.
    apply vnonzero_norm. apply eig2. assumption.
    apply ort_scvec. eapply eig_sym_ort. apply msym. apply sym_eig12.
    apply H. assumption.  assumption. assumption. apply normal_vec_norm.
    apply eig1. apply normal_vec_norm. apply eig2. Qed.

Lemma max_inequality a b c d :
  (d <= c -> 0 <= a -> 0 <= b -> a + b = 1 -> a * c + b * d <= c)%R.
Proof. nra. Qed.

Lemma mat_norm_spec1 m v :
  vec_norm v = 1 -> vec_norm (m ⋅ v) <= mat_norm m.
Proof.
  intros. rewrite <- Rabs_pos_eq by apply mat_norm_nonneg.

  apply (le_pow 2). lia.
  rewrite mat_norm_eig.
  assert (Psym : sym (m ^T * m)) by (unfold sym; cbv; auto_mat).
  pose proof spectral _ Psym as [e1 [e2 [[e1non0 eig1] [[e2non0 eig2] [ort12 [norm1 norm2]]]]]].

  pose proof (ort_span _ _ e1non0 e2non0 ort12) v as [c1 [c2 eq]].
  rewrite <- eq. rewrite inner_vec_norm. rewrite trans_adj.
  rewrite inner_plus_r, !inner_mult_r.
  rewrite <- !left_action.
  rewrite <- !sym_self_adj by assumption.
  rewrite !inner_plus_l, !inner_mult_l.
  rewrite eig1, eig2. rewrite !inner_mult_r.
  rewrite (inner_sym e2 e1).
  rewrite <- !inner_vec_norm, ort12, norm1, norm2. rify. field_simplify.
  apply max_inequality. apply sym_eig12_ineq. nra. nra.

  rewrite <- eq in H. apply (f_equal (fun x => pow x 2)) in H.
  cbv [ring_id Rone_ring_id] in H.
  replace (R1 ^ 2) with 1%R in H by nra.
  rewrite inner_vec_norm in H.
  rewrite !inner_plus_l, !inner_plus_r, !inner_mult_l, !inner_mult_r in H.
  rewrite (inner_sym e2 e1) in H.
  rewrite <- !inner_vec_norm, ort12, norm1, norm2 in H. rify_in H. nra. Qed.

Lemma e1_norm :
  vec_norm [1; 0] = 1.
Proof.
  unfold vec_norm. rewrite pow_i, pow1, Rplus_0_r, sqrt_1 by lia. reflexivity. Qed.

Lemma mat_norm_spec2 m a :
  (forall v, vec_norm v = 1 -> vec_norm (m ⋅ v) <= a) -> (mat_norm m <= a).
Proof.
  intros.
  assert (0 <= a).
  { specialize (H [1; 0] e1_norm). etransitivity. apply vec_norm_nonneg. apply H. }
  rewrite <- Rabs_pos_eq by assumption.
  apply (le_pow 2). lia.

  rewrite mat_norm_eig.
  assert (Psym : sym (m ^T * m)) by (unfold sym; cbv; auto_mat).
  pose proof spectral _ Psym as [e1 [e2 [[e1non0 eig1] [[e2non0 eig2] [ort12 [norm1 norm2]]]]]].
  specialize (H e1 norm1).
  rewrite <- (Rabs_pos_eq (vec_norm _)) in H by apply vec_norm_nonneg.
  apply pow_maj_Rabs with (n:=2%nat) in H.
  rewrite inner_vec_norm, trans_adj in H.
  rewrite <- !left_action in H.
  rewrite eig1 in H. rewrite inner_mult_l in H.
  rewrite <- !inner_vec_norm, norm1 in H. rify_all. lra. Qed.

Lemma vec_norm_v0 : vec_norm 0 = 0.
Proof. change (@abelian_group_id vec _) with v0. auto_mat. rewrite Rmult_0_l, Rplus_0_l. apply sqrt_0. Qed.

Lemma mat_norm_condition (P : mat) (N : R) :
  let '(P11, P12, P21, P22) := P in
  let a := P11 ^ 2 + P12 ^ 2 in
  let b := P11 * P21 + P12 * P22 in
  let c := P11 * P21 + P12 * P22 in
  let d := P21 ^ 2 + P22 ^ 2 in
  mat_norm P <= N <-> (0 <= N)
                   /\ a + d <= 2 * N ^ 2
                   /\ (a - d) ^ 2 + 4 * b ^ 2 <= (2 * N ^ 2 - a - d) ^ 2.
Proof.
  pose proof (mat_norm_nonneg P).
  destruct P as [[[P11 P12] P21] P22].
  unfold mat_norm; rify.
  assert_pow; assert_sqrt.
  split; intros.
  - assert (0 <= N) by lra.
    rewrite <- (Rabs_pos_eq (sqrt _)) in H10 by lra.
    apply (pow_maj_Rabs _ _ 2) in H10.

    rewrite <- Rsqr_pow2, Rsqr_sqrt in H10.
    repeat split. lra. lra.
    apply sqrt_le_0. lra. lra.
    rewrite <- (Rsqr_pow2 (_ - _ - _)), sqrt_Rsqr; lra. nra.
  - destruct H10 as [H11 [H12 H13]].
    apply sqrt_le_1 in H13.
    rewrite <- (Rsqr_pow2 (_ - _ - _)) in H13. rewrite sqrt_Rsqr in H13.
    replace N with (Rabs N) by (apply Rabs_pos_eq; assumption).
    apply le_pow with (n := 2%nat). replace (INR 2%nat) with 2 by reflexivity. lia.
    rewrite <- Rsqr_pow2, Rsqr_sqrt. all: lra. Qed.


(***************************************************************)
(** Note that this theorem has an equational proof in Matrix.v *)
(***************************************************************)

Lemma mat_norm_vmult m v :
  vec_norm (m ⋅ v) <= mat_norm m * vec_norm v.
Proof.
  destruct (vec_eq_dec v 0).
  - subst. rewrite act_0_r. rewrite vec_norm_v0. rify. nra.
  - replace v with (vec_norm v ⋅ normal_vec v).
    rewrite vmult_scvec. rewrite scmat_vmult.
    rewrite !vec_norm_scvec. rewrite (Rmult_comm (mat_norm m)).
    rewrite normal_vec_norm.
    pose proof mat_norm_spec1 m _ (normal_vec_norm _ n).
    pose proof Rabs_pos (vec_norm v). rify_all. nra. assumption.
    unfold normal_vec. rewrite scvec_scvec.
    rewrite Rinv_r. change (IZR _) with (@ring_id R _). apply act_1_l. apply vnonzero_norm. assumption.
    Qed.

(*************************************************************************)
(** Note that this theorem DOES NOT have an equational proof in Matrix.v *)
(** Neither does mat_norm_spec2 (which this is a corollary of.           *)
(** The reason for this is plainly that the norm of a product of         *)
(** matrices have a terribly unhandy equation which several sqrt term.   *)
(** I am certain that you can come up with a pure algebraic proof of     *)
(** this theorem though I am uncertaing how it looks.                    *)
(*************************************************************************)

Lemma mat_norm_mmult n m :
  mat_norm (n * m) <= mat_norm n * mat_norm m.
Proof.
  apply mat_norm_spec2.
  intros.
  rewrite left_action, mat_norm_vmult.
  pose proof (mat_norm_vmult m v). rewrite H in H0.
  pose proof (mat_norm_nonneg n).
  pose proof (mat_norm_nonneg m). rify_all. nra.
Qed.

Lemma mat_norm_scmat m a :
  mat_norm (a ⋅ m) = Rabs a * mat_norm m.
Proof.
  pose proof (mat_norm_nonneg m).
  destruct m as [[[m11 m12] m21] m22].
  cbv [module_left_act scmat_left_act scmat mat_norm].
  rewrite <- sqrt_Rsqr_abs.
  rewrite <- sqrt_mult; try assumption. apply f_equal.
  rewrite Rsqr_pow2. rify.
  field_simplify. apply f_equal2.
  apply f_equal2. reflexivity.
  rewrite <- (Rsqr_pow2 a).
  rewrite Rsqr_abs.
  rewrite Rsqr_pow2.
  rewrite RPow_abs.
  rewrite <- sqrt_Rsqr_abs.
  rewrite <- sqrt_mult.
  apply f_equal.
  rewrite Rsqr_pow2. field.
  apply Rle_0_sqr.
  assert_pow. lra. reflexivity.
  apply Rle_0_sqr.
  assert_pow. assert_sqrt.
  lra. Qed.
