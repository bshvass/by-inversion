From Coq Require Import List Rbase Reals QArith micromega.Lia micromega.Lra.

From BY Require Import Rlemmas Tactics SetoidRewrite Matrix.

Local Open Scope R_scope.
Local Open Scope list_scope.

Local Open Scope mat_scope.
Local Open Scope vec_scope.


Lemma vec_eq_dec (v w : vec) : (v = w) \/ v <> w.
Proof. auto_mat; destruct (Req_dec r1 r); destruct (Req_dec r2 r0); tauto. Qed.

Lemma scmat_vmult (l : R) (v : vec) (m : mat) :
  l ** m *v v = l **v (m *v v).
Proof. auto_mat. Qed.

Lemma vmult_scvec (l : R) (v : vec) (m : mat) :
  m *v (l **v v) = l ** m *v v.
Proof. auto_mat. Qed.

Lemma scvec_vmult l v m :
  l **v (m *v v) = l ** m *v v.
Proof. auto_mat. Qed.

Lemma vmult_I_l v : I *v v = v.
Proof. auto_mat. Qed.

Lemma vmult_mminus_distr_r m1 m2 v :
  (m1 - m2) *v v = m1 *v v -v m2 *v v.
Proof. auto_mat. Qed.


Lemma mnonzero m11 m12 m21 m22 :
  m11 <> 0 \/ m12 <> 0 \/ m21 <> 0 \/ m22 <> 0 <-> [ m11 , m12 ; m21 , m22 ] <> m0.
Proof. split. intros [m110 | [m120 | [m210 | m220]]] m_not0; inversion m_not0; contradiction.
       destruct (Req_dec m11 0); destruct (Req_dec m12 0); destruct (Req_dec m21 0); destruct (Req_dec m22 0); subst; try tauto.
Qed.

Lemma inner_mult_r μ v w :
  ⟨ v , μ **v w ⟩ = (μ * ⟨ v , w ⟩)%R.
Proof. auto_mat. Qed.

Lemma inner_mult_l ν v w :
  ⟨ ν **v v , w ⟩ = (ν * ⟨ v , w ⟩)%R.
Proof. auto_mat. Qed.

Lemma inner_plus_r u v w :
  ⟨ u , v +v w ⟩ = (⟨ u , v ⟩ + ⟨ u , w ⟩)%R.
Proof. auto_mat. Qed.

Lemma inner_plus_l u v w :
  ⟨ u +v v , w ⟩ = (⟨ u , w ⟩ + ⟨ v , w ⟩)%R.
Proof. auto_mat. Qed.

Lemma inner_sym u v :
  ⟨ u , v ⟩ = ⟨ v , u ⟩.
Proof. auto_mat. Qed.

Lemma inner_vec_norm v :
  (vec_norm v) ^ 2 = ⟨ v , v ⟩.
Proof. unfold vec_norm.
       destruct v as [v1 v2].
       rewrite pow2_sqrt. simpl; nra. nra. Qed.


Lemma vec_norm_scvec a v : vec_norm (a **v v) = (Rabs a * vec_norm v)%R.
Proof.
  unfold vec_norm. destruct v as [v1 v2]. simpl.
  replace (a * v1 * (a * v1 * 1) + a * v2 * (a * v2 * 1))%R with (a ^ 2 * (v1 ^ 2 + v2 ^ 2))%R by nra.
  rewrite sqrt_mult_alt.
  rewrite <- Rsqr_pow2.
  rewrite sqrt_Rsqr_abs.
  apply f_equal2. reflexivity.
  apply f_equal. nra. nra. Qed.


Lemma det_zero m :
  det m = 0 -> exists v, v <> v0 /\ m *v v = v0.
Proof.
  destruct m as [[[m11 m12] m21] m22].
  unfold det. intros.
  destruct (Req_dec m22 0).
  assert (m12 = 0 \/ m21 = 0). nra.
  destruct (Req_dec m12 0).
  - exists [ 0 ; 1]. split. apply vnonzero. right; lra. auto_mat.
  - assert (m21 = 0) by tauto.
    exists [ m12 ; -m11]. split. apply vnonzero. left; lra. auto_mat.
  - exists [ m22 ; - m21 ]. split. apply vnonzero; left; lra. auto_mat. Qed.

Lemma ort_scvec_r u v ν : ort u v -> ort u (ν **v v).
Proof. unfold ort; intros; rewrite inner_mult_r; nra. Qed.

Lemma ort_scvec_l u v μ : ort u v -> ort (μ **v u) v.
Proof. unfold ort; intros; rewrite inner_mult_l; nra. Qed.

Lemma ort_scvec u v μ ν : ort u v -> ort (μ **v u) (ν **v v).
Proof. unfold ort; intros; rewrite inner_mult_l, inner_mult_r; nra. Qed.

Lemma scvec_scvec μ ν v :
  μ **v (ν **v v) = (μ * ν) **v v.
Proof. auto_mat. Qed.

Lemma eig_vec_scvec l v m x (xnon0 : x <> 0) :
  eig_vec l v m -> eig_vec l (x **v v) m.
Proof.
  intros [vnon0 eig]. split.
  auto_mat. apply vnonzero in vnon0. apply vnonzero. nra.
  rewrite vmult_scvec.
  rewrite scmat_vmult. rewrite eig.
  rewrite scvec_scvec. rewrite Rmult_comm.
  rewrite scvec_scvec. reflexivity. Qed.

Lemma eig_pol l m :
  det (m - l ** I) = 0 -> eig_val l m.
Proof.
  intros. apply det_zero in H.
  destruct H as [v [vnon0 eq]].
  unfold det. exists v. split. assumption.
  inversion_mat eq. auto_mat. psatz R. Qed.

Lemma inner_nonzero v : v <> v0 -> ⟨ v , v ⟩ <> 0.
Proof. intros; auto_mat; apply vnonzero in H; simpl; nra. Qed.

Lemma ort_span v w (Hv : v <> v0) (Hw : w <> v0) : ort v w -> forall u, exists μ ν, μ **v v +v ν **v w = u.
Proof.
  intros.
  exists (⟨ u , v ⟩ / ⟨ v , v ⟩), (⟨ u , w ⟩ / ⟨ w , w ⟩).

  unfold ort in H. auto_mat. field_simplify. apply eq_div.

  apply vnonzero in Hv.
  apply vnonzero in Hw.

  destruct Hv; destruct Hw.

  assert (0 < r3 ^ 2 * r1 ^ 2). apply Rmult_lt_0_compat. nra. nra. nra.
  assert (0 < r3 ^ 2 * r2 ^ 2). apply Rmult_lt_0_compat. nra. nra. nra.
  assert (0 < r4 ^ 2 * r1 ^ 2). apply Rmult_lt_0_compat. nra. nra. nra.
  assert (0 < r4 ^ 2 * r2 ^ 2). apply Rmult_lt_0_compat. nra. nra. nra.

  simpl in H; psatz R.

  split; apply vnonzero in Hv; apply vnonzero in Hw; nra.

  field_simplify. apply eq_div.

  apply vnonzero in Hv.
  apply vnonzero in Hw.

  destruct Hv; destruct Hw.

  assert (0 < r3 ^ 2 * r1 ^ 2). apply Rmult_lt_0_compat; nra. nra.
  assert (0 < r3 ^ 2 * r2 ^ 2). apply Rmult_lt_0_compat; nra. nra.
  assert (0 < r4 ^ 2 * r1 ^ 2). apply Rmult_lt_0_compat; nra. nra.
  assert (0 < r4 ^ 2 * r2 ^ 2). apply Rmult_lt_0_compat; nra. nra.

  simpl in H; psatz R.

  split; apply vnonzero in Hv; apply vnonzero in Hw; nra. Qed.

Lemma trans_adj m v w : ⟨ v , m *v w ⟩ = ⟨ m ^T *v v , w ⟩.
Proof. auto_mat. Qed.

Lemma sym_self_adj m v w : sym m -> ⟨ v , m *v w ⟩ = ⟨ m *v v , w ⟩.
Proof. unfold sym; intros msym. rewrite msym at 2. apply trans_adj. Qed.

Lemma eig_sym_ort μ ν v w m :
  sym m -> μ <> ν -> eig_vec μ v m -> eig_vec ν w m -> ort v w.
Proof.
  intros msym neq [vnon0 veig] [wnon0 weig]. auto_mat.
  unfold ort.
  assert (ν * ⟨ (r5, r6), (r3, r4) ⟩ = μ * ⟨ (r5, r6), (r3, r4) ⟩)%R.
  now rewrite <- inner_mult_r, <- weig, sym_self_adj, veig, inner_mult_l.
  nra. Qed.

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
  inversion H. apply eig_pol. simpl. field_simplify. apply eq_div. lra.
  rewrite pow2_sqrt. nra. psatz R. Qed.

Lemma sym_eig2_eig m :
  sym m -> eig_val (sym_eig2 m) m.
Proof.
  intros. auto_mat.
  inversion H. apply eig_pol. simpl. field_simplify. apply eq_div. lra.
  rewrite pow2_sqrt. nra. psatz R. Qed.

Lemma mat_norm_eig m :
  (mat_norm m) ^ 2 = sym_eig1 (m ^T * m).
Proof.
  destruct m as [[[m11 m12] m21] m22].
  unfold mat_norm.

  rewrite pow2_sqrt.
  auto_mat. rewrite !Rmult_1_r.

  apply f_equal2. apply f_equal2. lra.

  apply sqr_inj. apply sqrt_positivity. psatz R.
  apply sqrt_positivity. psatz R.
  rewrite !pow2_sqrt.  nra. psatz R. psatz R. lra.
  assert_pow. assert_sqrt. nra. Qed.

Lemma m0_scalar_matrix m : ~ scalar_matrix m -> m <> m0.
Proof. intros. intros contra. apply H. exists 0. auto_mat; inversion contra; nra. Qed.

Lemma sym_eig12 m :
  ~ scalar_matrix m -> sym m -> sym_eig1 m <> sym_eig2 m.
Proof.
  intros not_sc_mat msym.
  pose proof m0_scalar_matrix m not_sc_mat as mnon0.
  unfold sym_eig1, sym_eig2. auto_mat.
  apply mnonzero in mnon0. unfold sym in msym. inversion msym. subst.
  intros contra.
  assert (sqrt ((r - r2) ^ 2 + 4 * r1 ^ 2) = 0). nra.
  apply sqrt_eq_0 in H.
  assert (r - r2 = 0)%R. nra.
  assert (r1 = 0). nra. assert (r = r2)%R. nra. subst.
  apply not_sc_mat. exists r2. auto_mat. psatz R. Qed.

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
  - left; exists m11. auto_mat.
  - right; intros contra. destruct contra. inversion_mat H2. nra.
  - right; intros contra. destruct contra. inversion_mat H1. nra.
  - right; intros contra. destruct contra. inversion_mat H0. nra. Qed.

Lemma normal_vec_norm v (vnon0 : v <> v0) : vec_norm (normal_vec v) = 1.
Proof.
  pose proof vec_norm_nonneg v.
  pose proof (proj1 (vnonzero_norm v)) vnon0.
  unfold normal_vec. rewrite vec_norm_scvec. rewrite Rabs_pos_eq. field. assumption.
  apply inv_pos. nra. Qed.

Lemma normal_vec_nonzero v (vnon0 : v <> v0) : normal_vec v <> v0.
Proof. apply vnonzero_norm. rewrite normal_vec_norm. nra. assumption. Qed.

Theorem spectral m :
  sym m -> exists u v , eig_vec (sym_eig1 m) u m /\ eig_vec (sym_eig2 m) v m /\ ort u v /\ vec_norm u = 1 /\ vec_norm v = 1.
Proof.
  destruct (is_scalar_matrix m) as [[x]|]; intros msym.
  - inversion_mat H.
    exists [ 1 ; 0 ], [ 0 ; 1 ]. repeat split.
    + apply vnonzero. nra.
    + auto_mat.
      field_simplify ((x * 1 - x * 1) * ((x * 1 - x * 1) * 1) + 4 * (x * 0 * (x * 0 * 1)))%R.
      rewrite sqrt_0. nra.
    + apply vnonzero; nra.
    + auto_mat.
      field_simplify ((x * 1 - x * 1) * ((x * 1 - x * 1) * 1) + 4 * (x * 0 * (x * 0 * 1)))%R.
      rewrite sqrt_0. nra.
    + unfold ort, inner. nra.
    + unfold vec_norm. replace (1 ^ 2 + 0 ^ 2)%R with 1 by nra. apply sqrt_1.
    + unfold vec_norm. replace (0 ^ 2 + 1 ^ 2)%R with 1 by nra. apply sqrt_1.
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

Lemma mat_norm_spec m v :
  vec_norm v = 1 -> vec_norm (m *v v) <= mat_norm m.
Proof.
  intros. rewrite <- Rabs_pos_eq by apply mat_norm_nonneg.

  apply (le_pow 2). lia.
  rewrite mat_norm_eig.
  assert (Psym : sym (m ^T * m)) by (unfold sym; auto_mat).
  pose proof spectral _ Psym as [e1 [e2 [[e1non0 eig1] [[e2non0 eig2] [ort12 [norm1 norm2]]]]]].

  pose proof (ort_span _ _ e1non0 e2non0 ort12) v as [c1 [c2 eq]].
  rewrite <- eq. rewrite inner_vec_norm. rewrite trans_adj.
  rewrite inner_plus_r, !inner_mult_r.
  rewrite <- !mmult_vmult.
  rewrite <- !sym_self_adj by assumption.
  rewrite !inner_plus_l, !inner_mult_l.
  rewrite eig1, eig2. rewrite !inner_mult_r.
  rewrite (inner_sym e2 e1).
  rewrite <- !inner_vec_norm, ort12, norm1, norm2. field_simplify.
  apply max_inequality. apply sym_eig12_ineq. nra. nra.

  rewrite <- eq in H. apply (f_equal (fun x => pow x 2)) in H.
  replace (1 ^ 2) with 1 in H by nra.
  rewrite inner_vec_norm in H.
  rewrite !inner_plus_l, !inner_plus_r, !inner_mult_l, !inner_mult_r in H.
  rewrite (inner_sym e2 e1) in H.
  rewrite <- !inner_vec_norm, ort12, norm1, norm2 in H. nra. Qed.

Lemma vmult_v0 m : m *v v0 = v0.
Proof. auto_mat. Qed.

Lemma vec_norm_v0 : vec_norm v0 = 0.
Proof. auto_mat; field_simplify (0 * (0 * 1) + 0 * (0 * 1))%R; apply sqrt_0. Qed.

Lemma mat_norm_vmult m v :
  vec_norm (m *v v) <= mat_norm m * vec_norm v.
Proof.
  destruct (vec_eq_dec v v0).
  - subst. rewrite vmult_v0, vec_norm_v0. nra.
  - replace v with (vec_norm v **v normal_vec v).
    rewrite vmult_scvec. rewrite scmat_vmult.
    rewrite !vec_norm_scvec. rewrite (Rmult_comm (mat_norm m)).
    rewrite normal_vec_norm.
    pose proof mat_norm_spec m _ (normal_vec_norm _ H).
    pose proof Rabs_pos (vec_norm v). nra. assumption.
    unfold normal_vec. rewrite scvec_scvec.
    replace (vec_norm v * / vec_norm v)%R with 1%R. auto_mat.
    field. apply vnonzero_norm. assumption. Qed.
