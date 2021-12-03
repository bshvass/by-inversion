Require Import ZArith micromega.Lia ZArith.Zhints.

From BY Require Import Matrix Hierarchy Impl Tactics.

Local Open Scope Z.
Local Open Scope mat_scope.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope lmodule_scope.

Definition ratchet M :=
  (0 < det M) /\
  let '(m11, m12, m21, m22) := M in
  (0 <= m11) /\ (0 <= m12).

Section __.

  Context
    {M : nat -> mat}
    `{forall i, ratchet (M i)}.

Notation big_mmult_rev := (fun n m f => @big_op_rev _ mmult I f n m).
Notation T i := (big_mmult_rev 0%nat i M).

Lemma T_pos_det i :
  0 < det (T i).
Proof.
  induction i.
  + reflexivity.
  + rewrite big_op_rev_S_l by lia. rewrite det_mul.
    specialize (H i).
    unfold ratchet in H. zify_all.
    destruct H. nia.
Qed.

Lemma sgn_lem i f g :
  Z.sgn (det [f, 0; g, 1]) = Z.sgn (det ((T i) * [f, 0; g, 1])).
Proof.
  rewrite det_mul.
  rewrite Z.sgn_mul.
  pose proof T_pos_det i. lia.
Qed.

Definition msb f :=
  if (Z_le_dec 0 f) then 1 else -1.

Lemma msb_sgn f :
  f <> 0 -> Z.sgn f = msb f.
Proof.
  intros.
  unfold msb.
  destruct_ifs. zify_all. lia.
  lia. Qed.

Lemma msb_mul a f :
  a <> 0 -> f <> 0 -> msb (a * f) = msb a * msb f.
Proof.
  intros; unfold msb; destruct_ifs; zify_all; try lia.
Qed.

Lemma msb_pos f :
  0 < f -> msb f = 1.
Proof. unfold msb; destruct_ifs; lia. Qed.

(* Lemma ratchet_lemma M N v : *)
(*   let '(a, b, c, d) := M in *)
(*   let '( *)

Theorem ratched_spec f g :
  f <> 0 \/ g > 0 ->
  let '(a0, b0, c0, d0) := T 0%nat in
  forall i,
    let '(ai, bi, ci, di) := T i in
    let '(fi, gi) := (T i) ⋅ (f, g) in
    (0 <= bi) <-> (msb fi = msb f).
Proof.
  intros.
  destruct (T 0%nat) as [[[a0 b0] c0] d0] eqn:E. intros.
  induction i.
  - simpl. zify.
    rewrite Z.mul_1_l, Z.mul_0_l, Z.add_0_r. intuition.
-
  pose proof (sgn_lem i f g). simpl in H1.
  pose proof (sgn_lem (S i) f g). simpl in H2. zify_all.
  destruct (Matrix.big_mmult_rev M 0 i) as [[[ai bi] ci] di] eqn:E2.
  set (fi := ai * f + bi * g).
  set (gi := ci * f + di * g).
  destruct (Matrix.big_mmult_rev M 0 (S i)) as [[[asi bsi] csi] dsi] eqn:E3.
  set (fsi := asi * f + bsi * g).
  set (gsi := csi * f + dsi * g).
  assert (((ai, bi, ci, di) * (f, 0, g, 1)) = [fi, bi; gi, di]).
  { cbn; unfold fi, gi; zify; auto_mat. }
  assert (((asi, bsi, csi, dsi) * (f, 0, g, 1)) = [fsi, bsi; gsi, dsi]).
  { cbn; unfold fsi, gsi; zify; auto_mat. }
  simpl in *.
  zify_all. simpl in *.
  zify_all.
  rewrite !Z.mul_0_r, !Z.mul_1_r, !Z.add_0_l in *.
  replace (ai * f + bi * g)%Z with fi in *.
  (* rewrite H3 in H1. *)
  (* rewrite H4 in H2. *)

  rewrite big_op_rev_S_l in E3 by lia.
  rewrite E2 in E3.

  destruct (M i) as [[[a b] c] d] eqn:E4.
  destruct (Z.eq_dec b 0); subst.
  +
  assert (0 < a * d /\ 0 < d /\ 0 < a).
  { specialize (H i). unfold ratchet in *. rewrite E4 in H.
    simpl in H. zify_all.
    split. lia.
    split. lia.
    assert (0 < d) by lia. lia. }

  inversion E3. zify_all. rewrite !Z.mul_0_l, !Z.add_0_r in *.
  split.
  * intros.
    assert (0 <= bi). clear -H5 H6. lia.
    apply IHi in H11. clear -H11 H5.
    replace (a * ai * f + a * bi * g)%Z with (a * fi)%Z by lia.
    destruct (Z.eq_dec fi 0). rewrite e in *. rewrite Z.mul_0_r. assumption.
    rewrite msb_mul. rewrite msb_pos by lia. zify. lia. zify_all. lia. assumption.
  * intros.
    assert (msb (ai * f + bi * g) = msb f).
    { clear -H5 H6 fi.
    fold fi.
    replace (a * ai * f + a * bi * g)%Z with (a * fi)%Z in * by lia.
    destruct (Z.eq_dec fi 0). rewrite e in *. rewrite Z.mul_0_r in *. assumption.
    rewrite msb_mul in *. rewrite msb_pos in * by lia. zify_all. lia. zify_all. lia. assumption. }
    apply IHi in H11. clear -H11 H5. nia.
  +
    destruct (Z.eq_dec f 0). subst. Search Z.sgn. simpl.
    Admitted.

(*   assert (0 < a * d /\ 0 < d /\ 0 < a). *)
(*   { specialize (H i). unfold ratchet in *. rewrite E4 in H. *)
(*     simpl in H. zify_all. *)
(*     split. lia. *)
(*     split. lia. *)
(*     assert (0 < d) by lia. lia. } *)

(*   inversion E3. zify_all. rewrite !Z.mul_0_l, !Z.add_0_r in *. *)
(*     split. *)
(*     * *)
(*       intros. *)
(*       apply IHi in H5. *)

(* .     *)

(*   assert (0 < d). *)

(*   inversion E3. subst. zify_all. *)
(*   simpl in E3. *)

(*   cbn in E3. *)
(*   zify_in E3. *)

(*   induction i. *)
(*   cbn in E, E2. zify_all. *)
(*   inversion E. inversion E2. subst. *)
(*   rewrite Z.mul_1_l, Z.mul_0_l, Z.add_0_r. simpl. intuition. *)



(*   simpl in H1. *)
(*   zify_all. *)
(*   rewrite !Z.mul_1_r, !Z.mul_0_r, Z.opp_0, !Z.add_0_r in H1. *)


(*   Print Hint. *)
(*   autorewrite with zarith in H1. *)
(*   assert T i * [f, g; 0, 1] = []) *)
(*   split_pairs. *)
(*   assert ((z5, z6, z4, z3) * (f, g, 0, 1))) *)
(*   cbn in H2. zify_all. *)
(*   ring_simplify in H2. *)
(*   assert (det (T i) > 0). *)
(*   { induction i. *)
(*     { reflexivity. } *)
(*     { rewrite big_op_rev_S_l by lia. rewrite det_mul. *)

(*   } } *)
