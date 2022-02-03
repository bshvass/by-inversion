Require Import ZArith micromega.Lia micromega.Lqa ZArith.Zhints QArith Field Psatz.
From stdpp Require Import decidable.

Lemma not_or_l {P Q : Prop} `{Decision P} : ¬(P \/ Q) ↔ ¬P /\ ¬Q.
Proof. destruct (decide P); tauto. Qed.
Lemma not_or_r {P Q : Prop} `{Decision Q} : ¬(P \/ Q) ↔ ¬P /\ ¬Q.
Proof. destruct (decide Q); tauto. Qed.
Lemma imp_l {P Q : Prop} `{Decision P} : (P -> Q) <-> (not P ∨ Q).
Proof. destruct (decide P); tauto. Qed.
Lemma imp_r {P Q : Prop} `{Decision Q} : (P -> Q) <-> (not P ∨ Q).
Proof. destruct (decide Q); tauto. Qed.
Lemma not_imp_l {P Q : Prop} `{Decision P} : not(P -> Q) <-> (P /\ not Q).
Proof. destruct (decide P); tauto. Qed.
Lemma not_iff {P Q : Prop} `{Decision P, Decision Q} : not(P <-> Q) <-> ((P /\ not Q) \/ (Q /\ not P)).
Proof. destruct (decide P), (decide Q); tauto. Qed.

From BY Require Import Matrix Impl Tactics Q.
From BY.Hierarchy Require Import Definitions BigOp.

Section __.

Local Open Scope Q_scope.
Local Open Scope mat_scope.
Local Open Scope ring_scope.
Local Open Scope lmod_scope.

Definition ratchet M :=
  (0 < det M) /\
  let '(m11, m12, m21, m22) := M in
  (0 <= m21) /\ (0 <= m22).
Instance : Proper ((≡) ==> iff) ratchet.
Proof.
  do 2 red. intros. unfold ratchet.
  invert_mat. cbn in *. rewrite H1, H2, H0, H3. auto. Qed.

Definition msb f :=
  if (Qlt_le_dec f 0) then (-1)%Z else 1.
Instance : Proper (Qeq ==> eq) msb.
Proof. do 2 red; intros. unfold msb.
       destruct_ifs; (reflexivity || nra). Qed.

Lemma msb_mul a f :
  a ≢ 0 -> f ≢ 0 -> msb (a * f) = msb a * msb f.
Proof.
  intros; unfold msb; cbn in *; destruct_ifs; nra || reflexivity.
Qed.

Lemma msb0 : msb 0 = 1.
Proof. reflexivity. Qed.

Lemma msb_pos f :
  0 <= f <-> msb f = 1.
Proof. unfold msb; split; destruct_ifs; cbn in *; reflexivity || lra || lia. Qed.

Ltac invert_mat :=
  repeat match goal with
         | M : prod _ _ |- _ => destruct M
         | H : (@equiv _ (@prod_equiv _ _ _ _)) _ _ |- _  => inversion H; clear H
         end.

Lemma msb_neg f : f < 0 <-> msb f = (-1)%Z.
Proof. unfold msb; split; destruct_ifs; cbn in *; reflexivity || lra || lia. Qed.

Lemma msb_dec a : { msb a = 1 /\ 0 <= a } + { msb a = (-1)%Z /\ a < 0 }.
Proof. unfold msb; destruct_ifs; auto. Qed.

Instance : RelDecision Qlt. do 2 red; intros.  destruct (Qlt_le_dec x y) as [l|r].
left. assumption. right. lra. Qed.
Instance : RelDecision Qle. do 2 red; intros.  destruct (Qlt_le_dec y x) as [l|r].
right. lra. left. assumption. Qed.

Definition aux M N := forall f g,
    f ≢ 0 \/ g > 0 ->
    let '(ai, bi, ci, di) := N in
    let '(asi, bsi, csi, dsi) := (M * N)%RI in
    let '(gi, fi) := N ⋅ (g, f) in
    let '(gsi, fsi) := (M * N) ⋅ (g, f) in
    if (decide (((0 <= f /\ 0 <= fi) \/ (f < 0 /\ fi < 0)) <-> (0 <= ci))) then
      ((0 <= fi /\ 0 <= fsi) \/ (fi < 0 /\ fsi < 0)) ->
      ((0 <= ci /\ 0 <= csi) \/ (ci < 0 /\ csi < 0))
    else
      ((0 <= ci /\ 0 <= csi) \/ (ci < 0 /\ csi < 0)) ->
      ((0 <= fi /\ 0 <= fsi) \/ (fi < 0 /\ fsi < 0)).
(* Definition aux M N := forall f g, *)
(*     f ≢ 0 \/ g > 0 -> *)
(*     let '(ai, bi, ci, di) := N in *)
(*     let '(asi, bsi, csi, dsi) := (M * N)%RI in *)
(*     let '(fi, gi) := N ⋅ (f, g) in *)
(*     let '(fsi, gsi) := (M * N) ⋅ (f, g) in *)
(*     if (decide (((0 <= f /\ 0 <= fi) \/ (f < 0 /\ fi < 0)) <-> (0 <= bi))) then *)
(*       ((0 <= fi * fsi)) -> *)
(*       ((0 <= bi /\ 0 <= bsi) \/ (bi < 0 /\ bsi < 0)) *)
(*     else *)
(*       ((0 <= bi /\ 0 <= bsi) \/ (bi < 0 /\ bsi < 0)) -> *)
(*       ((0 <= fi /\ 0 <= fsi) \/ (fi < 0 /\ fsi < 0)). *)

Lemma sgn_lem N f g :
  0 < det N -> (0 <= det [g, 1; f, 0] /\ 0 <= (det (N * [g, 1; f, 0]))) \/ (det [g, 1; f, 0] < 0 /\ (det (N * [g, 1; f, 0])) < 0) .
Proof.
  intros.
  destruct N as [[[ai bi] ci] di].
  unfold det in H.
  rewrite det_mul.
  cbn in *.
  destruct (decide (f ≡ 0)).
  - cbn. rewrite e. cbn. nra.
  - nra.
Qed.

Lemma ratchet_lemma1 M N a b c d :
  M ≡ (a, b, c, d) ->
  0 < det N ->
  ratchet M -> c ≡ 0 -> aux M N.
Proof.
  unfold aux.
  destruct M as [[[a b] c] d]. intros.
  pose proof sgn_lem N f g H.
  destruct N as [[[ai bi] ci] di].
  unfold ratchet, det in *. cbn in *.
  rewrite H1 in *.
  cbn in *.
  assert (0 < a * d) by nra. split_pairs.
  assert (0 < d). destruct (decide (d == 0)).
  rewrite q in *. nra. nra.
  assert (0 < a) by nra.
  destruct_ifs; try nra. Qed.

Lemma ratchet_lemma2 N :
  0 < det N -> aux (0, -1, 1, 0) N.
Proof.
  unfold aux. intros.
  pose proof sgn_lem N f g H.
  destruct N as [[[ai bi] ci] di]; intros.
  unfold det in *. cbn in *.
  destruct (decide (f == 0)).
  assert (0 < g) by tauto.
  rewrite q in *.
  destruct_ifs. nra. nra.
  destruct_ifs. nra. nra. Qed.

Lemma ratchet_lemma3 M N :
  0 < det N -> ratchet M -> aux M N.
Proof.
  intros.
  destruct M as [[[a b] c] d].
  destruct (decide (c ≡ 0)).
  apply ratchet_lemma1.
  assert (M ≡ (1,a,0,c))


Definition ratchet M :=
  (0 < det M) /\
  let '(m11, m12, m21, m22) := M in
  (0 <= m11) /\ (0 <= m12).

Definition msb f :=
  if (Qlt_le_dec f 0) then (-1)%Z else 1.
Instance : Proper (Qeq ==> eq) msb.
Proof. do 2 red; intros. unfold msb.
       destruct_ifs; (reflexivity || nra). Qed.

Lemma msb_mul a f :
  a ≢ 0 -> f ≢ 0 -> msb (a * f) = msb a * msb f.
Proof.
  intros; unfold msb; cbn in *; destruct_ifs; nra || reflexivity.
Qed.

Lemma msb0 : msb 0 = 1.
Proof. reflexivity. Qed.

Lemma msb_pos f :
  0 <= f <-> msb f = 1.
Proof. unfold msb; split; destruct_ifs; cbn in *; reflexivity || lra || lia. Qed.

Ltac invert_mat :=
  repeat match goal with
         | M : prod _ _ |- _ => destruct M
         | H : (@equiv _ (@prod_equiv _ _ _ _)) _ _ |- _  => inversion H; clear H
         end.

Lemma msb_neg f : f < 0 <-> msb f = (-1)%Z.
Proof. unfold msb; split; destruct_ifs; cbn in *; reflexivity || lra || lia. Qed.

Lemma msb_dec a : { msb a = 1 /\ 0 <= a } + { msb a = (-1)%Z /\ a < 0 }.
Proof. unfold msb; destruct_ifs; auto. Qed.

Instance : RelDecision Qlt. do 2 red; intros.  destruct (Qlt_le_dec x y) as [l|r].
left. assumption. right. lra. Qed.
Instance : RelDecision Qle. do 2 red; intros.  destruct (Qlt_le_dec y x) as [l|r].
right. lra. left. assumption. Qed.

Definition aux M N := forall f g,
    f ≢ 0 \/ g > 0 ->
    let '(ai, bi, ci, di) := N in
    let '(asi, bsi, csi, dsi) := (M * N)%RI in
    let '(fi, gi) := N ⋅ (f, g) in
    let '(fsi, gsi) := (M * N) ⋅ (f, g) in
    if (decide (((0 <= f /\ 0 <= fi) \/ (f < 0 /\ fi < 0)) <-> (0 <= bi))) then
      ((0 <= fi /\ 0 <= fsi) \/ (fi < 0 /\ fsi < 0)) ->
      ((0 <= bi /\ 0 <= bsi) \/ (bi < 0 /\ bsi < 0))
    else
      ((0 <= bi /\ 0 <= bsi) \/ (bi < 0 /\ bsi < 0)) ->
      ((0 <= fi /\ 0 <= fsi) \/ (fi < 0 /\ fsi < 0)).
(* Definition aux M N := forall f g, *)
(*     f ≢ 0 \/ g > 0 -> *)
(*     let '(ai, bi, ci, di) := N in *)
(*     let '(asi, bsi, csi, dsi) := (M * N)%RI in *)
(*     let '(fi, gi) := N ⋅ (f, g) in *)
(*     let '(fsi, gsi) := (M * N) ⋅ (f, g) in *)
(*     if (decide (((0 <= f /\ 0 <= fi) \/ (f < 0 /\ fi < 0)) <-> (0 <= bi))) then *)
(*       ((0 <= fi * fsi)) -> *)
(*       ((0 <= bi /\ 0 <= bsi) \/ (bi < 0 /\ bsi < 0)) *)
(*     else *)
(*       ((0 <= bi /\ 0 <= bsi) \/ (bi < 0 /\ bsi < 0)) -> *)
(*       ((0 <= fi /\ 0 <= fsi) \/ (fi < 0 /\ fsi < 0)). *)

Lemma sgn_lem N f g :
  0 < det N -> (0 <= det [f, 0; g, 1] /\ 0 <= (det (N * [f, 0; g, 1]))) \/ (det [f, 0; g, 1] < 0 /\ (det (N * [f, 0; g, 1])) < 0) .
Proof.
  intros.
  destruct N as [[[ai bi] ci] di].
  unfold det in H.
  rewrite det_mul.
  cbn in *.
  destruct (decide (f ≡ 0)).
  - cbn. rewrite e. cbn. nra.
  - nra.
Qed.

Lemma ratchet_lemma1 M N :
  let '(a, b, c, d) := M in
  0 < det N ->
  ratchet M -> b ≡ 0 -> aux M N.
Proof.
  unfold aux.
  destruct M as [[[a b] c] d]. intros.
  pose proof sgn_lem N f g H.
  destruct N as [[[ai bi] ci] di].
  unfold ratchet, det in *. cbn in *.
  assert (0 < a * d /\ 0 < d) by nra.
  assert (0 < a) by nra.
  destruct_ifs; nra. Qed.

Lemma ratchet_lemma2 N :
  0 < det N -> aux (0, -1, 1, 0) N.
Proof.
  unfold aux. intros.
  pose proof sgn_lem N f g H.
  destruct N as [[[ai bi] ci] di]; intros.
  unfold det in *. cbn in *.
  destruct H0.
  destruct H1.
  destruct_ifs. clear H2. intros.
  rewrite !Qmult_0_l, !Qmult_0_r, !Qmult_1_r, !Qplus_0_l, !Qplus_0_r in *.
  set (fi := (ai * f + bi * g)%Q) in *. split_pairs.

  destruct H2. left.
  assert (0 <= bi) by (apply i; nra).
  split. assumption. split_pairs.
  destruct (decide (0 <= - di)). nra. nra
  nra.



  destruct H2. admit.
  assert (0 <= f /\ 0 <= fi). split; nra.

  assert (fi * di <= 0).
  destruct H2. nra.

  destruct H2.
  destruct H1. right. nra. left. nra.
  assert
  destruct H2.

  destruct H4. left. assert (0 <= bi) by nra. split. nra. apply H3 in H5.
  destruct H5.
  nra.
  left. destruct H1. cbn in *. split_pairs. split. apply q0. nra.

split_pairs.   repeat match goal with
           | H : not (_ /\ _) |- _ => rewrite not_and_l in H
           | H : not (_ \/ _) |- _ => rewrite not_or_l in H; split_pairs
           | H : not (_ -> _) |- _ => rewrite not_imp_l in H; split_pairs
           | H : not (_ <-> _) |- _ => rewrite not_iff in H; split_pairs
           | H : _ \/ _ |- _ => destruct H; intros; split_pairs; try nra
           end. rewrite H1 in *. cbn in *.
  d
  assert (0 < a * d /\ 0 < d) by nra.
  assert (0 < a) by nra.
  unfold aux. intros.
  pose proof sgn_lem N f g H.
  pose proof sgn_lem2 N f g H.
  destruct N as [[[ai bi] ci] di].
  specialize (H0 f g H1).
  cbn in *.
  rewrite !Qmult_0_l, !Qmult_0_r, !Qmult_1_r, !Qplus_0_l, !Qplus_0_r in *.
  destruct (decide (f ≡ 0)).
  rewrite e in *.
  setoid_rewrite Qmult_0_r in H0. setoid_rewrite Qplus_0_l in H0.
  setoid_rewrite Qmult_0_r. setoid_rewrite Qplus_0_l.
  assert (0 < g) by intuition.
  split.
  - intros. apply msb_pos. nra.
  - intros. apply msb_pos in H5. nra.
  - destruct (msb_dec f); split_pairs; rewrite H4 in *.
    + split.
      * intros.
        assert (0 < f). cbn in *. nra.
        symmetry in H2.
        apply msb_pos.
        apply msb_pos in H2. cbn in *.
        specialize (H3 H7).
        destruct (msb_dec (ai * f + bi * g)); split_pairs.
        specialize ((proj2 H0) H8); intros. nra.

        apply ZifyClasses.not_morph in H0.
        assert (msb (ai * f + bi * g) <> 1). cbn. lia.
        apply H0 in H10. cbn in *.  assert (bi < 0) by lra.


  repeat match goal with
           | H : not (_ /\ _) |- _ => rewrite not_and_l in H
           | H : not (_ \/ _) |- _ => rewrite not_or_l in H; split_pairs
           | H : not (_ -> _) |- _ => rewrite not_imp_l in H; split_pairs
           | H : not (_ <-> _) |- _ => rewrite not_iff in H; split_pairs
           | H : _ \/ _ |- _ => destruct H; intros; split_pairs; try nra
           end. rewrite H1 in *. cbn in *.
Definition aux N M := forall f g,
    f ≢ 0 \/ g > 0 ->
    let '(ai, bi, ci, di) := N in
    let '(asi, bsi, csi, dsi) := (M * N)%RI in
    let '(fi, gi) := M ⋅ (f, g) in
    let '(fsi, gsi) := (M * N) ⋅ (f, g) in
    if (decide (msb f = msb fi <-> (msb bi = 1))) then
      msb fi = msb fsi -> msb bi = msb bsi
    else
      msb bi = msb bsi -> msb fi = msb fsi.

Lemma ratchet_lemma1 M N :
  let '(a, b, c, d) := M in
  ratchet M -> b ≡ 0 -> aux N M.
Proof.
  unfold aux.
  destruct N as [[[ai bi] ci] di].
  destruct M as [[[a b] c] d]. intros.
  unfold ratchet, det in H. cbn in H. cbn in H0.
  assert (0 < a * d /\ 0 < d) by nra.
  assert (0 < a) by nra.
  cbn.
  destruct_ifs.
  -  rewrite H0 in *.
     rewrite !Qmult_0_l, !Qplus_0_r in *.
     intros.
     destruct (msb_dec (a * bi)); split_pairs.
     rewrite H6.
     apply i.
  split.
  * intros.
    assert (0 <= bi). nra.
    apply (H1 f g) in H6. cbn in H6.
    set (fi := (ai * f + bi * g)%Q) in *.
    setoid_replace (a * ai * f + a * bi * g)%Q with (a * fi)%Q; [|(cbn; unfold fi; ring)].
    destruct (Qeq_dec fi 0). rewrite q in *. rewrite Qmult_0_r.
    assumption.
    rewrite msb_mul. rewrite (proj1 (msb_pos a)) by nra. cbn. lia. cbn. nra. assumption. assumption.
  * intros.
    set (fi := (ai * f + bi * g)%Q) in *.
    assert (msb fi = msb f).
    {
    setoid_replace (a * ai * f + a * bi * g)%Q with (a * fi)%Q in H5 by (cbn; unfold fi; ring).
    destruct (Qeq_dec fi 0). rewrite q in *. rewrite Qmult_0_r in *. assumption.
    rewrite msb_mul in *. rewrite (proj1 (msb_pos a)) in * by nra. cbn in *. lia. cbn in *. lra. assumption. }
    apply (H1 f g) in H6. nra.  assumption.
Qed.

Lemma sgn_lem N f g :
  0 < det N -> msb (det [f, 0; g, 1]) = msb (det (N * [f, 0; g, 1])).
Proof.
  intros.
  rewrite det_mul.
  destruct (decide (f ≡ 0)).
  - cbn. rewrite e.
    f_equiv. cbn. lra.
  -  rewrite msb_mul.
     assert (0 <= det N). nra.
     rewrite (proj1 (msb_pos _) H0). rewrite Z.mul_1_l. reflexivity.
     cbn in *. nra. cbn in *. nra.
Qed.

Lemma sgn_lem2 N f g :
  0 < det N -> 0 < (det [f, 0; g, 1]) -> 0 < (det (N * [f, 0; g, 1])).
Proof.
  intros.
  rewrite det_mul.
  destruct (decide (f ≡ 0)).
  - cbn in *. nra.
  - cbn in *. nra.
Qed.

Lemma ratchet_lemma2 N :
  0 < det N -> aux N -> aux ((0, -1, 1, 0) * N).
Proof.
  unfold aux. intros.
  pose proof sgn_lem N f g H.
  pose proof sgn_lem2 N f g H.
  destruct N as [[[ai bi] ci] di].
  specialize (H0 f g H1).
  cbn in *.
  rewrite !Qmult_0_l, !Qmult_0_r, !Qmult_1_r, !Qplus_0_l, !Qplus_0_r in *.
  destruct (decide (f ≡ 0)).
  rewrite e in *.
  setoid_rewrite Qmult_0_r in H0. setoid_rewrite Qplus_0_l in H0.
  setoid_rewrite Qmult_0_r. setoid_rewrite Qplus_0_l.
  assert (0 < g) by intuition.
  split.
  - intros. apply msb_pos. nra.
  - intros. apply msb_pos in H5. nra.
  - destruct (msb_dec f); split_pairs; rewrite H4 in *.
    + split.
      * intros.
        assert (0 < f). cbn in *. nra.
        symmetry in H2.
        apply msb_pos.
        apply msb_pos in H2. cbn in *.
        specialize (H3 H7).
        destruct (msb_dec (ai * f + bi * g)); split_pairs.
        specialize ((proj2 H0) H8); intros. nra.

        apply ZifyClasses.not_morph in H0.
        assert (msb (ai * f + bi * g) <> 1). cbn. lia.
        apply H0 in H10. cbn in *.  assert (bi < 0) by lra.
        destruct (msb_dec (-ci*f - di*g)); split_pairs. nra.
        destruct (Qeq_dec di 0). rewrite q in *.
        destruct (msb_dec ci); split_pairs.
        destruct (msb_dec di); split_pairs. cbn in *.
        ring_simplify in *
        psatz Q. nra. assert (f < 0) by lra. nra.
        psatz Q.
        destruct (Qlt_le_dec bi 0). nra.
        assert (not (0 <= bi)). lra.
        Search iff.
        apply ZifyClasses.not_morph in H0.
        apply H0 in H4.





    assert ((msb (bi * g)) = msb 0). apply msb_pos. nra. apply H0 in H4. nra.
    specialize ((proj1 H0) q); intros. apply msb_neg in H4.
    assert (bi == 0). nra. setoid_rewrite H6 in H.
    apply msb_neg.
    apply msb_pos in q.
    unfold msb in H0. revert H0. destruct_ifs; intros; cbn in *. nra.
    assert (bi < 0). nra.
    destruct (decide (msb (bi * g) = msb 0)).
    apply H0 in e0. nra. assert (msb (bi * g) = (-1)%Z).
    exfalso. apply n. apply H0. nra.
    apply H0 in n.
    assert
    apply H0.
    intros. rewrite Qmult_0_r, Qplus_0_l.
    symmetry in H2.
    apply msb_neg in H2.
    cbn in *. ring_simplify in H2.
    assert (bi < 0) by nra.
    apply

    apply msb_neg. nra.
  split.
  - intros.

    apply H Qsgn..
  assert (0 < a * d /\ 0 < d) by nra.
  assert (0 < a) by nra.
  cbn.
  rewrite H0 in *.
  rewrite !Qmult_0_l, !Qplus_0_r.
  split.
  * intros.
    assert (0 <= bi). nra.
    apply (H1 f g) in H6. cbn in H6.
    set (fi := (ai * f + bi * g)%Q) in *.
    setoid_replace (a * ai * f + a * bi * g)%Q with (a * fi)%Q; [|(cbn; unfold fi; ring)].
    destruct (Qeq_dec fi 0). rewrite q in *. rewrite Qmult_0_r.
    assumption.
    rewrite msb_mul. rewrite msb_pos by nra. cbn. lia. cbn. nra. assumption. assumption.
  * intros.
    set (fi := (ai * f + bi * g)%Q) in *.
    assert (msb fi = msb f).
    {
    setoid_replace (a * ai * f + a * bi * g)%Q with (a * fi)%Q in H5 by (cbn; unfold fi; ring).
    destruct (Qeq_dec fi 0). rewrite q in *. rewrite Qmult_0_r in *. assumption.
    rewrite msb_mul in *. rewrite msb_pos in * by nra. cbn in *. lia. cbn in *. lra. assumption. }
    apply (H1 f g) in H6. nra.  assumption.
Qed.


(* Lemma ratchet_lemma1 M N f g : *)
(*   ratchet M -> *)
(*   let '(a, b, c, d) := M in *)
(*   b ≡ 0 -> *)
(*   let '(ai, bi, ci, di) := N in *)
(*   let '(asi, bsi, csi, dsi) := (M * N)%RI in *)
(*   let '(fi, gi) := N ⋅ (f, g) in *)
(*   let '(fsi, gsi) := (M * N) ⋅ (f, g) in *)
(*   (0 <= bi <-> msb fi = msb f) -> (0 <= bsi <-> msb fsi = msb f). *)
(* Proof. *)
(*   destruct N as [[[ai bi] ci] di]. *)
(*   destruct M as [[[a b] c] d]. intros. *)
(*   unfold ratchet, det in H. cbn in H. cbn in H0. *)
(*   assert (0 < a * d /\ 0 < d) by nra. *)
(*   assert (0 < a) by nra. *)
(*   cbn. *)
(*   intros. rewrite H0 in *. *)
(*   rewrite !Qmult_0_l, !Qplus_0_r. *)
(*   split. *)
(*   * intros. *)
(*     assert (0 <= bi). nra. *)
(*     apply H3 in H5. *)
(*     set (fi := (ai * f + bi * g)%Q) in *. *)
(*     setoid_replace (a * ai * f + a * bi * g)%Q with (a * fi)%Q; [|(cbn; unfold fi; ring)].  *)
(*     destruct (Qeq_dec fi 0). rewrite q in *. rewrite Qmult_0_r. *)
(*     assumption. *)
(*     rewrite msb_mul. rewrite msb_pos by nra. cbn. lia. cbn. nra. assumption. *)
(*   * intros. *)
(*     set (fi := (ai * f + bi * g)%Q) in *. *)
(*     assert (msb fi = msb f). *)
(*     { *)
(*     setoid_replace (a * ai * f + a * bi * g)%Q with (a * fi)%Q in H4 by (cbn; unfold fi; ring). *)
(*     destruct (Qeq_dec fi 0). rewrite q in *. rewrite Qmult_0_r in *. assumption. *)
(*     rewrite msb_mul in *. rewrite msb_pos in * by nra. cbn in *. lia. cbn in *. lra. assumption. } *)
(*     apply H3 in H5. nra. *)
(* Qed. *)

Context
  {M : nat -> mat Q}
  `{forall i, ratchet (M i)}.
Notation T i := (big_mul_rev M 0%nat i).

Lemma T_pos_det i :
  0 < det (T i).
Proof.
  induction i.
  + reflexivity.
  + rewrite (big_op_rev_S_l [*] 1) by lia. rewrite det_mul.
    specialize (H i).
    unfold ratchet in H.
    destruct H. cbn in *. nra.
Qed.

Lemma sgn_lem i f g :
  f ≢ 0 -> msb (det [f, 0; g, 1]) = msb (det ((T i) * [f, 0; g, 1])).
Proof.
  intros.
  pose proof T_pos_det i.
  rewrite det_mul.
  rewrite msb_mul.
  rewrite (msb_pos _ H1). rewrite Z.mul_1_l. reflexivity.
  cbn in *. nra. cbn in *. nra.
Qed.



Theorem ratched_spec f g :
  f ≢ 0 \/ g > 0 ->
  let '(a0, b0, c0, d0) := T 0%nat in
  forall i,
    let '(ai, bi, ci, di) := T i in
    let '(fi, gi) := (T i) ⋅ (f, g) in
    (0 <= bi) <-> (msb fi = msb f).
Proof.
  intros.
  destruct (T 0%nat) as [[[a0 b0] c0] d0] eqn:E. intros.
  induction i.
  - simpl.
    rewrite Qmult_0_l, Qmult_1_l, Qplus_0_r. intuition.
  -
    (* epose proof ratchet_lemma1 (M i) (T i) f g ltac:(apply H). *)

    destruct (M i) as [[[a b] c] d] eqn:E4.
    destruct (T i) as [[[ai bi] ci] di] eqn:E2.
    destruct (T (S i)) as [[[asi bsi] csi] dsi] eqn:E3.
    cbn.
    assert (forall asi' bsi' csi' dsi', (asi', bsi', csi', dsi') ≡ T (S i) -> (0 <= bsi' ↔ msb (asi' * f + bsi' * g) = msb f) -> (0 <= bsi ↔ msb (asi * f + bsi * g) = msb f)).
    { intros.
      rewrite E3 in H1.
      invert_mat. cbn -[equiv big_op_rev id2] in H3, H4, H6, H5.
      setoid_rewrite H3 in H2. setoid_rewrite H6 in H2. assumption. }
    eapply H1.
    destruct (decide (b ≡ 0)).
    + epose proof ratchet_lemma1 (M i) (T i) f g ltac:(apply H).
      rewrite E2, E4 in H1.
      specialize (H1 e).
      rewrite <- E2, <- E4 in H1.
      destruct (M i * T i) as [[[asi' bsi'] csi'] dsi'].


  pose proof (sgn_lem i f g).
  pose proof (sgn_lem (S i) f g).
  set (fi := ai * f + bi * g).
  set (gi := ci * f + di * g).
  destruct (T (S i)) as [[[asi bsi] csi] dsi] eqn:E3.
  set (fsi := asi * f + bsi * g).
  set (gsi := csi * f + dsi * g).
  assert (((ai, bi, ci, di) * (f, 0, g, 1)) ≡ [fi, bi; gi, di]).
  { unfold fi, gi; auto_mat. }
  assert (((asi, bsi, csi, dsi) * (f, 0, g, 1)) ≡ [fsi, bsi; gsi, dsi]).
  { unfold fsi, gsi; auto_mat. }
  (* assert (a, b, c, d) * (ai, bi, ci ,di) ≡ T (S i). *)
  (* rewrite <- E2 in H1. *)
  rewrite H3 in H1.
  rewrite H4 in H2.
  cbn in IHi.
  cbn -[equiv big_op_rev id2] in *.
  invert_mat.
  cbn -[equiv big_op_rev id2] in *.
  rewrite !Qmult_0_l, !Qmult_0_r, !Qplus_0_l, !Qplus_0_r, !Qmult_1_r in *.
  replace (ai * f + bi * g)%Q with fi in * by reflexivity.
  (* rewrite H3 in H1. *)
  (* rewrite H4 in H2. *)

  assert (E2' : T i ≡ (ai, bi, ci, di)). rewrite <- E2. reflexivity.  assert (E3' : T (S i) ≡ (asi, bsi, csi, dsi)). rewrite <- E3. reflexivity.

  rewrite (big_op_rev_S_l [*] 1) in E3' by lia.
  destruct (Qeq_dec b 0).
  rewrite q in E4.

  rewrite E2' in E3'.

  invert_mat.
  cbn -[equiv big_op_rev id2] in *.
  +
    Set Printing All.
    rewrite E2 in H17.

    (T (S i)).
  assert (0 < a * d /\ 0 < d /\ 0 < a).
  { specialize (H i). unfold ratchet in *. rewrite E4 in H.
    simpl in H.
    split. nra.
    split. nra.
    assert (0 < d) by nra. nra. }
  rewrite q in H3, H15.
  rewrite !Qmult_0_l, !Qplus_0_r in H3, H15.
  destruct H17 as [lt_ad [lt_d lt_a]].
  cbn in H15, H3. cbn. setoid_rewrite <- H3. setoid_rewrite <- H15.
  split.
  * intros.
    assert (0 <= bi). clear -H15 H17 lt_ad lt_a lt_d. cbn in *. nra.
    apply IHi in H20.
    setoid_replace (a * ai * f + a * bi * g)%Q with (a * fi)%Q.
    destruct (Qeq_dec fi 0). rewrite q0 in *. rewrite Qmult_0_r. assumption.
    rewrite msb_mul. rewrite msb_pos by nra. cbn. lia. cbn.  nra. assumption.
    cbn. unfold fi. nra.
  * intros.
    assert (msb (ai * f + bi * g) = msb f).
    { clear -lt_a H17 fi.
    fold fi.
    setoid_replace (a * ai * f + a * bi * g)%Q with (a * fi)%Q in H17.
    destruct (Qeq_dec fi 0). rewrite q in *. rewrite Qmult_0_r in *. assumption.
    rewrite msb_mul in *. rewrite msb_pos in * by nra. cbn in *. lia. cbn in *. nra. assumption.
    cbn. unfold fi. lra. }
    fold fi in H20.
    apply IHi in H20. clear -H20 lt_a. nra.
  +
    destruct (Z.eq_dec f 0). subst. Search Z.sgn. simpl.
    Admitted.


Local Open Scope Z.
Local Open Scope mat_scope.
Local Open Scope ring_scope.
Local Open Scope grp_scope.
Local Open Scope lmod_scope.

Definition ratchet M :=
  (0 < det M) /\
  let '(m11, m12, m21, m22) := M in
  (0 <= m11) /\ (0 <= m12).

Section __.

Definition msb f :=
  if (Z_le_dec 0 f) then 1 else -1.

Lemma msb_sgn f :
  f <> 0 -> Z.sgn f = msb f.
Proof.
  intros.
  unfold msb.
  destruct_ifs. cbn in *. lia.
  lia. Qed.

Lemma msb_mul a f :
  a <> 0 -> f <> 0 -> msb (a * f) = msb a * msb f.
Proof.
  intros; unfold msb; destruct_ifs; cbn in *; try lia.
Qed.

Lemma msb_pos f :
  0 < f -> msb f = 1.
Proof. unfold msb; destruct_ifs; lia. Qed.

Lemma ratchet_lemma1 a c d N f g :
  let M := (a, 0, c, d) in
  ratchet M -> f <> 0 -> 0 < g ->
  let v := (f, g) in
  let T := M * N in
  let '(ai, bi, ci, di) := N in
  let '(asi, bsi, csi, dsi) := T in
  let '(fi, gi) := N ⋅ v in
  let '(fsi, gsi) := (M * N) ⋅ v in
  (0 <= bi <-> msb fi = msb f) -> (0 <= bsi <-> msb fsi = msb f).
Proof.
  intros.
  unfold ratchet, M, det in H. cbn in *.
  assert (0 < a * d /\ 0 < d) by lia.
  assert (0 < a) by lia.
  destruct N as [[[ai bi] ci] di].
  unfold T. simpl.
  intros.
  rewrite !Z.mul_0_l, !Z.add_0_r in *.
  split.
  * intros.
    assert (0 <= bi). lia.
    apply H4 in H6.
    set (fi := (ai * f + bi * g)%Z) in *.
    replace (a * ai * f + a * bi * g)%Z with (a * fi)%Z by lia.
    destruct (Z.eq_dec fi 0). rewrite e in *. rewrite Z.mul_0_r.
    assumption.
    rewrite msb_mul. rewrite msb_pos by lia. cbn. lia. cbn. lia. assumption.
  * intros.
    set (fi := (ai * f + bi * g)%Z) in *.
    assert (msb fi = msb f).
    {
    replace (a * ai * f + a * bi * g)%Z with (a * fi)%Z in * by lia.
    destruct (Z.eq_dec fi 0). rewrite e in *. rewrite Z.mul_0_r in *. assumption.
    rewrite msb_mul in *. rewrite msb_pos in * by lia. cbn in *. lia. cbn in *. lia. assumption. }
    apply H4 in H6. nia.
Qed.

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


Lemma ratchet_lemma1 a c d N f g :
  let M := (a, 0, c, d) in
  ratchet M -> f <> 0 -> 0 < g ->
  let v := (f, g) in
  let T := M * N in
  let '(ai, bi, ci, di) := N in
  let '(asi, bsi, csi, dsi) := T in
  let '(fi, gi) := N ⋅ v in
  let '(fsi, gsi) := (M * N) ⋅ v in
  (0 <= bi <-> msb fi = msb f) -> (0 <= bsi <-> msb fsi = msb f).
  rewrite T.

  { repeat split.
    { lia. }
    { lia. }
    { nia. }
  }
  unfold M in H.

  P
Admitted.
(* Lemma ratchet_lemma (M N : mat) v : *)
(*   let T := M * N in *)
(*   let '(a, b, c, d) := M in *)
(*   let '(ai, bi, ci, di) := N in *)
(*   let '(asi, bsi, csi, dsi) := T in *)
(*   let '(f, g) := v in *)
(*   let '(fi, gi) := N ⋅ v in *)
(*   let '(fsi, gsi) := (M * N) ⋅ v in *)
(*   (0 <= bi <-> msb fi = msb f) -> (0 <= bsi <-> msb fsi = msb f). *)
(* Proof. *)
(*   destruct M as [[[a b] c] d]. *)
(*   destruct N as [[[ai bi] ci] di]. *)
(*   simpl. *)
(*   split_pairs. *)

  Context
    {M : nat -> mat}
    `{forall i, ratchet (M i)}.

Notation big_mmult_rev := (fun n m f => @big_op_rev _ mmult I f n m).

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
