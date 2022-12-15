Require Import ZArith micromega.Lia micromega.Lqa ZArith.Zhints QArith Field Psatz.
From stdpp Require Import decidable.

From BY Require Import Matrix Impl Tactics Q.
From BY.Hierarchy Require Import Definitions BigOp.

From stdpp Require Import numbers.

(* TODO: Move *)
Global Instance Z_eq_dec: RelDecision Nat.eq := Nat.eq_dec.
Global Instance Q_lt_dec : RelDecision Qlt.
Proof. do 2 red; intros; destruct (Qlt_le_dec x y); [left | right]; lra. Qed.
Global Instance Q_le_dec : RelDecision Qle.
Proof. do 2 red; intros; destruct (Qlt_le_dec y x); [right | left]; lra. Qed.

Lemma mod3dec a : {a mod 3 = 0} + {a mod 3 = 1} + {a mod 3 = 2}.
Proof.
  destruct (decide (a mod 3 = 0));
  destruct (decide (a mod 3 = 1));
    destruct (decide (a mod 3 = 2)); auto.
  pose proof Nat.mod_bound_pos a 3 ltac:(lia) ltac:(lia). lia.
Qed.

Section __.

  Local Open Scope Q_scope.
  Local Open Scope mat_scope.
  Local Open Scope ring_scope.
  Local Open Scope lmod_scope.

  Definition ratchet M :=
    (0 < det M) /\
      (0 <= M.1.1.1) /\ (0 <= M.1.1.2).
  Instance : Proper ((≡) ==> iff) ratchet.
  Proof.
    do 2 red. intros. unfold ratchet.
    invert_mat. cbn in *. rewrite H1, H2, H0, H3. auto.
  Qed.

  Definition σ_r x y :=
    if decide (x < 0)
    then if decide (y < 0)
         then (-1)%Z
         else 1
    else 1.
  Global Instance : Proper ((≡) ==> (≡) ==> (=)) σ_r.
  Proof.
    do 3 red; intros.
    unfold σ_r.
    repeat (destruct (decide _)); try reflexivity; rewrite ?H, ?H0 in *; try lra.
  Qed.

  (* count sign changes *)
  Definition μ_r a b : Z :=
    if decide (a < 0)
    then if decide (0 <= b)
         then 1%Z
         else 0
    else if decide (b < 0)
         then 1
         else 0.
  Global Instance μ_r_Proper : Proper ((≡) ==> (≡) ==> (=)) μ_r.
  Proof.
    do 3 red; intros.
    unfold μ_r.
    repeat (destruct (decide _)); try reflexivity; rewrite ?H, ?H0 in *; try lra.
  Qed.

  Lemma σ_r_opp x :
    σ_r x (- x) = 1.
  Proof. unfold σ_r; repeat destruct (decide _); try lra; reflexivity. Qed.

  Lemma μ_r_opp x :
    x ≢ 0 -> μ_r x (- x) = 1.
  Proof. intros; unfold μ_r; repeat destruct (decide _); try nra; try reflexivity. simpl in *; lra. Qed.

  Lemma μ_r_id x :
    μ_r x x = 0.
  Proof. intros; unfold μ_r; repeat destruct (decide _); try nra; try reflexivity. Qed.

  Definition msb f :=
    if (Qlt_le_dec f 0) then (-1)%Z else 1.
  Instance : Proper (Qeq ==> eq) msb.
  Proof. do 2 red; intros. unfold msb. destruct_ifs; (reflexivity || nra). Qed.

  Lemma msb_mul a f :
    a ≢ 0 -> f ≢ 0 -> msb (a * f) = msb a * msb f.
  Proof. intros; unfold msb; cbn in *; destruct_ifs; nra || reflexivity. Qed.

  Lemma msb0 : msb 0 = 1.
  Proof. reflexivity. Qed.

  Lemma msb_pos f :
    0 <= f <-> msb f = 1.
  Proof. unfold msb; split; destruct_ifs; cbn in *; reflexivity || lra || lia. Qed.

  Lemma msb_neg f : f < 0 <-> msb f = (-1)%Z.
  Proof. unfold msb; split; destruct_ifs; cbn in *; reflexivity || lra || lia. Qed.

  Lemma msb_dec a : { msb a = 1 /\ 0 <= a } + { msb a = (-1)%Z /\ a < 0 }.
  Proof. unfold msb; destruct_ifs; auto. Qed.

  Context (f0 g0 : Q).

  Definition T (M : nat -> mat Q) i := (big_mul_rev M 0%nat i).
  Definition v M i := ((T M i) ⋅ (f0, g0)).
  Definition f M i := (v M i).1.
  Definition c M i := (T M i).1.1.2.
  Definition κ_r M i := (big_sum (fun j => μ_r (f M (S j)) (f M j)) 0%nat i).
  Definition κ_r' M i := (big_sum (fun j => μ_r (c M (S j)) (c M j)) 0%nat i).
  Definition k M i  := (big_mul (fun j => σ_r (f M (S j)) (- (f M j))) 0%nat i).
  Definition k' M i := (big_mul (fun j => σ_r (c M (S j)) (- (c M j))) 0%nat i).

  (* lower triangular *)
  Definition lt (N : mat Q) :=
    exists a c d, N ≡ (a, 0, c, d).
  Instance : Proper ((≡) ==> iff) lt.
  Proof.
    do 2 red; intros; unfold lt.
    split; intros; [setoid_rewrite <- H|setoid_rewrite H];
      destruct H0 as [? [? [?]]]; repeat eexists; auto_mat.
  Qed.

  Lemma ratchet_ut_vec :
    forall N x w,
      ratchet N -> lt N ->
      μ_r ((N ⋅ w).1) x = μ_r w.1 x.
  Proof.
    intros.
    destruct H0 as [a [b [d]]].
    destruct H as [det [cpos dpos]].
    destruct w as [w1 w2].
    rewrite H0 in *.
    simpl in *.
    unfold μ_r. repeat destruct (decide _); try nra; try reflexivity. 
    assert (d == 0). nra. nra.
    assert (d == 0). nra. nra.
  Qed.

  Lemma ratchet_ut_vec_2 :
    forall N w,
      ratchet N -> lt N ->
      μ_r ((N ⋅ w).1) w.1 = 0.
  Proof.
    intros; now rewrite ratchet_ut_vec, μ_r_id.
  Qed.

  Lemma ratchet_ut_mat :
    forall N x P,
      ratchet N -> lt N ->
      μ_r ((N * P).1.1.2) x = μ_r P.1.1.2 x.
  Proof.
    intros.
    destruct H0 as [a [b [d]]].
    destruct H as [det [cpos dpos]].
    destruct P as [[[p1 p2] p3] p4].
    rewrite H0 in *.
    simpl in *.
    unfold μ_r. repeat destruct (decide _); try nra; try reflexivity.
    assert (d == 0). nra. nra.
    assert (d == 0). nra. nra.
  Qed.

  Lemma ratchet_ut_mat_2 :
    forall N P,
      ratchet N -> lt N ->
      μ_r ((N * P).1.1.2) P.1.1.2 = 0.
  Proof.
    intros; now rewrite ratchet_ut_mat, μ_r_id.
  Qed.

  Lemma decomp N :
    forall a b c d,
      N ≡ (a, b, c, d) -> b ≢ 0 -> N ≡ (b, 0, d, 1) * (0, 1, -1, 0) * (a * d / b - c, 0, a / b, 1).
  Proof.
    intros. unfold Qinv_inv2.
    auto_mat; try nra.
    field_simplify. rewrite Qmult_comm. field_simplify; assumption. assumption.
  Qed.

  Definition t (M : nat -> mat Q) :=
    fun (i : nat) =>
      let '(a, b, c, d) := M (i / 3)%nat in
      if (decide (b ≡ 0))
      then match mod3dec i with
           | inright _ => I
           | inleft pf => match pf with
                         | right _ => I
                         | left _ => (a, b, c, d)
                         end
           end
      else match mod3dec i with
           | inright _ => (b, 0, d, 1)
           | inleft pf => match pf with
                         | right _ => (0, 1, -1, 0)
                         | left _ => (a * d / b - c, 0, a / b, 1)
                         end
           end.

  Lemma l1 i : (S (S (3 * i)) / 3 = i)%nat.
  Proof. symmetry. apply Nat.div_unique with (r:=2%nat); lia. Qed.

  Lemma l2 i : ((S (3 * i)) / 3 = i)%nat.
  Proof. symmetry. apply Nat.div_unique with (r:=1%nat); lia. Qed.

  Lemma l3 i : ((3 * i) / 3 = i)%nat.
  Proof. symmetry. apply Nat.div_unique with (r:=0%nat); lia. Qed.

  Lemma m1 i : S (S (3 * i)) mod 3 = 2%nat.
  Proof. symmetry. apply Nat.mod_unique with (q:=i%nat); lia. Qed.

  Lemma m11 i : exists p, mod3dec (S (S (3 * i))) = inright p.
  Proof. pose proof m1 i. destruct (mod3dec _) as [[]|]; try lia; eexists; reflexivity. Qed.

  Lemma m2 i : (S (3 * i)) mod 3 = 1%nat.
  Proof. symmetry. apply Nat.mod_unique with (q:=i%nat); lia. Qed.

  Lemma m22 i : exists p, mod3dec (S (3 * i)) = inleft (right p).
  Proof. pose proof m2 i. destruct (mod3dec _) as [[]|]; try lia; eexists; reflexivity. Qed.

  Lemma m3 i : (3 * i) mod 3 = 0%nat.
  Proof. symmetry. apply Nat.mod_unique with (q:=i%nat); lia. Qed.

  Lemma m33 i : exists p, mod3dec (3 * i) = inleft (left p).
  Proof. pose proof m3 i. destruct (mod3dec _) as [[]|]; try lia; eexists; reflexivity. Qed.

  Lemma t_lt M i :
    lt (t M (3 * i)).
  Proof.
    unfold t.
    rewrite l3. destruct m33 with (i:=i). rewrite H.
    destruct (M i) as [[[a b] c] d].
    destruct (decide _); [rewrite e|];
      repeat eexists.
  Qed.

  Lemma tSS_lt M i :
    lt (t M (S (S (3 * i)))).
  Proof.
    unfold t.
    rewrite l1. destruct m11 with (i:=i). rewrite H.
    destruct (M i) as [[[a b] c] d].
    destruct (decide _); repeat eexists.
  Qed.

  Lemma I_ratchet :
    ratchet I.
  Proof. split; simpl; lra. Qed.

  Lemma all_t_ratchet M :
    (forall i, ratchet (M i)) -> (forall i, ratchet (t M i)).
  Proof.
    intros.
    unfold t.
    specialize (H (i / 3)%nat).
    destruct (M (i / 3)%nat) as [[[a b] c] d].
    destruct H as [Mdet [cpos dpos]].
    destruct (decide _);
      destruct (mod3dec _); [destruct s| |destruct s|].
    - repeat split; assumption.
    - apply I_ratchet.
    - apply I_ratchet.
    - split.
      + simpl in *.
        apply Qmult_lt_r with (z:=b). lra.
        field_simplify. nra. assumption.
      + simpl in *. split.
        apply Qmult_le_r with (z:=b). lra. field_simplify. lra. lra. lra.
    - split; simpl in *; lra.
    - split; simpl in *; lra.
  Qed.

  Lemma t_ratchet M i :
    ratchet (M i) -> ratchet (t M (3 * i)).
  Proof.
    intros.  unfold t.
    rewrite l3. destruct m33 with (i:=i). rewrite H0.
    destruct (M i) as [[[a b] c] d].
    destruct (decide _); [assumption|].
    destruct H as [Mdet [cpos dpos]].
    split.
    - simpl in *.
      apply Qmult_lt_r with (z:=b). lra.
      field_simplify. nra. assumption.
    - simpl in *. split.
      apply Qmult_le_r with (z:=b). lra. field_simplify. lra. lra. lra.
  Qed.

  Lemma tSS_ratchet M i :
    ratchet (M i) -> ratchet (t M (S (S (3 * i)))).
  Proof.
    intros.  unfold t.
    rewrite l1. destruct m11 with (i:=i). rewrite H0.
    destruct (M i) as [[[a b] c] d].
    destruct H as [Mdet [cpos dpos]].
    destruct (decide _); split; simpl in *; lra.
  Qed.

  Lemma t_spec2 M i :
    t M (S (S (3 * i))) * (t M (S (3 * i)) * t M (3 * i)) ≡ M i.
  Proof.
    unfold t.
    rewrite l1, l2, l3.
    destruct m33 with (i:=i).
    destruct m22 with (i:=i).
    destruct m11 with (i:=i).
    rewrite H, H0, H1.
    destruct (M i) as [[[a b] c] d].
    destruct (decide _). rewrite !(left_id I [*]). reflexivity.
    rewrite !(assoc [*]).
    rewrite <- decomp. reflexivity. reflexivity. assumption.
  Qed.

  Lemma t_spec M i :
    T M i ≡ T (t M) (3 * i).
  Proof.
    induction i.
    - unfold T. rewrite !big_op_rev_nil by lia. reflexivity.
    - unfold T.
      replace (3 * S i)%nat with (S (S (S (3 * i)))) by lia.
      rewrite !big_op_rev_S_l by (exact _ || lia).
      fold (T M i).
      fold (T (t M) (3 * i)).
      rewrite <- IHi.
      rewrite <- t_spec2.
      rewrite !(assoc [*]). reflexivity.
  Qed.

  Lemma t_spec4 M i :
    f M i ≡ f (t M) (3 * i).
  Proof. unfold f, v. now rewrite t_spec. Qed.

  Lemma t_spec5 M i :
    c M i ≡ c (t M) (3 * i).
  Proof. unfold c. now rewrite t_spec. Qed.

  Lemma μ_r_lem_r (N P : mat Q) (w : vec Q) :
    (forall u, μ_r (P ⋅ u).1 u.1 = 0%Z) -> μ_r (P ⋅ w).1 w.1 + μ_r (N ⋅ (P ⋅ w)).1 (P ⋅ w).1 = μ_r (N ⋅ (P ⋅ w)).1 w.1.
  Proof.
    intros.
    specialize (H w).
    destruct N as [[[n11 n12] n21] n22].
    destruct P as [[[p11 p12] p21] p22].
    destruct w as [w1 w2].
    unfold μ_r in *.
    repeat destruct (decide _); cbn in *; try nra; try reflexivity; try lia.
  Qed.

  Lemma μ_r_lem_r2 (N P R : mat Q) :
    (forall R, μ_r (P * R).1.1.2 R.1.1.2 = 0%Z) -> μ_r (P * R).1.1.2 R.1.1.2 + μ_r (N * (P * R)).1.1.2 (P * R).1.1.2 = μ_r (N * (P * R)).1.1.2 R.1.1.2.
  Proof.
    intros.
    specialize (H R).
    destruct N as [[[n11 n12] n21] n22].
    destruct P as [[[p11 p12] p21] p22].
    destruct R as [[[r11 r12] r21] r22].
    unfold μ_r in *.
    repeat destruct (decide _); cbn in *; try nra; try reflexivity; try lia.
  Qed.

  Lemma μ_r_lem_l (N P : mat Q) (w : vec Q) :
    (forall u, μ_r (N ⋅ u).1 u.1 = 0%Z) -> μ_r (P ⋅ w).1 w.1 + μ_r (N ⋅ (P ⋅ w)).1 (P ⋅ w).1 = μ_r (N ⋅ (P ⋅ w)).1 w.1.
  Proof.
    intros.
    specialize (H (P ⋅ w)).
    destruct N as [[[n11 n12] n21] n22].
    destruct P as [[[p11 p12] p21] p22].
    destruct w as [w1 w2].
    unfold μ_r in *.
    repeat destruct (decide _); cbn in *; try nra; try reflexivity; try lia.
  Qed.

  Lemma μ_r_lem_l2 (N P R : mat Q) :
    (forall R, μ_r (N * R).1.1.2 R.1.1.2 = 0%Z) -> μ_r (P * R).1.1.2 R.1.1.2 + μ_r (N * (P * R)).1.1.2 (P * R).1.1.2 = μ_r (N * (P * R)).1.1.2 R.1.1.2.
  Proof.
    intros.
    specialize (H (P * R)).
    destruct N as [[[n11 n12] n21] n22].
    destruct P as [[[p11 p12] p21] p22].
    destruct R as [[[r11 r12] r21] r22].
    unfold μ_r in *.
    repeat destruct (decide _); cbn in *; try nra; try reflexivity; try lia.
  Qed.

  Lemma TS M i :
    T M (S i) ≡ M i * T M i.
  Proof. unfold T. rewrite big_op_rev_S_l; try exact _; [|lia]. reflexivity. Qed.

  Lemma aux3 N j x :
    μ_r (f N (S j)) x = μ_r (N j ⋅ (v N j)).1 x.
  Proof. unfold f, v. rewrite !TS. rewrite !(left_act_assoc (⋅) [*]). reflexivity. Qed.

  Lemma caux3 N j x :
    μ_r (c N (S j)) x = μ_r (N j * T N j).1.1.2 x.
  Proof. unfold c. rewrite !TS. reflexivity. Qed.

  Lemma vS N j :
    v N (S j) ≡ (N j) ⋅ v N j.
  Proof. unfold v. rewrite TS. rewrite !(left_act_assoc (⋅) [*]). reflexivity. Qed.

  Lemma aux4 N j :
    μ_r (N (S j) ⋅ (v N (S j))).1 (f N (S j)) = μ_r (N (S j) ⋅ (N j ⋅ (v N j))).1 (N j ⋅ v N j).1.
  Proof. unfold f, v. rewrite !TS. rewrite !(left_act_assoc (⋅) [*]). reflexivity. Qed.

  Lemma caux4 N j :
    μ_r (N (S j) * (T N (S j))).1.1.2 (c N (S j)) = μ_r (N (S j) * (N j * (T N j))).1.1.2 (N j * T N j).1.1.2.
  Proof. unfold c. rewrite !TS.  reflexivity. Qed.

  Lemma t_spec3 M i :
    (forall i, ratchet (M i)) ->
    κ_r M i = κ_r (t M) (3 * i).
  Proof.
    intros; induction i.
    - unfold κ_r. rewrite !big_op_nil by lia. reflexivity.
    - unfold κ_r.
      replace (3 * S i)%nat with (S (S (S (3 * i)))) by lia.
      rewrite !big_op_S_r by (exact _ || lia).
      fold (κ_r M i) (κ_r (t M) (3 * i)).
      rewrite <- IHi.
      rewrite <- !Z.add_assoc; f_equal.
      rewrite !Z.add_assoc.
      rewrite !aux3.
      rewrite !aux4.
      unfold f.
      rewrite μ_r_lem_r.
      2: { intros; apply ratchet_ut_vec_2. eapply t_ratchet; auto. apply t_lt. }
      rewrite vS.
      rewrite <- (left_act_assoc (⋅) [*]).
      rewrite μ_r_lem_l.
      2: { intros; apply ratchet_ut_vec_2. eapply tSS_ratchet; auto. apply tSS_lt. }
      apply μ_r_Proper.
      2: { unfold v. rewrite <- t_spec. reflexivity. }
      rewrite <- (left_act_assoc (⋅) [*]).
      rewrite t_spec2.
      unfold v. rewrite <- t_spec. reflexivity.
  Qed.

  Lemma t_spec6 M i :
    (forall i, ratchet (M i)) ->
    κ_r' M i = κ_r' (t M) (3 * i).
  Proof.
    intros; induction i.
    - unfold κ_r'. rewrite !big_op_nil by lia. reflexivity.
    - unfold κ_r'.
      replace (3 * S i)%nat with (S (S (S (3 * i)))) by lia.
      rewrite !big_op_S_r by (exact _ || lia).
      fold (κ_r' M i) (κ_r' (t M) (3 * i)).
      rewrite <- IHi.
      rewrite <- !Z.add_assoc; f_equal.
      rewrite !Z.add_assoc.
      rewrite !caux3.
      rewrite !caux4.
      unfold c.
      rewrite μ_r_lem_r2.
      2: { intros; apply ratchet_ut_mat_2. eapply t_ratchet; auto. apply t_lt. }
      rewrite TS.
      rewrite (assoc [*]).
      rewrite μ_r_lem_l2.
      2: { intros; apply ratchet_ut_mat_2. eapply tSS_ratchet; auto. apply tSS_lt. }
      apply μ_r_Proper.
      rewrite (assoc [*]).
      rewrite t_spec2.
      rewrite <- t_spec. reflexivity.
      rewrite <- t_spec. reflexivity.
  Qed.

  Definition ratchet_spec M i :=
    (κ_r M i = (κ_r' M i) + ((μ_r (f M i) (f M 0)) + (μ_r (c M i) (c M 0))) mod 2)%Z.

  Lemma transform_spec2 M i :
    (forall i, ratchet (M i)) -> ratchet_spec (t M) (3 * i) -> ratchet_spec M i.
  Proof.
    intros.
    unfold ratchet_spec in *.
    intros.
    assert (μ_r (f M i) (f M 0) = μ_r (f (t M) (3 * i)) (f (t M) 0)) by (now rewrite t_spec4). 
    rewrite H1.
    assert (μ_r (c M i) (c M 0) = μ_r (c (t M) (3 * i)) (c (t M) 0)) by (now rewrite t_spec5). 
    rewrite H2.
    rewrite t_spec3, t_spec6; auto.
  Qed.

  Definition lt_or_rot N :=
    lt N \/ N ≡ (0,1,-1,0).

  Lemma t_lt_or_rot M :
    forall i, lt_or_rot (t M i).
  Proof.
    intros.
    unfold lt_or_rot, t.
    destruct (M (i / 3)%nat) as [[[a b] c] d].
    destruct (decide _);
      destruct (mod3dec i);[destruct s| |destruct s|].
    - left. rewrite e. repeat eexists.
    - left. repeat eexists.
    - left. repeat eexists.
    - left. repeat eexists.
    - right. reflexivity.
    - left. repeat eexists.
  Qed.

  Lemma T_pos_det M i :
    (forall i, ratchet (M i)) -> 0 < det (T M i).
  Proof.
    intros.
    induction i.
    + reflexivity.
    + unfold T in *.
      rewrite (big_op_rev_S_l [*] 1) by lia. rewrite det_mul.
      specialize (H i).
      unfold ratchet in H.
      destruct H. cbn in *. nra.
  Qed.

  Lemma T0 M : T M 0 = I.
  Proof. unfold T. now rewrite big_op_rev_nil. Qed.

  Lemma v0_ M : v M 0 ≡ (f0, g0).
  Proof. unfold v. rewrite T0; split; simpl; lra. Qed.

  Lemma f0_ M : f M 0 ≡ f0.
  Proof. unfold f. rewrite v0_; simpl; lra. Qed.

  Theorem thm M :
    f0 ≢ 0 \/ g0 > 0 ->
    (forall i, ratchet (M i)) ->
    (forall i, lt_or_rot (M i)) ->
    (forall i, ratchet_spec M i).
  Proof.
    unfold ratchet_spec. intros.
    induction i.
    -
      unfold κ_r, κ_r', f, c, T.
      rewrite !big_op_nil, !big_op_rev_nil by lia.
      rewrite !μ_r_id. reflexivity.
    -
      pose proof (T_pos_det M i) as ti_det.
      unfold κ_r, κ_r'.
      rewrite !big_op_S_r by lia.
      fold (κ_r M i).
      fold (κ_r' M i).
      rewrite !IHi.
      rewrite <- !Z.add_assoc. apply f_equal.
      specialize (ti_det H0).
      specialize (H0 i).
      specialize (H1 i).
      destruct H1.
      +
        rewrite !aux3.
        rewrite ratchet_ut_vec_2 by assumption.
        rewrite ratchet_ut_vec by assumption.
        rewrite !caux3.
        rewrite ratchet_ut_mat_2 by assumption.
        rewrite ratchet_ut_mat by assumption.
        rewrite Z.add_0_l, Z.add_0_r. reflexivity.
      +
        rewrite !aux3.
        rewrite !caux3.

        (* weird but it works *)
        rewrite H1 at 1.
        rewrite H1 at 1.
        setoid_rewrite H1.
        (* end weird *)
        rewrite f0_ at 1.
        rewrite f0_ at 1.
        unfold c, f, v.
        rewrite T0.
        destruct (T M i) as [[[ai bi] ci] di].

        cbn -[Z.add Z.mul Z.sub Z.opp] in *.

        unfold μ_r.
        repeat (destruct (decide _)); try nra; try reflexivity.
        destruct H. nra.
        assert (ai < 0). nra.
        assert (ci < 0). nra. nra.
        destruct H. nra.
        assert (ci >= 0). nra.
        assert (ai >= 0). nra. nra.
  Qed.

  Theorem thm2 M :
    f0 ≢ 0 \/ g0 > 0 ->
    (forall i, ratchet (M i)) ->
    (forall i, ratchet_spec M i).
  Proof.
    intros.
    apply transform_spec2.
    assumption.
    apply thm. assumption.
    apply all_t_ratchet. assumption.
    apply t_lt_or_rot.
  Qed.
End __.

Local Open Scope Z.

Definition ratchetz (M : mat Z) :=
  (0 < det M) /\
    (0 <= M.1.1.1) /\ (0 <= M.1.1.2).

Definition μ (a b : Z) :=
  if decide (a < 0)
  then if decide (0 <= b)
       then 1%Z
       else 0
  else if decide (b < 0)
       then 1
       else 0.

(* lower triangular *)
Definition lt_z (N : mat Z) :=
  exists a c d, N ≡ (a, 0, c, d).

Definition lt_or_rot_z (N : mat Z) :=
  lt_z N \/ N ≡ (0,1,-1,0).

Local Coercion inject_Z : Z >-> Q.

Definition inj_matZ (M : mat Z) : mat Q :=
  let '(a,b,c,d) := M in (inject_Z a,inject_Z  b,inject_Z  c,inject_Z  d).
Definition inj_vecZ (M : vec Z) : vec Q :=
  let '(a,b) := M in (inject_Z a,inject_Z  b).

Definition inj_nat_matZ (M : nat -> mat Z) :=
  (fun i => (inj_matZ (M i))).
Instance : Proper ((≡) ==> (≡)) inj_matZ.
Proof.
  do 2 red; intros; unfold inj_matZ.
  destruct x as [[[? ? ] ? ]? ].
  destruct y as [[[? ? ] ? ]? ].
  split_pairs.
  repeat constructor; cbn in *; congruence.
Qed.

Local Open Scope lmod_scope.
Local Open Scope mat_scope.
Local Open Scope ring_scope.

Lemma inj_matZ_mult (N M : mat Z) :
  inj_matZ (N * M) ≡ inj_matZ N * inj_matZ M.
Proof. auto_mat; rewrite !inject_Z_plus, !inject_Z_mult; reflexivity.  Qed.

Lemma inj_matZ_vec_mult (N : mat Z) (v : vec Z) :
  ((inj_matZ N) ⋅ (inj_vecZ v)).1 = inject_Z (N ⋅ v).1.
Proof. auto_mat; rewrite !inject_Z_plus, !inject_Z_mult; reflexivity.  Qed.

Lemma inj_matZ112 (N : mat Z) :
  (inj_matZ N).1.1.2 ≡ inject_Z N.1.1.2.
Proof. auto_mat. Qed.

Local Open Scope lmod_scope.
Definition κ (f g : Z) (M : nat -> mat Z) i := big_sum (fun j => μ ((big_mul_rev M 0%nat (S j)) ⋅ (f, g)).1 ((big_mul_rev M 0%nat j) ⋅ (f, g)).1) 0%nat i.
Definition κ' (M : nat -> mat Z) i := big_sum (fun j => μ ((big_mul_rev M 0%nat (S j)).1.1.2) ((big_mul_rev M 0%nat j).1.1.2)) 0%nat i.

Lemma inject_Z_opp a : inject_Z (- a) = (- inject_Z a)%Q.
Proof. reflexivity. Qed.
Lemma inject_Z_0 : inject_Z 0 = 0%Q.
Proof. reflexivity. Qed.

Definition ratchetz_spec f g M i :=
  κ f g M i = (κ' M i) + ((μ (((big_mul_rev M 0%nat i) ⋅ (f, g)).1) f + (μ ((big_mul_rev M 0%nat i).1.1.2) 0)) mod 2)%Z.

Lemma inj1 (M : mat Z) : ratchet (inj_matZ M) -> ratchetz M.
Proof.
  intros.
  unfold ratchetz, ratchet in *.
  destruct H as [? [? ?]].
  destruct M as [[[? ?]?]?].
  unfold inj_matZ in *.
  split; unfold det in *; cbn -[Z.add Z.sub Z.mul Z.opp] in *.
  - now rewrite Zlt_Qlt, !inject_Z_plus, !inject_Z_opp, !inject_Z_mult, inject_Z_0.
  - now rewrite !Zle_Qle, !inject_Z_0 in *.
Qed.

Lemma inj12 (M : mat Z) : ratchetz M -> ratchet (inj_matZ M).
Proof.
  intros.
  unfold ratchetz, ratchet in *.
  destruct H as [? [? ?]].
  destruct M as [[[? ?]?]?].
  unfold inj_matZ in *.
  split; unfold det in *; cbn -[Z.add Z.sub Z.mul Z.opp] in *.
  - now rewrite Zlt_Qlt, !inject_Z_plus, !inject_Z_opp, !inject_Z_mult, inject_Z_0 in *.
  - now rewrite !Zle_Qle, !inject_Z_0 in *.
Qed.

Local Open Scope ring_scope.

Lemma inj2 (M : nat -> mat Z) i :
  big_mul_rev (inj_nat_matZ M) 0%nat i ≡ inj_matZ (big_mul_rev M 0%nat i).
Proof.
  induction i.
  - rewrite !big_op_rev_nil by lia; reflexivity.
  - rewrite !(big_op_rev_S_l [*] 1) by lia.
    rewrite IHi.
    unfold inj_nat_matZ.
    rewrite <- inj_matZ_mult. reflexivity.
Qed.

Lemma μ_r_μ (a b : Z) :
  μ_r a b = μ a b.
Proof.
  unfold μ_r, μ. repeat destruct (decide _); rewrite <- inject_Z_0, <- ?Zlt_Qlt, <- ?Zle_Qle in *; lia.
Qed.

Lemma inj3 (f g : Z) (M : nat -> mat Z) i :
  κ_r f g (inj_nat_matZ M) i = κ f g M i.
Proof.
  induction i; unfold κ, κ_r in *.
  - rewrite !big_op_nil by lia; reflexivity.
  - rewrite !big_op_S_r by lia.
    rewrite !IHi.
    apply f_equal.
    unfold Ratchet.f, v, T.
    rewrite !inj2.
    rewrite (big_op_rev_S_l [*] 1) by lia.
    replace (inject_Z f, inject_Z g) with (inj_vecZ (f, g)) by reflexivity.
    rewrite !inj_matZ_vec_mult.
    rewrite μ_r_μ.
    reflexivity.
Qed.

Lemma inj4 (M : nat -> mat Z) i :
  κ_r' (inj_nat_matZ M) i = κ' M i.
Proof.
  induction i; unfold κ', κ_r' in *.
  - rewrite !big_op_nil by lia; reflexivity.
  - rewrite !big_op_S_r by lia.
    rewrite !IHi.
    apply f_equal.
    unfold c, T.
    rewrite !inj2.
    rewrite (big_op_rev_S_l [*] 1) by lia.
    rewrite !inj_matZ112.
    rewrite μ_r_μ.
    reflexivity.
Qed.


Lemma inj5 (f g : Z) (M : nat -> mat Z) i : ratchet_spec f g (inj_nat_matZ M) i -> ratchetz_spec f g M i.
Proof.
  intros.
  unfold ratchet_spec in *.
  unfold ratchetz_spec.
  unfold Ratchet.f, c, v, T in *.
  rewrite !inj2 in H.
  replace (inject_Z f, inject_Z g) with (inj_vecZ (f, g)) in H.
  rewrite !inj_matZ_vec_mult in H.
  rewrite inj_matZ112 in H.
  rewrite !(big_op_rev_nil _ _ _ _ 0) in H.
  cbn -[Z.add Z.sub Z.mul Z.opp] in *.
  rewrite !μ_r_μ in *.
  rewrite Z.mul_1_l in H.
  rewrite Z.mul_0_l in H.
  rewrite Z.add_0_r in H.
  rewrite inj3, inj4 in H.
  assumption. lia. reflexivity.
Qed.

Require Import Divstep.

Lemma Tn_ratchet d f g i :
  ratchetz (Tn d f g i).
Proof.
  unfold ratchetz, det, Tn, Tmat.
  destruct (Nat.iter _ _ _) as [[dn fn] gn];
    destruct (Z.odd gn), (0 <? dn); cbn -[Z.add Z.sub Z.add Z.opp]; try lia.
Qed.

Theorem thm3 d f g :
  f <> 0 \/ 0 < g -> (forall i, ratchetz_spec f g (Tn d f g) i).
Proof.
  intros.
  apply inj5.
  apply thm2.
  destruct H. left. intros contra. inversion contra.
  ring_simplify in H1. contradiction.
  right.
  rewrite Zlt_Qlt in H. rewrite inject_Z_0 in H. assumption.
  intros.
  apply inj12.
  apply Tn_ratchet.
Qed.
