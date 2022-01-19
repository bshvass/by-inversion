Require Import ZArith micromega.Lia.
Require Import micromega.Lra.
Require Import micromega.Lqa.
Require Import List.
Require Import QArith.
Require Import Qpower.
Require Import MSets.
Require Import List.
Require Import Orders.
Require Import OrdersEx.
Require Import OrdersAlt.
Require Import FMapAVL.

From BY Require Import Q Qmin_list Impl Zpower_nat ListLemmas Tactics Matrix.

Import ListNotations.

Local Open Scope Q.

Module ZMap := FMapAVL.Make OrderedTypeEx.Z_as_OT.
Module ZZOT <: OrderedType := PairOrderedType Z_as_OT Z_as_OT.
Module ZZOTorig <: OrderedType.OrderedType := Backport_OT ZZOT.

Module ZZMap := FMapAVL.Make ZZOTorig.

Lemma ZZeq_dec (w i w0 i0 : Z) : {(w,i) = (w0,i0)} + {(w,i) <> (w0,i0)}.
Proof. destruct (Z.eq_dec w w0); destruct (Z.eq_dec i i0); [left; subst; reflexivity| | |]; right; congruence.  Qed.

Definition emptyZ := ZMap.empty.
Definition emptyZZ := ZZMap.empty.

Definition init_amap := emptyZ Q.
Definition init_aqmap := emptyZZ Q.
Definition init_bmap := emptyZ Q.
Definition init_bqmap := emptyZZ Q.
Definition init_gmap := emptyZZ Q.

Definition alphaQ_mem map w :=
  match ZMap.find w map with
  | Some a => (map, a)
  | _ => let res := alphaQ w in
        (ZMap.add w res map, res)
  end.

Definition alphaQ_quot_mem quot_map alpha_map w i :=
  match ZZMap.find (w, i) quot_map with
  | Some a => (quot_map, alpha_map, a)
  | _ => let (alphai_map, alphai) := alphaQ_mem alpha_map i in
        let (alphawi_map, alphawi) := alphaQ_mem alphai_map (w + i)%Z in
        let res := alphawi / alphai in
        (ZZMap.add (w, i) res quot_map, alphawi_map, res)
  end.

Fixpoint betaQ_mem_aux aq_map a_map w l n :=
  match n with
  | 0%nat => (aq_map, a_map, l)
  | S n => let '(q_map, a_map, res) := alphaQ_quot_mem aq_map a_map w (Z.of_nat n) in
          betaQ_mem_aux q_map a_map w (res :: l) n
  end.

Definition betaQ_mem b_map aq_map a_map w :=
  match ZMap.find w b_map with
  | Some res => (b_map, aq_map, a_map, res)
  | _ => if (w <=? 66)%Z
        then let '(q_map, a_map, l) := betaQ_mem_aux aq_map a_map w [] 68%nat in
             let res := Qmin_list l in
             (ZMap.add w res b_map, q_map, a_map, res)
        else let res := ((633/1024) ^ w) * (633^5 / (2^30 * 165219)) in
             (ZMap.add w res b_map, aq_map, a_map, res)
  end.

Definition betaQ_quot_mem bq_map b_map q_map a_map w j :=
  match ZZMap.find (w, j) bq_map with
  | Some b => (bq_map, b_map, q_map, a_map, b)
  | _ => let '(b_map, q_map, a_map, bwj) := betaQ_mem b_map q_map a_map (w + j)%Z in
        let res := bwj * 2^j * 70 / 169 in
        (ZZMap.add (w, j) res bq_map, b_map, q_map, a_map, res)
  end.

Fixpoint gammaQ_mem_aux bq_map b_map q_map a_map w e l n :=
  match n with
  | 0%nat => (bq_map, b_map, q_map, a_map, l)
  | S n => let '(bq_map, b_map, q_map, a_map, res) := betaQ_quot_mem bq_map b_map q_map a_map w ((Z.of_nat n) + e) in
          gammaQ_mem_aux bq_map b_map q_map a_map w e (res :: l) n
  end.

Definition gammaQ_mem g_map bq_map b_map q_map a_map w e :=
  match ZZMap.find (w, e) g_map with
  | Some a => (g_map, bq_map, b_map, q_map, a_map, a)
  | _ => if (w + e <=? 66)%Z
        then let '(bq_map, b_map, q_map, a_map, l) := gammaQ_mem_aux bq_map b_map q_map a_map w e [] 68%nat in
             let res := Qmin_list l in
             (ZZMap.add (w, e) res g_map, bq_map, b_map, q_map, a_map, res)
        else let res := 2 ^ e * ((633/1024) ^ (w + e)) * (70/169) * 633^5 / (2^30 * 165219) in
             (ZZMap.add (w, e) res g_map, bq_map, b_map, q_map, a_map, res)
  end.

Definition a_map_correct a_map := forall w, (0 <= w)%Z -> snd (alphaQ_mem a_map w) = alphaQ_nat (Z.to_nat w).

Definition aq_map_correct aq_map := forall a_map, a_map_correct a_map -> forall w i, (0 <= w)%Z -> (0 <= i)%Z -> snd (alphaQ_quot_mem aq_map a_map w i) = alphaQ_quot (Z.to_nat w) (Z.to_nat i).

Definition b_map_correct b_map := forall aq_map a_map, aq_map_correct aq_map -> a_map_correct a_map -> forall w, (0 <= w)%Z -> snd (betaQ_mem b_map aq_map a_map w) == betaQ (Z.to_nat w).

Definition bq_map_correct bq_map := forall b_map aq_map a_map, b_map_correct b_map -> aq_map_correct aq_map -> a_map_correct a_map -> forall w i, (0 <= w)%Z -> (0 <= i)%Z -> snd (betaQ_quot_mem bq_map b_map aq_map a_map w i) == betaQ_quot (Z.to_nat w) (Z.to_nat i).

Definition g_map_correct g_map := forall bq_map b_map aq_map a_map, bq_map_correct bq_map -> b_map_correct b_map -> aq_map_correct aq_map -> a_map_correct a_map -> forall w e, (0 <= w)%Z -> (0 <= e)%Z -> snd (gammaQ_mem g_map bq_map b_map aq_map a_map w e) == gammaQ (Z.to_nat w) (Z.to_nat e).

Lemma alphaQ_mem_spec a_map : a_map_correct a_map ->
                              forall w, (0 <= w)%Z -> let '(a_map, alpha_w) := alphaQ_mem a_map w in a_map_correct a_map /\ alpha_w = alphaQ_nat (Z.to_nat w).
Proof.
  intros. split_pairs. split.
  red; intros. unfold alphaQ_mem in H1.
  destruct (ZMap.find (elt:=Q) w a_map) eqn:E1; split_pairs.
  - apply H. assumption.
  - destruct (Z.eq_dec w w0).
    + subst.
      pose proof @ZMap.add_1 Q a_map w0 w0 (alphaQ w0) eq_refl.
      apply ZMap.find_1 in H1.
      unfold alphaQ_mem.
      rewrite H1. simpl. apply alphaQ_nat_alphaQ. assumption.
    + unfold a_map_correct in *. unfold alphaQ_mem.
      destruct (ZMap.find (elt:=Q) w0 (ZMap.add w (alphaQ w) a_map)) eqn:E.
      * apply ZMap.find_2 in E.
        apply ZMap.add_3 in E.
        apply ZMap.find_1 in E.
        specialize (H w0). unfold alphaQ_mem in H.
        rewrite E in H. simpl in *. apply H. assumption. assumption.
      * simpl. apply alphaQ_nat_alphaQ. assumption.
  - unfold a_map_correct in *.
    specialize (H w).
    rewrite H1 in H.
    simpl in *. apply H. assumption. Qed.

Lemma alphaQ_quot_mem_spec aq_map a_map : aq_map_correct aq_map -> a_map_correct a_map ->
                                          forall w i, (0 <= w)%Z -> (0 <= i)%Z -> let '(aq_map1, a_map1, alpha_quot_w_i) := alphaQ_quot_mem aq_map a_map w i in
                                                 aq_map_correct aq_map1 /\ a_map_correct a_map1 /\ alpha_quot_w_i = alphaQ_quot (Z.to_nat w) (Z.to_nat i).
Proof.
  intros. split_pairs; repeat split.
  - unfold alphaQ_quot_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, i) aq_map) eqn:E1; red; intros; split_pairs.
    + apply H; assumption.
    + apply alphaQ_mem_spec with (w:=i) in H0; try lia; split_pairs.
      apply alphaQ_mem_spec with (w:=(w+i)%Z) in H0; try lia; split_pairs.

      replace (Z.to_nat (w + i))%nat with ((Z.to_nat w) + (Z.to_nat i))%nat by lia.
      fold (alphaQ_quot (Z.to_nat w) (Z.to_nat i)).

      destruct (ZZeq_dec w i w0 i0) eqn:eqE; [inversion e|].
      * subst.
        unfold alphaQ_quot_mem.
        pose proof @ZZMap.add_1 Q aq_map (w0, i0) (w0, i0) (alphaQ_quot (Z.to_nat w0) (Z.to_nat i0)) ltac:(reflexivity).
        apply ZZMap.find_1 in H8.
        rewrite H8. reflexivity.
      * unfold aq_map_correct in *. unfold alphaQ_quot_mem.
        destruct (ZZMap.find (elt:=Q) (w0, i0) (ZZMap.add (w, i) (alphaQ_quot (Z.to_nat w) (Z.to_nat i)) aq_map)) eqn:E.
        ** apply ZZMap.find_2 in E.
           apply ZZMap.add_3 in E.
           apply ZZMap.find_1 in E.
           specialize (H a_map0 H4 w0 i0). unfold alphaQ_quot_mem in H.
           rewrite E in H. simpl in *. apply H; assumption. intros contra. inversion contra. apply n.
           inversion H8.
           inversion H9. simpl in *. subst. reflexivity.
        ** subst.
           apply alphaQ_mem_spec with (w:=i0) in H4; split_pairs.
           apply alphaQ_mem_spec with (w:=(w0+i0)%Z) in H4; split_pairs.
           replace (Z.to_nat (w0 + i0)) with ((Z.to_nat w0) + (Z.to_nat i0))%nat by lia.
           reflexivity. lia. lia.
  - red; intros; split_pairs.
    unfold alphaQ_quot_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, i) aq_map) eqn:E1; split_pairs.
    + apply H0. assumption.
    + apply alphaQ_mem_spec with (w:=i) in H0. split_pairs.
      apply alphaQ_mem_spec with (w:=(w+i)%Z) in H0. split_pairs.
      apply H0; lia. lia. lia.
  - specialize (H a_map H0 w i H1 H2).
    rewrite H3 in H. simpl in *. assumption. Qed.

Lemma betaQ_mem_aux_spec aq_map a_map n l' : a_map_correct a_map -> aq_map_correct aq_map -> forall w, (0 <= w)%Z -> let '(aq_map, a_map, l) := betaQ_mem_aux aq_map a_map w l' n in aq_map_correct aq_map /\ a_map_correct a_map /\ l = betaQ_aux (Z.to_nat w) n ++ l'.
Proof.
  revert aq_map a_map l'.
  induction n; intros; cbn -[Z.of_nat] in *; split_pairs; repeat split; try assumption.
  -
    pose proof @alphaQ_mem_spec a_map H w H1.
    pose proof @alphaQ_quot_mem_spec aq_map a_map H0 H w (Z.of_nat n) H1 ltac:(lia).
    split_pairs.
    rewrite Nat2Z.id in *.
    specialize (IHn t1 t2 ((alphaQ_quot (Z.to_nat w) n) :: l') H9 H5 w H1); split_pairs; assumption.
  - pose proof @alphaQ_mem_spec a_map H w H1.
    pose proof @alphaQ_quot_mem_spec aq_map a_map H0 H w (Z.of_nat n) H1 ltac:(lia).
    split_pairs.
    rewrite Nat2Z.id in *.
    specialize (IHn t1 t2 ((alphaQ_quot (Z.to_nat w) n) :: l') H9 H5 w H1); split_pairs; assumption.
  - pose proof @alphaQ_mem_spec a_map H w H1.
    pose proof @alphaQ_quot_mem_spec aq_map a_map H0 H w (Z.of_nat n) H1 ltac:(lia).
    split_pairs.
    rewrite Nat2Z.id in *.
    specialize (IHn t1 t2 ((alphaQ_quot (Z.to_nat w) n) :: l') H9 H5 w H1).
    split_pairs.

    unfold betaQ_aux.
    replace (_ :: _) with ([alphaQ_quot (Z.to_nat w) n] ++ l') by reflexivity.
    rewrite app_assoc.
    rewrite app_comm_cons.
    apply f_equal2.
    rewrite cons_map_seq.
    rewrite map_seq_snoc. reflexivity. reflexivity. Qed.

Lemma betaQ_mem_spec b_map aq_map a_map : b_map_correct b_map -> aq_map_correct aq_map -> a_map_correct a_map ->
                                          forall w, (0 <= w)%Z -> let '(b_map, aq_map, a_map, beta_w) := betaQ_mem b_map aq_map a_map w in b_map_correct b_map /\ aq_map_correct aq_map /\ a_map_correct a_map /\ beta_w == betaQ (Z.to_nat w).
Proof.
  intros. split_pairs. repeat split.
  - unfold betaQ_mem in *.
    destruct (ZMap.find (elt:=Q) w b_map) eqn:E1; split_pairs.
    + assumption.
    + red; intros.
      pose proof @betaQ_mem_aux_spec aq_map a_map 68%nat [] H1 H0 w H2; split_pairs.
      destruct (Z.eq_dec w w0) eqn:eqE; [inversion e|].
      * subst.
        rewrite betaQ_spec.
        unfold betaQ_mem.
        destruct (w0 <=? 66)%Z eqn:leE.
        ** assert ((Z.to_nat w0 <=? 66)%nat = true). apply Z.leb_le in leE. apply Nat.leb_le. lia.
           rewrite H10.
           rewrite app_nil_r in H3.
           fold (betaQ (Z.to_nat w0)) in H3; split_pairs.
           pose proof @ZMap.add_1 Q b_map w0 w0 (betaQ (Z.to_nat w0)) ltac:(reflexivity).
           apply ZMap.find_1 in H3.
           rewrite H3. reflexivity.
        ** assert ((Z.to_nat w0 <=? 66)%nat = false). apply Z.leb_gt in leE. apply Nat.leb_gt. lia.
           pose proof @ZMap.add_1 Q b_map w0 w0 (((633 / 1024) ^ w0 * (633 ^ 5 / (2 ^ 30 * 165219)))) ltac:(reflexivity).
           rewrite H10. split_pairs.
           apply ZMap.find_1 in H12. rewrite H12.
           cbn -[Z.of_nat]. rewrite Z2Nat.id. field. lia.
      * unfold betaQ_mem.
        destruct (w <=? 66)%Z eqn:leE.
        ** assert ((Z.to_nat w <=? 66)%nat = true). apply Z.leb_le in leE. apply Nat.leb_le. lia.
           rewrite app_nil_r in H3. split_pairs.
           destruct (ZMap.find (elt:=Q) w0 (ZMap.add w (Qmin_list (betaQ_aux (Z.to_nat w) 68)) b_map)) eqn:E.
           *** apply ZMap.find_2 in E.
               apply ZMap.add_3 in E.
               apply ZMap.find_1 in E.
               specialize (H _ _ H0 H1 w0 H7).
               unfold betaQ_mem in H.
               rewrite E in H. assumption. assumption.
           *** rewrite betaQ_spec.
               destruct (w0 <=? 66)%Z eqn:leE0.
               assert ((Z.to_nat w0 <=? 66)%nat = true). apply Z.leb_le in leE0. apply Nat.leb_le. lia.
               rewrite H3. pose proof @betaQ_mem_aux_spec aq_map0 a_map0 68%nat [] H6 H5 w0 H7. split_pairs. reflexivity.

               assert ((Z.to_nat w0 <=? 66)%nat = false). apply Z.leb_gt in leE0. apply Nat.leb_gt. lia.
               rewrite H3.
               rewrite Z2Nat.id. simpl; field. assumption.
        ** assert ((Z.to_nat w <=? 66)%nat = false). apply Z.leb_gt in leE. apply Nat.leb_gt. lia.
           split_pairs.
           destruct (ZMap.find (elt:=Q) w0 (ZMap.add w ((633 / 1024) ^ w * (633 ^ 5 / (2 ^ 30 * 165219))) b_map)) eqn:E.
           *** apply ZMap.find_2 in E.
               apply ZMap.add_3 in E.
               apply ZMap.find_1 in E.
               specialize (H _ _ H0 H1 w0 H7).
               unfold betaQ_mem in H.
               rewrite E in H. assumption. assumption.
           *** rewrite betaQ_spec.
               destruct (w0 <=? 66)%Z eqn:leE0.
               assert ((Z.to_nat w0 <=? 66)%nat = true). apply Z.leb_le in leE0. apply Nat.leb_le. lia.
               rewrite H3. pose proof @betaQ_mem_aux_spec aq_map0 a_map0 68%nat [] H6 H5 w0 H7. split_pairs. reflexivity.

               assert ((Z.to_nat w0 <=? 66)%nat = false). apply Z.leb_gt in leE0. apply Nat.leb_gt. lia.
               rewrite H3.
               rewrite Z2Nat.id. simpl; field. assumption.
  - unfold betaQ_mem in *.
    destruct (ZMap.find (elt:=Q) w b_map); split_pairs; [assumption|].
    destruct ((w <=? 66)%Z); split_pairs; [|assumption].
    pose proof @betaQ_mem_aux_spec aq_map a_map 68%nat [] H1 H0 w H2; split_pairs; assumption.
  - unfold betaQ_mem in *.
    destruct (ZMap.find (elt:=Q) w b_map); split_pairs; [assumption|].
    destruct ((w <=? 66)%Z); split_pairs; [|assumption].
    pose proof @betaQ_mem_aux_spec aq_map a_map 68%nat [] H1 H0 w H2; split_pairs; assumption.
  -
    specialize (H aq_map a_map H0 H1 w H2).
    rewrite <- H, H3; reflexivity. Qed.

Lemma betaQ_quot_mem_spec bq_map b_map aq_map a_map :
  bq_map_correct bq_map -> b_map_correct b_map -> aq_map_correct aq_map -> a_map_correct a_map ->
  forall w j, (0 <= w)%Z -> (0 <= j)%Z ->
         let '(bq_map, b_map, aq_map, a_map, beta_quot_w_j) := betaQ_quot_mem bq_map b_map aq_map a_map w j in
         bq_map_correct bq_map /\ b_map_correct b_map /\ aq_map_correct aq_map /\ a_map_correct a_map /\ beta_quot_w_j == betaQ_quot (Z.to_nat w) (Z.to_nat j).
Proof.
  intros. split_pairs. repeat split.
  - unfold betaQ_quot_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, j) bq_map) eqn:E1; split_pairs.
    + assumption.
    + red; intros.
      pose proof @betaQ_mem_spec b_map aq_map a_map H0 H1 H2 (w + j)%Z ltac:(lia); split_pairs.

      destruct (ZZeq_dec w j w0 i); unfold betaQ_quot_mem; split_pairs.
      *
        unfold betaQ_quot. replace ((Z.to_nat w0 + Z.to_nat i)%nat) with (Z.to_nat (w0 + i)) by lia. rewrite Z2Nat.id by lia.

        pose proof @ZZMap.add_1 Q bq_map (w0, i) (w0, i) (q0 * 2 ^ i * 70 / 169) ltac:(reflexivity) as zzadd.
        apply ZZMap.find_1 in zzadd.
        rewrite zzadd. simpl. rewrite H17. reflexivity.
      * destruct (ZZMap.find (elt:=Q) (w0, i) (ZZMap.add (w, j) (q0 * 2 ^ j * 70 / 169) bq_map))  eqn:E.
        ** apply ZZMap.find_2 in E.
           apply ZZMap.add_3 in E.
           apply ZZMap.find_1 in E.
           specialize (H _ _ _ H0 H1 H2 w0 i H9 H10).
           unfold betaQ_quot_mem in H.
           rewrite E in H. assumption.
           intros contra. inversion contra. inversion H13. inversion H14. simpl in *. subst. contradiction.
        ** pose proof @betaQ_mem_spec b_map0 aq_map0 a_map0 H5 H7 H8 (w0 + i) ltac:(lia). split_pairs. simpl.
           unfold betaQ_quot. replace ((Z.to_nat w0 + Z.to_nat i)%nat) with (Z.to_nat (w0 + i)) by lia. rewrite Z2Nat.id by lia.
           rewrite H22. reflexivity.
  - unfold betaQ_quot_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, j)); split_pairs; [assumption|].
    pose proof @betaQ_mem_spec _ _ _ H0 H1 H2 (w + j)%Z ltac:(lia); split_pairs; assumption.
  - unfold betaQ_quot_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, j)); split_pairs; [assumption|].
    pose proof @betaQ_mem_spec _ _ _ H0 H1 H2 (w + j)%Z ltac:(lia); split_pairs; assumption.
  - unfold betaQ_quot_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, j)); split_pairs; [assumption|].
    pose proof @betaQ_mem_spec _ _ _ H0 H1 H2 (w + j)%Z ltac:(lia); split_pairs; assumption.
  - specialize (H _ _ _ H0 H1 H2 _ _ H3 H4).
    rewrite <- H, H5; reflexivity. Qed.

Lemma gammaQ_lemma bq_map b_map aq_map a_map w e l l' n :
  fst (gammaQ_mem_aux bq_map b_map aq_map a_map w e l n) =
  fst (gammaQ_mem_aux bq_map b_map aq_map a_map w e l' n).
Proof.
  revert bq_map b_map aq_map a_map l l'.
  induction n; intros; simpl; split_pairs; try reflexivity. apply IHn. Qed.

Lemma gammaQ_mem_aux_spec bq_map b_map aq_map a_map n l' :
  bq_map_correct bq_map -> b_map_correct b_map -> aq_map_correct aq_map -> a_map_correct a_map ->
  forall w e, (0 <= w)%Z -> (0 <= e)%Z -> let '(bq_map, b_map, aq_map, a_map, l) := gammaQ_mem_aux bq_map b_map aq_map a_map w e l' n in
                                 bq_map_correct bq_map /\
                                 b_map_correct b_map /\
                                 aq_map_correct aq_map /\
                                 a_map_correct a_map /\
                                 Qlist_eq l (gammaQ_aux (Z.to_nat w) (Z.to_nat e) n ++ l').
Proof.
  revert bq_map b_map aq_map a_map l'.
  induction n; intros; cbn -[Z.of_nat Z.to_nat Z.add] in *; split_pairs; repeat split; try assumption.
  - reflexivity.
  -
    pose proof @alphaQ_mem_spec a_map H2 w H3.
    pose proof @alphaQ_quot_mem_spec aq_map a_map ltac:(auto) ltac:(auto) w (Z.of_nat n) ltac:(auto) ltac:(lia).
    pose proof @betaQ_mem_spec b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) w ltac:(lia).
    pose proof @betaQ_quot_mem_spec bq_map b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w (Z.of_nat n + e) ltac:(lia) ltac:(lia).
    split_pairs.
    specialize (IHn t5 t6 t4 t3 ((betaQ_quot (Z.to_nat w) (Z.to_nat (Z.of_nat n + e))%nat) :: l')
                    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w e ltac:(lia) ltac:(lia)).
    split_pairs.
    pose proof gammaQ_lemma t5 t6 t4 t3 w e (q :: l') (betaQ_quot (Z.to_nat w) (Z.to_nat (Z.of_nat n + e)) :: l') n.
    rewrite H5, H9 in H12. simpl in H12. split_pairs.
    assumption.
  -
    pose proof @alphaQ_mem_spec a_map H2 w ltac:(auto).
    pose proof @alphaQ_quot_mem_spec aq_map a_map ltac:(auto) ltac:(auto) w (Z.of_nat n) ltac:(auto) ltac:(lia).
    pose proof @betaQ_mem_spec b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) w ltac:(lia).
    pose proof @betaQ_quot_mem_spec bq_map b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w (Z.of_nat n + e) ltac:(lia) ltac:(lia).
    split_pairs.
    specialize (IHn t5 t6 t4 t3 ((betaQ_quot (Z.to_nat w) (Z.to_nat (Z.of_nat n + e))%nat) :: l')
                    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w e ltac:(lia) ltac:(lia)).
    split_pairs.
    pose proof gammaQ_lemma t5 t6 t4 t3 w e (q :: l') (betaQ_quot (Z.to_nat w) (Z.to_nat (Z.of_nat n + e)) :: l') n.
    rewrite H9, H5 in H12. simpl in H12. split_pairs. assumption.
  -
    pose proof @alphaQ_mem_spec a_map H2 w ltac:(auto).
    pose proof @alphaQ_quot_mem_spec aq_map a_map ltac:(auto) ltac:(auto) w (Z.of_nat n) ltac:(auto) ltac:(lia).
    pose proof @betaQ_mem_spec b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) w ltac:(lia).
    pose proof @betaQ_quot_mem_spec bq_map b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w (Z.of_nat n + e) ltac:(lia) ltac:(lia).
    split_pairs.
    rewrite Nat2Z.id in *.
    specialize (IHn t5 t6 t4 t3 ((betaQ_quot (Z.to_nat w) (Z.to_nat (Z.of_nat n + e))%nat) :: l')
                    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w e ltac:(lia) ltac:(lia)).
    split_pairs.
    pose proof @gammaQ_lemma t5 t6 t4 t3 w e (q :: l') (betaQ_quot (Z.to_nat w) (Z.to_nat (Z.of_nat n + e)) :: l') n.
    rewrite H9, H5 in H12. simpl in H12. split_pairs. assumption.
  -
    pose proof @alphaQ_mem_spec a_map H2 w ltac:(auto).
    pose proof @alphaQ_quot_mem_spec aq_map a_map ltac:(auto) ltac:(auto) w (Z.of_nat n) ltac:(auto) ltac:(lia).
    pose proof @betaQ_mem_spec b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) w ltac:(lia).
    pose proof @betaQ_quot_mem_spec bq_map b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w (Z.of_nat n + e) ltac:(lia) ltac:(lia).
    split_pairs.
    rewrite Nat2Z.id in *.
    specialize (IHn t5 t6 t4 t3 ((betaQ_quot (Z.to_nat w) (Z.to_nat (Z.of_nat n + e))%nat) :: l')
                    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w e ltac:(lia) ltac:(lia)).
    split_pairs.
    pose proof gammaQ_lemma t5 t6 t4 t3 w e (q :: l') (betaQ_quot (Z.to_nat w) (Z.to_nat (Z.of_nat n + e)) :: l') n.
    rewrite H9, H5 in H12. simpl in H12. split_pairs. assumption.
  -
    pose proof @alphaQ_mem_spec a_map H2 w ltac:(auto).
    pose proof @alphaQ_quot_mem_spec aq_map a_map ltac:(auto) ltac:(auto) w (Z.of_nat n) ltac:(auto) ltac:(lia).
    pose proof @betaQ_mem_spec b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) w ltac:(lia).
    pose proof @betaQ_quot_mem_spec bq_map b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w (Z.of_nat n + e) ltac:(lia) ltac:(lia).
    split_pairs.
    rewrite Nat2Z.id in *.
    assert (IHn2 := IHn).
    specialize (IHn t5 t6 t4 t3 ((betaQ_quot (Z.to_nat w) (Z.to_nat e + n)%nat) :: l')
                    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w e ltac:(lia) ltac:(lia)).
    specialize (IHn2 t5 t6 t4 t3 (q :: l')
                    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w e ltac:(lia) ltac:(lia)).
    split_pairs.
    pose proof gammaQ_lemma t5 t6 t4 t3 w e (q :: l') (betaQ_quot (Z.to_nat w) (Z.to_nat e + n) :: l') n.
    setoid_rewrite H34. unfold gammaQ_aux.

    setoid_rewrite H24.

    replace (_ :: _) with ([betaQ_quot (Z.to_nat w) (Z.to_nat (Z.of_nat n + e))] ++ l') by reflexivity.
    rewrite app_assoc.
    rewrite app_comm_cons.
    rewrite cons_map_seq.
    rewrite map_seq_snoc.
    replace ((Z.to_nat (Z.of_nat n + e))) with (Z.to_nat e + n)%nat by lia.
    reflexivity. Qed.

Lemma gammaQ_mem_spec g_map bq_map b_map aq_map a_map :
  g_map_correct g_map -> bq_map_correct bq_map -> b_map_correct b_map -> aq_map_correct aq_map -> a_map_correct a_map ->
  forall w e, (0 <= w)%Z -> (0 <= e)%Z ->
       let '(g_map, bq_map, b_map, aq_map, a_map, gamma_w_e) := gammaQ_mem g_map bq_map b_map aq_map a_map w e
       in g_map_correct g_map /\
          bq_map_correct bq_map /\
          b_map_correct b_map /\
          aq_map_correct aq_map /\
          a_map_correct a_map /\
          (gamma_w_e == gammaQ (Z.to_nat w) (Z.to_nat e))%Q.
Proof.
  intros. split_pairs. repeat split.
  - unfold gammaQ_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, e) g_map) eqn:E1; split_pairs.
    + assumption.
    + red; intros.
      pose proof @gammaQ_mem_aux_spec bq_map b_map aq_map a_map 68%nat [] H0 H1 H2 H3 w e H4 H5; split_pairs.
      destruct (ZZeq_dec w e w0 e0); [|].
      * split_pairs.
        unfold gammaQ_mem.
        destruct (w0 + e0 <=? 66)%Z eqn:leE; split_pairs.
        ** assert ((Z.to_nat w0 + Z.to_nat e0 <=? 66)%nat = true). apply Z.leb_le in leE. apply Nat.leb_le. lia.
           pose proof @ZZMap.add_1 Q g_map (w0, e0) (w0, e0) (Qmin_list l) ltac:(reflexivity) as zzmapadd.
           apply ZZMap.find_1 in zzmapadd.
           rewrite zzmapadd. simpl. setoid_rewrite H22.
           rewrite app_nil_r.
           unfold gammaQ.
           reflexivity.
        ** assert ((Z.to_nat w0 + Z.to_nat e0 <=? 66)%nat = false) as ineq. apply Z.leb_gt in leE. apply Nat.leb_gt. lia.
           rewrite gammaQ_spec.
           rewrite ineq.
           pose proof @ZZMap.add_1 Q g_map (w0, e0) (w0, e0)
                (2 ^ e0 * (633 / 1024) ^ (w0 + e0) * (70 / 169) * 633 ^ 5 / (2 ^ 30 * 165219)) ltac:(reflexivity)
             as zzmapadd.
           apply ZZMap.find_1 in zzmapadd. rewrite zzmapadd.
           cbn -[Z.add Z.to_nat Z.of_nat]. rewrite Z2Nat.id.
           replace (Z.of_nat (Z.to_nat w0 + Z.to_nat e0)) with (w0 + e0)%Z by lia.
           field. lia.
      * unfold gammaQ_mem.
        destruct (w + e <=? 66)%Z eqn:leE.
        ** assert ((Z.to_nat (w + e) <=? 66)%nat = true). apply Z.leb_le in leE. apply Nat.leb_le. lia.
           rewrite app_nil_r in H22. split_pairs.
           destruct (ZZMap.find (elt:=Q) (w0, e0) (ZZMap.add (w, e) (Qmin_list l) g_map)) eqn:E.
           *** apply ZZMap.find_2 in E.
               apply ZZMap.add_3 in E.
               apply ZZMap.find_1 in E.
               specialize (H _ _ _ _ H0 H1 H2 H3 w0 e0 H12 H13).
               unfold gammaQ_mem in H.
               rewrite E in H. assumption.
               red. intros. inversion H6. inversion H17. inversion H18. simpl in H23. simpl in H24.
               subst. contradiction.
           *** rewrite gammaQ_spec.
               destruct ((w0 + e0) <=? 66)%Z eqn:leE0.
               assert ((Z.to_nat w0 + Z.to_nat e0 <=? 66)%nat = true). apply Z.leb_le in leE0. apply Nat.leb_le. lia.
               rewrite H6.
               pose proof @gammaQ_mem_aux_spec _ _ _ _ 68%nat [] H8 H9 H10 H11 w0 e0 H12 H13.
               split_pairs. simpl.
               rewrite app_nil_r in H29. setoid_rewrite H29.
               unfold gammaQ. reflexivity.
               assert ((Z.to_nat w0 + Z.to_nat e0 <=? 66)%nat = false). apply Z.leb_gt in leE0. apply Nat.leb_gt. lia.
               rewrite H6.
               Arguments Z.of_nat : simpl never.
               Arguments Z.to_nat : simpl never.
               Arguments Z.add : simpl never.
               cbn. rewrite Z2Nat.id.
               replace (Z.of_nat (Z.to_nat w0 + Z.to_nat e0)) with (w0 + e0)%Z by lia.
               field. assumption.
        ** assert ((Z.to_nat w + Z.to_nat e <=? 66)%nat = false). apply Z.leb_gt in leE. apply Nat.leb_gt. lia.
           split_pairs.
           destruct (ZZMap.find (elt:=Q) (w0, e0)
                               (ZZMap.add (w, e) (2 ^ e * (633 / 1024) ^ (w + e) * (70 / 169) * 633 ^ 5 / (2 ^ 30 * 165219)) g_map))
                    eqn:E.
           *** apply ZZMap.find_2 in E.
               apply ZZMap.add_3 in E.
               apply ZZMap.find_1 in E.
               specialize (H _ _ _ _ H0 H1 H2 H3 w0 e0 ltac:(lia) ltac:(lia)).
               unfold gammaQ_mem in H.
               rewrite E in H. assumption.
               red. intros. inversion H6. inversion H17. inversion H18. simpl in H23. simpl in H24.
               subst. contradiction.
           *** rewrite gammaQ_spec.
               destruct (w0 + e0 <=? 66)%Z eqn:leE0.
               assert ((Z.to_nat w0 + Z.to_nat e0 <=? 66)%nat = true). apply Z.leb_le in leE0. apply Nat.leb_le. lia.
               rewrite H6.
               pose proof @gammaQ_mem_aux_spec _ _ _ _ 68%nat [] H8 H9 H10 H11 _ _ H12 H13. split_pairs.
               simpl. rewrite H29. unfold gammaQ. reflexivity.

               assert ((Z.to_nat w0 + Z.to_nat e0 <=? 66)%nat = false). apply Z.leb_gt in leE0. apply Nat.leb_gt. lia.
               rewrite H6.
               rewrite Z2Nat.id. simpl.
               replace (Z.of_nat (Z.to_nat w0 + Z.to_nat e0)) with (w0 + e0)%Z by lia.
               field. assumption.
  - unfold gammaQ_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, e) g_map); split_pairs; [assumption|].
    destruct ((w + e <=? 66)%Z); split_pairs; [|assumption].
    pose proof @gammaQ_mem_aux_spec _ _ _ _ 68%nat [] H0 H1 H2 H3 _ _ H4 H5; split_pairs; assumption.
  - unfold gammaQ_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, e) g_map); split_pairs; [assumption|].
    destruct ((w + e <=? 66)%Z); split_pairs; [|assumption].
    pose proof @gammaQ_mem_aux_spec _ _ _ _ 68%nat [] H0 H1 H2 H3 _ _ H4 H5; split_pairs; assumption.
  - unfold gammaQ_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, e) g_map); split_pairs; [assumption|].
    destruct ((w + e <=? 66)%Z); split_pairs; [|assumption].
    pose proof @gammaQ_mem_aux_spec _ _ _ _ 68%nat [] H0 H1 H2 H3 _ _ H4 H5; split_pairs; assumption.
  - unfold gammaQ_mem in *.
    destruct (ZZMap.find (elt:=Q) (w, e) g_map); split_pairs; [assumption|].
    destruct ((w + e <=? 66)%Z); split_pairs; [|assumption].
    pose proof @gammaQ_mem_aux_spec _ _ _ _ 68%nat [] H0 H1 H2 H3 _ _ H4 H5; split_pairs; assumption.
  -
    specialize (H _ _ _ _ H0 H1 H2 H3 _ _ H4 H5).
    rewrite <- H, H6; reflexivity. Qed.

Lemma init_a_map_correct : a_map_correct init_amap.
Proof. red; intros; apply alphaQ_nat_alphaQ; assumption. Qed.

Lemma init_aq_map_correct : aq_map_correct init_aqmap.
Proof. red; intros. unfold alphaQ_quot_mem. split_pairs.
       epose proof @alphaQ_mem_spec a_map _ i _; split_pairs.
       epose proof @alphaQ_mem_spec t _ (w + i) _; split_pairs.
       unfold alphaQ_quot. rewrite Z2Nat.inj_add by lia. reflexivity.
       Unshelve. all: assumption || lia.
Qed.

Lemma init_b_map_correct : b_map_correct init_bmap.
Proof. red; intros; unfold betaQ_mem; split_pairs.
       epose proof @betaQ_mem_aux_spec aq_map a_map 68%nat [] _ _ w _; split_pairs.
       rewrite betaQ_spec.
       replace (Z.to_nat w <=? 66)%nat with (w <=? 66)%Z.
       rewrite Z2Nat.id. rewrite app_nil_r. fold (betaQ (Z.to_nat w)).
       destruct (w <=? 66)%Z; reflexivity. assumption.

       destruct (Z.to_nat w <=? 66)%nat eqn:E; [apply Nat.leb_le in E; apply Z.leb_le | apply Nat.leb_gt in E; apply Z.leb_gt ]; lia.
       Unshelve. all: assumption || lia.
Qed.

Lemma init_bq_map_correct : bq_map_correct init_bqmap.
Proof. red; intros; unfold betaQ_quot_mem; split_pairs.
       epose proof @betaQ_mem_spec b_map aq_map a_map _ _ _ (w + i) _; split_pairs.
       simpl.  rewrite H11. unfold betaQ_quot.
       rewrite Z2Nat.id, Z2Nat.inj_add by lia. reflexivity.
       Unshelve. all: assumption || lia.
Qed.

Lemma init_g_map_correct : g_map_correct init_gmap.
Proof. red; intros; unfold gammaQ_mem; split_pairs.
       epose proof @gammaQ_mem_aux_spec bq_map b_map aq_map a_map 68%nat [] _ _ _ _ w e _ _; split_pairs.
       rewrite gammaQ_spec.
       replace (Z.to_nat w + Z.to_nat e <=? 66)%nat with (w + e <=? 66)%Z.
       simpl.
       destruct (w + e <=? 66)%Z; [unfold gammaQ; cbn [snd]; rewrite H14, app_nil_r|rewrite <- Z2Nat.inj_add, !Z2Nat.id by lia];
         reflexivity || cbn; field.
       destruct (Z.to_nat w + Z.to_nat e <=? 66)%nat eqn:E; [apply Nat.leb_le in E; apply Z.leb_le | apply Nat.leb_gt in E; apply Z.leb_gt ]; lia.
       Unshelve. all: assumption || lia.
Qed.

Fixpoint depth_first_verify_aux_no_mem_three_fuel_gen m (nodes nodes0 cnodes0 w e0 : Z) fuel1 fuel2 :=
  match fuel1 with
  | 0%nat => None
  | S fuel1 =>
    let mm := mmult (mtrans m) m in
    if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None
    else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w))
         then Some nodes
         else (fix inner_loop e nodes fuel3 :=
                 match fuel3 with
                 | 0%nat => None
                 | S fuel4 => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e)))
                            then Some nodes
                            else match
                                (fix verify_children cnodes fuel5 :=
                                   match fuel5 with
                                   | 0%nat => Some cnodes
                                   | S fuel6 => let q := ((2 * fuel6) + 1)%nat in
                                           match
                                             depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat q)) m) nodes0 nodes0 cnodes0 (e + w)%Z e0 fuel1 fuel2 with
                                           | None => None
                                           | Some nodes =>
                                             verify_children (nodes + cnodes)%Z fuel6
                                           end
                                   end) cnodes0 (Z.to_nat (2 ^ e)) with
                              | None => None
                              | Some cnodes =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel4
                              end
                 end) e0 nodes fuel2
  end.

Fixpoint depth_first_verify_aux_three_fuel_gen m (nodes nodes0 cnodes0 w e0 : Z) fuel1 fuel2 a_map b_map g_map bq_map aq_map :=
  match fuel1 with
  | 0%nat => None
  | S fuel1 =>
    let mm := mmult (mtrans m) m in
    let '(a_map, alpha_w) := alphaQ_mem a_map w in
    let '(b_map, aq_map, a_map, beta_w) := betaQ_mem b_map aq_map a_map w in
    if negb (has_at_most_norm mm ((4^w) * alpha_w)) then None
    else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * beta_w)
         then Some (a_map, b_map, g_map, bq_map, aq_map, nodes)
         else (fix inner_loop e nodes fuel3 a_map b_map g_map bq_map aq_map :=
                 match fuel3 with
                 | 0%nat => None
                 | S fuel4 => let '(g_map, bq_map, b_map, aq_map, a_map, gamma_w_e) := gammaQ_mem g_map bq_map b_map aq_map a_map w e in
                            if has_at_most_norm mm ((4^w) * gamma_w_e)
                            then Some (a_map, b_map, g_map, bq_map, aq_map, nodes)
                            else match
                                (fix verify_children cnodes a_map b_map g_map bq_map aq_map fuel5 :=
                                   match fuel5 with
                                   | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes)
                                   | S fuel6 => let q := ((2 * fuel6) + 1)%nat in
                                           match
                                             depth_first_verify_aux_three_fuel_gen (mmult (scaledM e (Z.of_nat q)) m) nodes0 nodes0 cnodes0 (e + w)%Z e0 fuel1 fuel2 a_map b_map g_map bq_map aq_map with
                                           | None => None
                                           | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) =>
                                             verify_children (nodes + cnodes)%Z a_map b_map g_map bq_map aq_map fuel6
                                           end
                                   end) cnodes0 a_map b_map g_map bq_map aq_map (Z.to_nat (2 ^ e)) with
                              | None => None
                              | Some (a_map, b_map, g_map, bq_map, aq_map, cnodes) =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel4 a_map b_map g_map bq_map aq_map
                              end
                 end) e0 nodes fuel2 a_map b_map g_map bq_map aq_map
  end.

(** [pose proof defn], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn
  end.

(** [pose defn], but only if that hypothesis doesn't exist *)
Tactic Notation "unique" "pose" constr(defn) :=
  lazymatch goal with
  | [ H := defn |- _ ] => fail
  | _ => pose defn
  end.

(** [assert T], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "assert" constr(T) :=
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => assert T
  end.

(** [assert T], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "assert" constr(T) "by" tactic3(tac) :=
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => assert T by tac
  end.

Ltac memt :=
  repeat (match goal with
          | [ H : alphaQ_mem ?a_map ?w = _ |- _ ] =>
            unique pose proof (@alphaQ_mem_spec a_map ltac:(auto) w ltac:(lia)); rewrite H in *; clear H; split_pairs
          | [ H : betaQ_mem ?b_map ?aq_map ?a_map ?w = _ |- _ ] =>
            unique pose proof (@betaQ_mem_spec b_map aq_map a_map ltac:(auto) ltac:(auto) ltac:(auto) w ltac:(lia)); rewrite H in *; clear H; split_pairs
          | [ H : gammaQ_mem ?g_map ?bq_map ?b_map ?aq_map ?a_map ?w ?e = _ |- _ ] =>
            unique pose proof (@gammaQ_mem_spec g_map bq_map b_map aq_map a_map
                                               ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) w e ltac:(lia) ltac:(lia)); rewrite H in *; clear H; split_pairs
         end).

Lemma mem_no_mem_three_fuel_aux m nodes nodes0 cnodes0 w e0 fuel1 fuel2 a_map b_map g_map bq_map aq_map :
  a_map_correct a_map ->
  b_map_correct b_map ->
  g_map_correct g_map ->
  bq_map_correct bq_map ->
  aq_map_correct aq_map ->
  (0 < e0)%Z ->
  (0 <= w)%Z ->
match depth_first_verify_aux_three_fuel_gen m nodes nodes0 cnodes0 w e0 fuel1 fuel2 a_map b_map g_map bq_map aq_map with
  | Some (a_map, b_map, g_map, bq_map, aq_map,nodes1) => a_map_correct a_map /\ b_map_correct b_map /\
  g_map_correct g_map /\
  bq_map_correct bq_map /\
  aq_map_correct aq_map /\
  depth_first_verify_aux_no_mem_three_fuel_gen m nodes nodes0 cnodes0 w e0 fuel1 fuel2 = Some nodes1
  | None =>
    depth_first_verify_aux_no_mem_three_fuel_gen m nodes nodes0 cnodes0 w e0 fuel1 fuel2 = None
end.

  revert fuel2 m nodes nodes0 cnodes0 w e0 a_map b_map g_map bq_map aq_map.
  induction fuel1; [auto|]; intros.

  destruct (depth_first_verify_aux_three_fuel_gen m nodes nodes0 cnodes0 w e0 0 fuel2 a_map b_map g_map bq_map aq_map) eqn:E.
  split_pairs.

  cbn [depth_first_verify_aux_no_mem_three_fuel_gen depth_first_verify_aux_three_fuel_gen] in *; auto; split_pairs.
  inversion E.

  cbn [depth_first_verify_aux_no_mem_three_fuel_gen depth_first_verify_aux_three_fuel_gen].
  reflexivity.

  destruct (depth_first_verify_aux_three_fuel_gen m nodes nodes0 cnodes0 w e0 (S fuel1) fuel2 a_map b_map g_map bq_map aq_map) eqn:E.
  split_pairs.
  cbn [depth_first_verify_aux_no_mem_three_fuel_gen depth_first_verify_aux_three_fuel_gen] in *.

  split_pairs. memt.
  split_pairs.

  setoid_rewrite H10 in E.

  destruct_ifs; try reflexivity; try tauto.
  inversion E.
  inversion E.
  subst.

  tauto.

  assert (H' := H4).
  revert E. revert H'.

  generalize e0 at 1 3 5.

  revert nodes.

  revert H9 H7 H1 H2 H8.
  revert t5 t6 g_map bq_map t7.

  generalize fuel2 at 1 3.

  induction fuel2; [auto|]; intros.

  inversion E.

  split_pairs. memt. setoid_rewrite H18 in E.

  destruct_ifs; try reflexivity.
  inversion E. subst. tauto.

  assert
    (forall fuel10,
      match
        (
          fix verify_children (cnodes : Z) (a_map b_map : ZMap.t Q) (g_map bq_map aq_map : ZZMap.t Q) (fuel4 : nat) {struct fuel4} :
            option (ZMap.t Q * ZMap.t Q * ZZMap.t Q * ZZMap.t Q * ZZMap.t Q * Z) :=
            match fuel4 with
            | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes)
            | S fuel5 =>
              match
                depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
                                                      (e1 + w) e0 fuel1 fuel0 a_map b_map g_map bq_map aq_map
              with
              | Some (a_map0, b_map0, g_map0, bq_map0, aq_map0, nodes) =>
                verify_children (nodes + cnodes)%Z a_map0 b_map0 g_map0 bq_map0 aq_map0 fuel5
              | None => None
              end
            end) cnodes0 t8 t10 t11 t12 t9 fuel10
      with
      | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) =>
        a_map_correct a_map /\
        b_map_correct b_map /\
        g_map_correct g_map /\
        bq_map_correct bq_map /\
        aq_map_correct aq_map /\
    (fix verify_children (cnodes : Z) (fuel4 : nat) {struct fuel4} : option Z :=
       match fuel4 with
       | 0%nat => Some cnodes
       | S fuel5 =>
           match
             depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
               (e1 + w) e0 fuel1 fuel0
           with
           | Some nodes1 => verify_children (nodes1 + cnodes)%Z fuel5
           | None => None
           end
       end) cnodes0 fuel10  = Some nodes
      | None => (fix verify_children (cnodes : Z) (fuel4 : nat) {struct fuel4} : option Z :=
                  match fuel4 with
                  | 0%nat => Some cnodes
                  | S fuel5 =>
                    match
                      depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
                                                                   (e1 + w) e0 fuel1 fuel0
                    with
                    | Some nodes1 => verify_children (nodes1 + cnodes)%Z fuel5
                    | None => None
                    end
                  end) cnodes0 fuel10 = None
      end).

  clear E.
  clear IHfuel2. intros.

  generalize cnodes0 at 2 4 6.
  revert cnodes0.

  revert H17 H15 H13 H14 H16.
  revert t8 t10 t11 t12 t9.
  induction fuel10; intros.
  tauto.

  assert (IH := IHfuel1).

  specialize (IH fuel0 (mmult (scaledM e1 (Z.of_nat (2 * fuel10 + 1))) m) nodes0 nodes0 cnodes0
                 (e1 + w)%Z e0 t8 t10 t11 t12 t9 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(lia)).


  destruct ( depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel10 + 1))) m) nodes0 nodes0 cnodes0
                                                   (e1 + w) e0 fuel1 fuel0 t8 t10 t11 t12 t9) eqn:E2.
  split_pairs.

  rewrite H30.

  specialize (IHfuel10 t16 t17 t15 t14 t13 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) cnodes0 (z0 + cnodes1)%Z).

  destruct (
      (fix verify_children (cnodes : Z) (a_map0 b_map0 : ZMap.t Q) (g_map0 bq_map0 aq_map0 : ZZMap.t Q) (fuel4 : nat) {struct fuel4} :
         option (ZMap.t Q * ZMap.t Q * ZZMap.t Q * ZZMap.t Q * ZZMap.t Q * Z) :=
       match fuel4 with
       | 0%nat => Some (a_map0, b_map0, g_map0, bq_map0, aq_map0, cnodes)
       | S fuel5 =>
           match
             depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
               (e1 + w) e0 fuel1 fuel0 a_map0 b_map0 g_map0 bq_map0 aq_map0
           with
           | Some (a_map1, b_map1, g_map1, bq_map1, aq_map1, nodes1) =>
               verify_children (nodes1 + cnodes)%Z a_map1 b_map1 g_map1 bq_map1 aq_map1 fuel5
           | None => None
           end
       end) (z0 + cnodes1)%Z t16 t17 t15 t14 t13 fuel10) eqn:E4.

  split_pairs.

  tauto.
  tauto.

  rewrite IH. reflexivity.

  specialize (H20 (Z.to_nat (2 ^ e1))).

  destruct ((fix verify_children
             (cnodes : Z) (a_map b_map : ZMap.t Q) (g_map bq_map aq_map : ZZMap.t Q) (fuel4 : nat) {struct fuel4} :
               option (ZMap.t Q * ZMap.t Q * ZZMap.t Q * ZZMap.t Q * ZZMap.t Q * Z) :=
             match fuel4 with
             | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes)
             | S fuel5 =>
                 match
                   depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
                     (e1 + w) e0 fuel1 fuel0 a_map b_map g_map bq_map aq_map
                 with
                 | Some (a_map0, b_map0, g_map0, bq_map0, aq_map0, nodes) =>
                     verify_children (nodes + cnodes)%Z a_map0 b_map0 g_map0 bq_map0 aq_map0 fuel5
                 | None => None
                 end
             end) cnodes0 t8 t10 t11 t12 t9 (Z.to_nat (2 ^ e1))).

  split_pairs.
  rewrite H30.

  specialize (IHfuel2 _ t16 t17 t15 t14 t13 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) (z0 + nodes)%Z (e1 + 1)%Z ltac:(lia) E).
  apply IHfuel2.

  inversion E.

  (** Second case *)

  cbn [depth_first_verify_aux_no_mem_three_fuel_gen depth_first_verify_aux_three_fuel_gen] in *.
  split_pairs. memt.

  setoid_rewrite H10 in E.

  destruct_ifs; try reflexivity; try tauto.
  inversion E.

  assert (H' := H4).
  revert E. revert H'.

  generalize e0 at 1 3 5.

  revert nodes.

  revert H1 H2 H7 H8 H9.
  revert t0 t1 g_map bq_map t2.

  generalize fuel2 at 1 3.

  induction fuel2; [auto|]; intros.

  split_pairs. memt. setoid_rewrite H18 in E.

  destruct_ifs; try reflexivity.
  inversion E.

  revert E.
  intros.

  assert
    (forall fuel10,

      match
        (
          fix verify_children (cnodes : Z) (a_map b_map : ZMap.t Q) (g_map bq_map aq_map : ZZMap.t Q) (fuel4 : nat) {struct fuel4} :
            option (ZMap.t Q * ZMap.t Q * ZZMap.t Q * ZZMap.t Q * ZZMap.t Q * Z) :=
            match fuel4 with
            | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes)
            | S fuel5 =>
              match
                depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
                                                      (e1 + w) e0 fuel1 fuel0 a_map b_map g_map bq_map aq_map
              with
              | Some (a_map0, b_map0, g_map0, bq_map0, aq_map0, nodes) =>
                verify_children (nodes + cnodes)%Z a_map0 b_map0 g_map0 bq_map0 aq_map0 fuel5
              | None => None
              end
            end) cnodes0 t3 t5 t6 t7 t4 fuel10
      with
      | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) =>
        a_map_correct a_map /\
        b_map_correct b_map /\
        g_map_correct g_map /\
        bq_map_correct bq_map /\
        aq_map_correct aq_map /\
    (fix verify_children (cnodes : Z) (fuel4 : nat) {struct fuel4} : option Z :=
       match fuel4 with
       | 0%nat => Some cnodes
       | S fuel5 =>
           match
             depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
               (e1 + w) e0 fuel1 fuel0
           with
           | Some nodes1 => verify_children (nodes1 + cnodes)%Z fuel5
           | None => None
           end
       end) cnodes0 fuel10  = Some nodes
      | None => (fix verify_children (cnodes : Z) (fuel4 : nat) {struct fuel4} : option Z :=
                  match fuel4 with
                  | 0%nat => Some cnodes
                  | S fuel5 =>
                    match
                      depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
                                                                   (e1 + w) e0 fuel1 fuel0
                    with
                    | Some nodes1 => verify_children (nodes1 + cnodes)%Z fuel5
                    | None => None
                    end
                  end) cnodes0 fuel10 = None
      end).

  clear E.
  clear IHfuel2. intros.


  generalize cnodes0 at 2 4 6.
  revert cnodes0.

  revert H13 H14 H15 H16 H17.
  revert t3 t5 t6 t7 t4.
  induction fuel10; intros.
  tauto.

  assert (IH := IHfuel1).

  specialize (IH fuel0 (mmult (scaledM e1 (Z.of_nat (2 * fuel10 + 1))) m) nodes0 nodes0 cnodes0
                 (e1 + w)%Z e0 t3 t5 t6 t7 t4 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(lia)).

  destruct ( depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel10 + 1))) m) nodes0 nodes0 cnodes0
                                                   (e1 + w) e0 fuel1 fuel0 t3 t5 t6 t7 t4) eqn:E2.
  split_pairs.

  rewrite H30.

  specialize (IHfuel10 t11 t12 t10 t9 t8 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) cnodes0 (z + cnodes1)%Z).

  destruct (
      (fix verify_children (cnodes : Z) (a_map0 b_map0 : ZMap.t Q) (g_map0 bq_map0 aq_map0 : ZZMap.t Q) (fuel4 : nat) {struct fuel4} :
         option (ZMap.t Q * ZMap.t Q * ZZMap.t Q * ZZMap.t Q * ZZMap.t Q * Z) :=
       match fuel4 with
       | 0%nat => Some (a_map0, b_map0, g_map0, bq_map0, aq_map0, cnodes)
       | S fuel5 =>
           match
             depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
               (e1 + w) e0 fuel1 fuel2 a_map0 b_map0 g_map0 bq_map0 aq_map0
           with
           | Some (a_map1, b_map1, g_map1, bq_map1, aq_map1, nodes1) =>
               verify_children (nodes1 + cnodes)%Z a_map1 b_map1 g_map1 bq_map1 aq_map1 fuel5
           | None => None
           end
       end) (z + cnodes1)%Z t11 t12 t10 t9 t8 fuel0) eqn:E4.

  split_pairs.

  tauto.
  tauto.

  rewrite IH. reflexivity.

  specialize (H20 (Z.to_nat (2 ^ e1))).
  destruct ((fix verify_children
             (cnodes : Z) (a_map b_map : ZMap.t Q) (g_map bq_map aq_map : ZZMap.t Q) (fuel4 : nat) {struct fuel4} :
               option (ZMap.t Q * ZMap.t Q * ZZMap.t Q * ZZMap.t Q * ZZMap.t Q * Z) :=
             match fuel4 with
             | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes)
             | S fuel5 =>
                 match
                   depth_first_verify_aux_three_fuel_gen (mmult (scaledM e1 (Z.of_nat (2 * fuel5 + 1))) m) nodes0 nodes0 cnodes0
                     (e1 + w) e0 fuel1 fuel0 a_map b_map g_map bq_map aq_map
                 with
                 | Some (a_map0, b_map0, g_map0, bq_map0, aq_map0, nodes) =>
                     verify_children (nodes + cnodes)%Z a_map0 b_map0 g_map0 bq_map0 aq_map0 fuel5
                 | None => None
                 end
             end) cnodes0 t3 t5 t6 t7 t4 (Z.to_nat (2 ^ e1))).

  split_pairs.
  rewrite H30.

  specialize (IHfuel2 _ t11 t12 t10 t9 t8 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) (z + nodes)%Z (e1 + 1)%Z ltac:(lia) E).
  apply IHfuel2.
  rewrite H20. reflexivity. Qed.

Definition depth_first_verify :=
  match depth_first_verify_aux_three_fuel_gen I 1 1 0 0 1 10000 10000 init_amap init_bmap init_gmap init_bqmap init_aqmap with None => None | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) => Some nodes end.

Axiom comp1_theorem :
  depth_first_verify = Some 3787975117%Z.

Require Import Coq.extraction.ExtrOcamlZBigInt.

Extraction "mem" depth_first_verify.
