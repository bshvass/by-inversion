Require Import Bool ZArith micromega.Lia.

Require Import MatrixZ BigOp Zlemmas.

Import Z.

Local Open Scope mat_scope.
Local Open Scope vec_scope.
Local Open Scope Z.

Local Coercion of_nat : nat >-> Z.

Definition divstep d f g :=
  if (0 <? d) && odd g
  then (1 - d, g, (g - f) / 2)
  else (1 + d, f, (g + (g mod 2) * f) / 2 ).

Definition divstep2 m d g v r :=
  if (0 <? d) && Z.odd g
  then (2 * r mod m, (r - v) mod m)
  else (2 * v mod m, (r + (g mod 2) * v) mod m).

Definition divstep_full d f g v r :=
  if (0 <? d) && Z.odd g
  then (1 - d, g, (g - f) / 2, 2 * r, r - v)
  else (1 + d, f, (g + (g mod 2) * f) / 2, 2 * v, r + (g mod 2) * v).

Lemma divstep_divstep_full d f g v r :
  let '(d1, f1, g1, _, _) := divstep_full d f g v r in
  divstep d f g = (d1, f1, g1).
Proof. unfold divstep_full, divstep; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

Definition divstep_full2 m d f g v r :=
  if (0 <? d) && Z.odd g
  then (1 - d, g, (g - f) / 2, 2 * r mod m, (r - v) mod m)
  else (1 + d, f, (g + (g mod 2) * f) / 2, 2 * v mod m, (r + (g mod 2) * v) mod m).

Lemma divstep_divstep_full2 m d f g v r :
  let '(d1, f1, g1, _, _) := divstep_full2 m d f g v r in
  divstep d f g = (d1, f1, g1).
Proof. unfold divstep_full2, divstep; destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

Fixpoint divstep_iter d f g n :=
  match n with
  | 0%nat => (d, f, g)
  | S m => let '(d, f, g) := divstep_iter d f g m in divstep d f g
  end.

Fixpoint divstep_full_iter d f g v r n :=
  match n with
  | 0%nat => (d, f, g, v, r)
  | S n => let '(d, f, g, v, r) := divstep_full_iter d f g v r n in divstep_full d f g v r
  end.

Fixpoint divstep_full2_iter m d f g v r n :=
  match n with
  | 0%nat => (d, f, g, v, r)
  | S n => let '(d, f, g, v, r) := divstep_full2_iter m d f g v r n in divstep_full2 m d f g v r
  end.

Lemma divstep_divstep_full_iter d f g v r n :
  let '(dn, fn, gn, _, _) := divstep_full_iter d f g v r n in
  divstep_iter d f g n = (dn, fn, gn).
Proof. induction n; simpl. reflexivity.
       destruct (divstep_full_iter d f g v r n) as [[[[? ?] ? ]? ]?].
       rewrite IHn; apply divstep_divstep_full. Qed.

Lemma divstep_divstep_full2_iter m d f g v r n :
  let '(dn, fn, gn, _, _) := divstep_full2_iter m d f g v r n in
  divstep_iter d f g n = (dn, fn, gn).
Proof. induction n; simpl. reflexivity.
       destruct (divstep_full2_iter m d f g v r n) as [[[[? ?] ? ]? ]?].
       rewrite IHn; apply divstep_divstep_full2. Qed.

Definition fn d f g n := let '(_, fn, _) := divstep_iter d f g n in fn.
Definition gn d f g n := let '(_, _, gn) := divstep_iter d f g n in gn.
Definition dn d f g n := let '(dn, _, _) := divstep_iter d f g n in dn.

Definition Tmat (d f g : Z) :=
  if (0 <? d) && (odd g)
  then
    [ 0 , 2 ; -1 , 1 ]
  else
    [ 2 , 0 ; g mod 2 , 1 ].

Definition Smat (d f g : Z) :=
  let b := (0 <? d) && (odd g) in
  if b
  then
    [ 1 , 0 ; 1 , -1 ]
  else
    [ 1 , 0 ; 1 , 1 ].

Definition Tn d f g n :=
  let '(dn, fn, gn) :=
      divstep_iter d f g n in
  Tmat dn fn gn.

Definition Sn d f g n :=
  let '(dn, fn, gn) :=
      divstep_iter d f g n in
  Smat dn fn gn.

Lemma Tn_0 d f g : Tn d f g 0 = Tmat d f g.
Proof. unfold Tn. reflexivity. Qed.

(* Lemma divstep_iter0 d f g n : *)
(*   divstep_iter d f g 0 = let '(d', f', g') := divstep_iter d f g n in divstep d' f' g'. *)
(* Proof. reflexivity. Qed. *)

Lemma divstep_iter_S d f g n :
  divstep_iter d f g (S n) = let '(d', f', g') := divstep_iter d f g n in divstep d' f' g'.
Proof. reflexivity. Qed.

Lemma divstep_iter_S' d f g n :
  divstep_iter d f g (S n) = let '(d', f', g') := divstep d f g in divstep_iter d' f' g' n.
Proof.
  induction n.
  - now simpl; destruct (divstep d f g) as [[d' f'] g'].
  - rewrite divstep_iter_S, IHn.
    destruct (divstep d f g) as [[d' f'] g']. now rewrite divstep_iter_S. Qed.

Lemma divstep_iter_add d f g n m :
  divstep_iter d f g (n + m) =
  let '(d', f', g') := divstep_iter d f g n in
  divstep_iter d' f' g' m.
Proof. induction m.
       - now rewrite Nat.add_0_r; destruct (divstep_iter d f g n) as [[? ?] ?].
       - rewrite Nat.add_succ_r; simpl; rewrite IHm.
         now destruct (divstep_iter d f g n) as [[? ?] ?]. Qed.

Lemma divstep_iter_0 d f g d' f' n k :
  divstep_iter d f g n = (d', f', 0) -> divstep_iter d f g (n + k) = (d' + k, f', 0).
Proof.
  induction k; intros.
  - rewrite Nat.add_0_r, add_0_r; assumption.
  - replace (n + S k)%nat with (S (n + k)) by lia. simpl.
    rewrite IHk by assumption.
    unfold divstep. assert (odd 0 = false) by reflexivity. rewrite H0.
    rewrite andb_false_r. rewrite mod_0_l.
    apply f_equal2; [apply f_equal2|]. lia. lia. reflexivity. lia. Qed.

Lemma divstep_iter_0' d f g d' f' n m
      (Hnlem : (n <= m)%nat) :
  divstep_iter d f g n = (d', f', 0) -> exists d'' f'', divstep_iter d f g m = (d'', f'', 0).
Proof.
  set (k := (m - n)%nat). intros H.
  apply divstep_iter_0 with (k := k) in H.
  replace (n + k)%nat with m in H by lia. eauto. Qed.

Lemma fn_odd d f g n : odd f = true -> odd (fn d f g n) = true.
Proof.
  intros. unfold fn. induction n.
  - assumption.
  - rewrite divstep_iter_S. destruct (divstep_iter d f g n) as [[dn fn] gn].
    unfold divstep. destruct (0 <? dn); destruct (odd gn) eqn:gnodd; simpl; assumption. Qed.

Lemma Tn_transition d f g n (fodd : odd f = true) :
    2 **v [ fn d f g (S n) ; gn d f g (S n) ] = ((Tn d f g n) *v [ fn d f g n ; gn d f g n ]).
Proof.
  pose proof fn_odd d f g n fodd as fnodd. auto_mat.
  unfold Tn, fn, gn, Tmat in *. rewrite divstep_iter_S. unfold divstep.
  destruct (divstep_iter d f g n) as [[dn fn] gn]. rewrite Zmod_odd.
  destruct (0 <? dn); destruct (odd gn) eqn:gnodd; cbn -[Z.mul]; apply f_equal2;
    rewrite <- ?Z_div_exact_full_2; rewrite ?Zmod_odd, ?odd_sub, ?odd_add, ?odd_mul, ?fnodd, ?gnodd; try lia; reflexivity. Qed.

Lemma Sn_transition d f g n :
    [ 1 ; dn d f g (S n) ] = (Sn d f g n) *v [ 1 ; dn d f g n ].
Proof.
  unfold Sn, dn, Smat in *. rewrite divstep_iter_S. unfold divstep.
  destruct (divstep_iter d f g n) as [[dn fn] gn].
  destruct ((0 <? dn) && odd gn); auto_mat. Qed.

Lemma divstep_full_spec d f g :
  let '(d1, f1, g1, v1, r1) := divstep_full d f g 0 1 in
  exists u1 q1, [ u1, v1; q1, r1 ] = Tmat d f g.
Proof.
  unfold divstep_full, Tmat.
  destruct ((0 <? d) && odd g); do 2 eexists; repeat apply f_equal2; try lia; reflexivity. Qed.

Ltac pair_eq :=
  repeat match goal with
         | [ |- (_, _) = (_, _)] => apply f_equal2
         end.

Lemma divstep_full_iter_spec d f g m :
  let '(d1, f1, g1, v1, r1) := divstep_full_iter d f g 0 1 m in
  exists u1 q1, [ u1, v1; q1, r1 ] = big_mmult_rev 0%nat m (fun i : nat => Tn d f g i).
Proof. induction m.
       - rewrite big_op_rev_nil by lia. do 2 eexists; repeat apply f_equal2; reflexivity.
       - simpl.
         rewrite big_op_rev_S_l.
         pose proof divstep_divstep_full_iter d f g 0 1 m.

         destruct (divstep_full_iter d f g 0 1 m) as [[[[dm fm] gm] vm] rm] eqn:full_iter.
         pose proof divstep_divstep_full dm fm gm vm rm.

         destruct IHm as [um [qm]]. rewrite <- H1.
         unfold Tn.
         destruct (divstep_full dm fm gm vm rm) as [[[[dSm fSm] gSm] vSm] rSm] eqn:full.
         rewrite H.

         unfold Tmat.
         unfold divstep in H0.
         unfold divstep_full in full.

         Arguments sub : simpl never.
         Arguments add : simpl never.
         Arguments mul : simpl never.
         unfold mmult.

         destruct ((0 <? dm) && odd gm) eqn:E.
         inversion full; inversion H0.
         do 2 eexists; pair_eq; try reflexivity; lia.

         destruct (mod2_dec gm). rewrite e in *.
         inversion full; inversion H0.
         do 2 eexists; pair_eq; try reflexivity; lia.

         rewrite e in *.
         inversion full; inversion H0.
         do 2 eexists; pair_eq; try reflexivity; lia. lia. Qed.
