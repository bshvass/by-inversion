Require Import ZArith.
From stdpp Require Import decidable.
Require Import micromega.Lia.
From BY Require Import Matrix Impl Zlemmas.
From BY.Hierarchy Require Import Definitions BigOp.

From stdpp Require Import numbers.

Local Open Scope Z_scope.

Local Open Scope Z.
Global Instance Z_le_dec: RelDecision Z.le := Z_le_dec.
Global Instance Z_lt_dec: RelDecision Z.lt := Z_lt_dec.
Global Instance Z_eq_dec: RelDecision Z.eq := Z.eq_dec.

Local Coercion Z.of_nat : nat >-> Z.

Definition divstep '(d, f, g) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2)
       else (1 + d, f, (g + f) / 2 )
  else (1 + d, f, g / 2 ).

Definition divstep_vr '(d, f, g, v, r) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2, 2 * r, r - v)
       else (1 + d, f, (g + f) / 2, 2 * v, r + v)
  else (1 + d, f, g / 2, 2 * v, r).

Definition divstep_vr_mod m '(d, f, g, v, r) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2, (2 * r) mod m, (r - v) mod m)
       else (1 + d, f, (g + f) / 2, (2 * v) mod m, (r + v) mod m)
  else (1 + d, f, g / 2, (2 * v) mod m, r mod m).

Definition divstep_uvqr '(d, f, g, u, v, q, r) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2, 2 * q, 2 * r, q - u, r - v)
       else (1 + d, f, (g + f) / 2, 2 * u, 2 * v, q + u, r + v)
  else (1 + d, f, g / 2, 2 * u, 2 * v, q, r).

Definition jump_divstep n mw m '(d, f, g, v, r) :=
  let '(d1, f1, g1, u1, v1, q1, r1) := Nat.iter n divstep_uvqr (d, f mod 2 ^ mw, g mod 2 ^ mw, 1, 0, 0, 1) in
  let f1' := (u1 * f + v1 * g) / 2 ^ n in
  let g1' := (q1 * f + r1 * g) / 2 ^ n in
  let v1' := (u1 * v + v1 * r) mod m in
  let r1' := (q1 * v + r1 * r) mod m in
  (d1, f1', g1', v1', r1').

Lemma divstep_vr_divstep d f g v r :
  let '(d1, f1, g1, _, _) := divstep_vr (d, f, g, v, r) in
  divstep (d, f, g) = (d1, f1, g1).
Proof. unfold divstep, divstep_vr; destruct (0 <? _), (Z.odd _); reflexivity. Qed.

Lemma iter_divstep_vr_iter_divstep d f g v r n :
  let '(dn, fn, gn, _, _) := Nat.iter n divstep_vr (d, f, g, v, r) in
  Nat.iter n divstep (d, f, g) = (dn, fn, gn).
Proof.
  induction n; simpl. reflexivity.
  destruct (Nat.iter _ _ _) as [[[[? ?] ? ]? ]?].
  rewrite IHn. apply divstep_vr_divstep.
Qed.

Lemma iter_divstep_vr_mod_iter_divstep_uvqr m d f g u2 v1 v2 q2 r1 r2 n :
  let '(d1,f1,g1,_,_) :=
      Nat.iter n (divstep_vr_mod m) (d, f, g, v1, r1) in
  (d1,f1,g1)
  = let '(d2,f2,g2,_,_,_,_) := Nat.iter n divstep_uvqr (d, f, g, u2, v2, q2, r2) in
    (d2,f2,g2).
Proof.
  induction n; simpl.
  - reflexivity.
  - destruct (Nat.iter _ _ _) as [[[[?]?]?]?].
    destruct (Nat.iter _ _ _) as [[[[[[?]?]?]?]?]?].
    rewrite IHn. unfold divstep_vr_mod, divstep_uvqr.
    destruct (0 <? _), (Z.odd _); reflexivity.
Qed.

Lemma iter_divstep_f_odd d f g n
  (fodd : Z.odd f = true) :
  let '(_,f,_) := Nat.iter n divstep (d, f, g) in Z.odd f = true.
Proof.
  induction n; simpl.
  - assumption.
  - unfold divstep.
    destruct (Nat.iter _ _ _) as [[d1 f1] g1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption.
Qed.

Lemma iter_divstep_vr_mod_f_odd m d f g v r n
  (fodd : Z.odd f = true) :
  let '(_,f,_,_,_) := Nat.iter n (divstep_vr_mod m) (d, f, g, v, r) in Z.odd f = true.
Proof.
  induction n; simpl.
  - assumption.
  - unfold divstep_vr_mod.
    destruct (Nat.iter _ _ _) as [[[[d1 f1]g1]v1]r1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption.
Qed.

Lemma iter_divstep_uvqr_f_odd d f g u v q r n
  (fodd : Z.odd f = true) :
  let '(_,f,_,_,_,_,_) := Nat.iter n divstep_uvqr (d, f, g, u, v, q, r) in Z.odd f = true.
Proof.
  induction n; simpl.
  - assumption.
  - unfold divstep_uvqr.
    destruct (Nat.iter _ _ _) as [[[[[[d1 f1]g1]u1]v1]q1]r1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption.
Qed.

Lemma odd_mod2m m a (Hm : 0 < m) : Z.odd (a mod 2 ^ m) = Z.odd a.
Proof.
  rewrite Zdiv.Zmod_eq_full, Z.odd_sub, Z.odd_mul, Z.odd_pow by (lia || apply Z.pow_nonzero; lia).
  now rewrite andb_false_r, xorb_false_r.
Qed.

Lemma mod_div : forall a b c : Z, 0 <= c -> (a / b) mod c = a mod (c * b) / b.
Proof.
  intros.
  destruct (Z.eq_dec c 0) as [c_eq|?];
    destruct (Z.eq_dec b 0) as [b_eq|?];subst;
    rewrite ?Z.mul_0_l, ?Z.mul_0_r, ?Zmod_0_r, ?Zdiv_0_r; try reflexivity.
  rewrite !Z.mod_eq by lia.
  apply Z.div_unique with (r:=a mod b).
  pose proof Z.mod_pos_bound a b. pose proof Z.mod_neg_bound a b. lia.
  rewrite !Z.mod_eq, Z.div_div, (Z.mul_comm c) by lia. ring.
Qed.

Lemma mod_pow_same_base_smaller a b n m :
  0 <= m <= n -> 0 < b ->
  (a mod (b^n)) mod (b^m) = a mod b^m.
Proof.
  intros. replace n with (m+(n-m)) by lia.
  rewrite Z.pow_add_r, Z.rem_mul_r by auto with zarith.
  rewrite Zplus_mod_idemp_l.
  rewrite <- Zplus_mod_idemp_r.
  rewrite <- Zmult_mod_idemp_l.
  rewrite Z_mod_same_full.
  rewrite Z.mul_0_l.
  rewrite Z.mod_0_l.
  rewrite Z.add_0_r.  reflexivity. apply Z.pow_nonzero. lia. lia.
Qed.

Lemma divstep_uvqr_important_bits d f f0 g g0 u v q r n k
      (Hk : (0 <= n < k)%nat)
      (fodd : Z.odd f = true)
      (fmod : f mod 2 ^ Z.of_nat k = f0 mod 2 ^ Z.of_nat k)
      (gmod : g mod 2 ^ Z.of_nat k = g0 mod 2 ^ Z.of_nat k) :
  let '(d1,f1,g1,u1,v1,q1,r1) := Nat.iter n divstep_uvqr (d, f,  g,  u, v, q, r) in
  let '(d2,f2,g2,u2,v2,q2,r2) := Nat.iter n divstep_uvqr (d, f0, g0, u, v, q, r) in
  g1 mod 2 ^ (k - n) = g2 mod 2 ^ (k - n) /\
  f1 mod 2 ^ (k - n) = f2 mod 2 ^ (k - n) /\
  d1 = d2 /\
  (u1,v1,q1,r1) = (u2,v2,q2,r2).
Proof.
  induction n.
  - cbn in *. rewrite !Z.sub_0_r. repeat split; assumption.
  - rewrite !Nat.iter_succ.
    assert (f0_odd : Z.odd f0 = true).
    { rewrite <- odd_mod2m with (m:=k), <- fmod, odd_mod2m; try assumption; lia. }

    pose proof iter_divstep_uvqr_f_odd d f g u v q r n fodd.
    pose proof iter_divstep_uvqr_f_odd d f0 g0 u v q r n f0_odd.

    destruct (Nat.iter _ _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1].
    destruct (Nat.iter _ _ _) as [[[[[[d2 f2] g2] u2] v2] q2] r2].

    assert (g1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = g2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\
            f1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = f2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\
            d1 = d2 /\ (u1, v1, q1, r1) = (u2, v2, q2, r2)) by (apply IHn; lia).

    destruct H1 as [H2 [H3 [H4 H5]]].

    assert (Z.odd g1 = Z.odd g2 /\ d1 = d2) as [].
    { rewrite <- odd_mod2m with (m:=k - n), H2, odd_mod2m by lia; split; reflexivity || lia. }

    unfold divstep_uvqr.
    inversion H5. subst. rewrite H1.

    destruct (0 <? d2); destruct (Z.odd g2) eqn:odd; cbn -[Z.mul Z.add Z.div Z.of_nat].
    + split; [|split;[|split]]; try lia; try congruence.
      * rewrite !mod_div by lia. f_equal.
        replace 2 with (2 ^ 1) at 2 4 by reflexivity. rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat k - S n + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        rewrite <- Zminus_mod_idemp_r, <- Zminus_mod_idemp_l, H2, H3, Zminus_mod_idemp_r, Zminus_mod_idemp_l.
        reflexivity.
      * rewrite <- mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H2, mod_pow_same_base_smaller; lia.
    + split; [|split;[|split]]; try lia; try congruence.
      * rewrite !mod_div by lia. f_equal.
        replace 2 with (2 ^ 1) at 2 4 by reflexivity. rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat k - S n + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        apply H2.
      * rewrite <- mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H3, mod_pow_same_base_smaller; lia.
    + split; [|split;[|split]]; try lia; try congruence.
      * rewrite !mod_div by lia. f_equal.
        replace 2 with (2 ^ 1) at 2 4 by reflexivity. rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat k - S n + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        rewrite <- Zplus_mod_idemp_r, <- Zplus_mod_idemp_l, H2, H3, Zplus_mod_idemp_r, Zplus_mod_idemp_l.
        reflexivity.
      * rewrite <- mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H3, mod_pow_same_base_smaller; lia.
    + split; [|split;[|split]]; try lia; try congruence.
      * rewrite !mod_div by lia. f_equal.
        replace 2 with (2 ^ 1) at 2 4 by reflexivity. rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat k - S n + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        apply H2.
      * rewrite <- mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H3, mod_pow_same_base_smaller; lia.
Qed.

Lemma mul_div_eq' : (forall a m, m > 0 -> (a / m) * m = (a - a mod m))%Z.
Proof.
  intros a m H.
  rewrite (Z_div_mod_eq a m) at 2 by auto.
  ring.
Qed.
Lemma mul_div_eq : forall a m, m > 0 -> m * (a / m) = (a - a mod m).
Proof.
  intros a m H.
  rewrite (Z_div_mod_eq a m) at 2 by auto.
  ring.
Qed.

Lemma jump_divstep_lemma m d f g v r n
      (fodd : Z.odd f = true)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m)
  :
    let '(d1, f1, g1, v1, r1) := Nat.iter n (divstep_vr_mod m) (d, f, g, v, r) in
    (d1,2 ^ n * f1,2 ^ n * g1,v1 ,r1)
  = let '(d1', f1', g1', u1', v1', q1', r1') := Nat.iter n divstep_uvqr (d, f, g, 1, 0, 0, 1) in
    (d1', (u1' * f + v1' * g), (q1' * f + r1' * g), (u1' * v + v1' * r) mod m, (q1' * v + r1' * r) mod m).
Proof.
  induction n.
  - cbn -[Z.add Z.mul].
    repeat match goal with
           | [ |- (_, _) = (_, _) ] => apply f_equal2; rewrite ?Z.div_1_r, ?Z.mod_small by lia; try lia
           end.
  - rewrite !Nat.iter_succ.
    pose proof iter_divstep_vr_mod_iter_divstep_uvqr m d f g 1 v 0 0 r 1 n.
    pose proof iter_divstep_vr_mod_f_odd m d f g v r n fodd as fodd1.
    destruct (Nat.iter _ _ _) as [[[[d2 f2] g2] v2] r2].
    destruct (Nat.iter _ _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1].

    replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1) by lia. rewrite Z.pow_add_r by lia.
    replace (2 ^ 1) with 2 by reflexivity.
    unfold divstep_vr_mod, divstep_uvqr.
    inversion H; inversion IHn; subst.
    destruct (0 <? d1); destruct (Z.odd g1) eqn:godd; cbn -[Z.mul Z.add Z.div Z.of_nat];
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end; try lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, mul_div_eq, Zmod_odd, Z.odd_sub, godd, fodd1; cbn; lia.
    rewrite Zmult_mod_idemp_r. f_equal; lia.
    rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l. f_equal; lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, mul_div_eq, !Zmod_odd, godd, Z.sub_0_r, <- H6; lia.
    rewrite Zmult_mod_idemp_r. f_equal; lia.
    rewrite Z.mod_mod by lia. f_equal; lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, mul_div_eq, !Zmod_odd, Z.odd_add, godd, fodd1, Z.sub_0_r; lia.
    rewrite Zmult_mod_idemp_r. f_equal; lia.
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l. f_equal; lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, mul_div_eq, Zmod_odd, godd, <- H6; lia.
    rewrite Zmult_mod_idemp_r. f_equal; lia.
    rewrite Z.mod_mod by lia. f_equal; lia.
Qed.

Lemma div_mul' : forall a b : Z, b <> 0 -> (b * a) / b = a.
  Proof. intros. rewrite Z.mul_comm. apply Z.div_mul; auto. Qed.

Lemma jump_divstep_full m d f f0 g g0 v r n
      (fodd : Z.odd f = true)
      (Hm : 1 < m)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m)
      (Hf : f mod 2 ^ (Z.of_nat (S n)) = f0 mod 2 ^ (Z.of_nat (S n)))
      (Hg : g mod 2 ^ (Z.of_nat (S n)) = g0 mod 2 ^ (Z.of_nat (S n)))
  :
  Nat.iter n (divstep_vr_mod m) (d, f, g, v, r)
  = let '(d1, f1, g1, u1, v1, q1, r1) := Nat.iter n divstep_uvqr (d, f0, g0, 1, 0, 0, 1) in
    let f1' := (u1 * f + v1 * g) / 2 ^ n in
    let g1' := (q1 * f + r1 * g) / 2 ^ n in
    let v1' := (u1 * v + v1 * r) mod m in
    let r1' := (q1 * v + r1 * r) mod m in
    (d1, f1', g1', v1', r1').
Proof.
  assert (f0odd : Z.odd f0 = true).
  { rewrite <- odd_mod2m with (m:=S n), <- Hf, odd_mod2m; try assumption; lia. }

  pose proof jump_divstep_lemma m d f g v r n fodd Hv Hr.
  pose proof divstep_uvqr_important_bits d f f0 g g0 1 0 0 1 n (S n) ltac:(lia) fodd Hf Hg.

  destruct (Nat.iter _ _ _) as [[[[d1 f1] g1] v1] r1].
  destruct (Nat.iter _ _ _) as [[[[[[d1' f1'] g1'] u1'] v1'] q1'] r1'].
  destruct (Nat.iter _ _ _) as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''].
  destruct H0 as [H1 [H2 [H3 H4]]].

  inversion H; inversion H4; subst.

  apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H6.
  apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H7.
  rewrite div_mul' in * by (apply Z.pow_nonzero; lia).
  congruence.
Qed.

Lemma jump_divstep_spec mw m d f g v r (n : nat)
      (fodd : Z.odd f = true)
      (Hmw : n < mw)
      (Hm : 1 < m)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m) :
  jump_divstep n mw m (d, f, g, v, r) =
    Nat.iter n (divstep_vr_mod m) (d, f, g, v, r).
Proof.
  symmetry.
  apply jump_divstep_full; try assumption;
    rewrite mod_pow_same_base_smaller; lia.
Qed.

Lemma Nat_iter_ext {A} n (f g : A -> A) a :
  (forall x, f x = g x) -> Nat.iter n f a = Nat.iter n g a.
Proof.
  intros; induction n.
  - reflexivity.
  - simpl. rewrite IHn. apply H.
Qed.

Lemma iter_jump_divstep_inv (n : nat) mw k m d f g v r
      (f_odd : Z.odd f = true)
      (Hmw : n < mw)
      (Hm : 1 < m)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m) :
  let '(_,f1,_,v1,r1) := Nat.iter k (jump_divstep n mw m) (d, f, g, v, r) in
  Z.odd f1 = true
  /\ 0 ≤ v1 < m
  /\ 0 ≤ r1 < m.
Proof.
  induction k as [|k IHk]; simpl; [auto|].
  destruct Nat.iter as [[[[d1 f1] g1] v1] r1].
  destruct IHk as [f1_odd [v1_bounds r1_bounds]].
  rewrite jump_divstep_spec by assumption.
  induction n; simpl; [auto|].
  specialize (IHn ltac:(lia)).
  destruct Nat.iter as [[[[dn fn]gn]vn]rn].
  destruct IHn as [fn_odd [vn_bounds rn_bounds]]; simpl.
  destruct (Z.odd gn) eqn:E; destruct (0 <? dn);
    split; try split; try apply Z.mod_pos_bound; try lia; try assumption.
Qed.

Lemma iter_jump_divstep_spec (n : nat) mw k m d f g v r
      (f_odd : Z.odd f = true)
      (Hmw : n < mw)
      (Hm : 1 < m)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m) :
  Nat.iter k (jump_divstep n mw m) (d, f, g, v, r) =
    Nat.iter (k * n) (divstep_vr_mod m) (d, f, g, v, r).
Proof.
  induction k.
  - reflexivity.
  - rewrite Nat.iter_mul, !Nat.iter_succ, <- Nat.iter_mul, IHk.
    pose proof iter_jump_divstep_inv n mw k m d f g v r f_odd Hmw Hm Hv Hr.
    destruct (Nat.iter (k * n) _ _) as [[[[d1 f1] g1]v1]r1].
    rewrite IHk in H. destruct H as [?[? ?]].
    apply jump_divstep_spec; auto.
Qed.

Lemma divstep_vr_divstep_vr_mod m d f g v r :
  divstep_vr_mod m (d, f, g, v, r) =
  let '(d1, f1, g1, v1, r1) := divstep_vr (d, f, g, v, r) in
  (d1, f1, g1, v1 mod m, r1 mod m).
Proof.
  unfold divstep_vr, divstep_vr_mod.
  destruct Z.odd, (0 <? d); reflexivity.
Qed.

Lemma iter_divstep_vr_iter_divstep_vr_mod (n : nat) m d f g v r
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m) :
  Nat.iter n (divstep_vr_mod m) (d, f, g, v, r) =
  let '(d1, f1, g1, v1, r1) := Nat.iter n divstep_vr (d, f, g, v, r) in
  (d1, f1, g1, v1 mod m, r1 mod m).
Proof.
  induction n.
  - simpl. rewrite !Z.mod_small by assumption. reflexivity.
  - simpl. rewrite IHn; clear IHn.
    destruct Nat.iter as [[[[d1 f1]g1]v1]r1].
    rewrite divstep_vr_divstep_vr_mod.
    simpl.
    destruct Z.odd, (0 <? d1); simpl.
    + rewrite Zmult_mod_idemp_r, Zminus_mod_idemp_r, Zminus_mod_idemp_l.
      reflexivity.
    + rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_r, Zplus_mod_idemp_l.
      reflexivity.
    + rewrite Zmult_mod_idemp_r.
      destruct (decide (m = 0)).
      * subst.
        rewrite !Zmod_0_r. reflexivity.
      * rewrite Z.mod_mod. reflexivity.
        assumption.
    + rewrite Zmult_mod_idemp_r.
      destruct (decide (m = 0)).
      * subst.
        rewrite !Zmod_0_r. reflexivity.
      * rewrite Z.mod_mod. reflexivity.
        assumption.
Qed.

Definition σ x y :=
  if decide (x < 0)
  then if decide (y < 0)
       then -1
       else 1
  else 1.

Definition τ x :=
  if decide (x mod 4 = 3) then -1
  else 1.

Definition η x y :=
  if decide (x mod 4 = 3)
  then if decide (y mod 4 = 3)
       then -1
       else 1
  else 1.

Definition ν x :=
  if decide (x mod 8 = 3)
  then -1
  else if decide (x mod 8 = 5)
       then -1
       else 1.

Definition divstep_jac '(d, f, g, k) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2, k * σ g (-f) * η g (-f) * ν g)
       else (1 + d, f, (g + f) / 2, k * ν f)
  else (1 + d, f, g / 2, k * ν f).

Definition divstep_jac_uvqr '(d, f, g, u, v, q, r, k) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2, u - q, v - r, 2 * u, 2 * v, k * σ g (-f) * η g (-f) * ν g)
       else (1 + d, f, (g + f) / 2, u + q, v + r, 2 * q, 2 * r, k * ν f)
  else (1 + d, f, g / 2, u, v, 2 * q, 2 * r, k * ν f).

Local Open Scope mat_scope.
Local Open Scope vec_scope.
Local Open Scope Z.

Definition fn d f g n := let '(_, fn, _) := Nat.iter n divstep (d, f, g) in fn.
Definition gn d f g n := let '(_, _, gn) := Nat.iter n divstep (d, f, g) in gn.
Definition dn d f g n := let '(dn, _, _) := Nat.iter n divstep (d, f, g) in dn.

Definition Tmat (d f g : Z) :=
  if Z.odd g
  then if 0 <? d
       then [ 0 , 2 ; -1 , 1 ]
       else [ 2 , 0 ; 1 , 1 ]
  else [ 2 , 0 ; 0 , 1 ].

Definition Smat (d f g : Z) :=
  if Z.odd g
  then if 0 <? d
       then [ 1 , 0 ; 1 , -1 ]
       else [ 1 , 0 ; 1 , 1 ]
  else [ 1 , 0 ; 1 , 1 ].

Definition Tn d f g n :=
  let '(dn, fn, gn) :=
      Nat.iter n divstep (d, f, g) in
  Tmat dn fn gn.

Definition Sn d f g n :=
  let '(dn, fn, gn) :=
      Nat.iter n divstep (d, f, g) in
  Smat dn fn gn.

Lemma Tn_0 d f g : Tn d f g 0 = Tmat d f g.
Proof. unfold Tn. reflexivity. Qed.

Lemma divstep_iter_0 d f g d' f' n k :
  Nat.iter n divstep (d, f, g) = (d', f', 0) -> Nat.iter (n + k) divstep (d, f, g) = (d' + k, f', 0).
Proof.
  induction k; intros.
  - rewrite Nat.add_0_r, Z.add_0_r; assumption.
  - replace (n + S k)%nat with (S (n + k)) by lia. simpl.
    rewrite IHk by assumption.
    unfold divstep. assert (Z.odd 0 = false) by reflexivity. rewrite H0.
    apply f_equal2; [apply f_equal2|]. lia. lia. reflexivity. Qed.

Lemma divstep_iter_0' d f g d' f' n m
      (Hnlem : (n <= m)%nat) :
  Nat.iter n divstep (d, f, g) = (d', f', 0) -> exists d'' f'', Nat.iter m divstep (d, f, g) = (d'', f'', 0).
Proof.
  set (k := (m - n)%nat). intros H.
  apply divstep_iter_0 with (k := k) in H.
  replace (n + k)%nat with m in H by lia. eauto. Qed.

Lemma fn_odd d f g n : Z.odd f = true -> Z.odd (fn d f g n) = true.
Proof.
  intros. unfold fn. induction n.
  - assumption.
  - rewrite Nat.iter_succ. destruct (Nat.iter _ _ _) as [[dn fn] gn].
    unfold divstep. destruct (0 <? dn); destruct (Z.odd gn) eqn:gnodd; simpl; assumption. Qed.

(* Local Open Scope group_scope. *)
Local Open Scope ring_scope.
Local Open Scope lmod_scope.

Lemma Tn_transition d f g n (fodd : Z.odd f = true) :
    2 ⋅ [ fn d f g (S n) , gn d f g (S n) ] = ((Tn d f g n) ⋅ [ fn d f g n , gn d f g n ]).
Proof.
  pose proof fn_odd d f g n fodd as fnodd. (* cbv [module_left_act vmult_left_act vmult]. *)
  unfold Tn, fn, gn, Tmat in *. rewrite Nat.iter_succ. unfold divstep.
  destruct (Nat.iter _ _ _) as [[dn fn] gn]. zify.
  destruct (0 <? dn); destruct (Z.odd gn) eqn:gnodd; cbn -[Z.mul]; apply f_equal2;
    rewrite <- ?Z_div_exact_full_2; rewrite ?Zmod_odd, ?Z.odd_sub, ?Z.odd_add, ?fnodd, ?gnodd; try (zify; lia); try reflexivity. Qed.

Lemma Sn_transition d f g n :
    [ 1 , dn d f g (S n) ] ≡ (Sn d f g n) ⋅ [ 1 , dn d f g n ].
Proof.
  unfold Sn, dn, Smat in *. rewrite Nat.iter_succ. unfold divstep.
  destruct (Nat.iter _ _ _) as [[dn fn] gn].
  destruct (0 <? dn), (Z.odd gn); auto_mat. Qed.

Lemma divstep_full_spec d f g :
  let '(d1, f1, g1, v1, r1) := divstep_vr (d, f, g, 0, 1) in
  exists u1 q1, [ u1, v1; q1, r1 ] = Tmat d f g.
Proof.
  unfold divstep_vr, Tmat.
  destruct (0 <? d), (Z.odd g); do 2 eexists; repeat apply f_equal2; try lia; reflexivity. Qed.

Ltac pair_eq :=
  repeat match goal with
         | [ |- (_, _) = (_, _)] => apply f_equal2
         end.

Lemma divstep_full_iter_spec d f g m :
  let '(d1, f1, g1, v1, r1) := Nat.iter m divstep_vr (d, f, g, 0, 1) in
  exists u1 q1, [ u1, v1; q1, r1 ] ≡ big_mul_rev (fun i : nat => Tn d f g i) 0%nat m.
Proof.
  induction m.
  - rewrite big_op_rev_nil by lia. do 2 eexists. auto_mat.
  - rewrite Nat.iter_succ.
    pose proof iter_divstep_vr_iter_divstep d f g 0 1 m.
    destruct (Nat.iter _ _ _) as [[[[dm fm] gm] vm] rm] eqn:full_iter.
    destruct IHm as [um [qm]].
    destruct (divstep_vr (dm, fm, gm, vm, rm)) as [[[[dSm fSm] gSm] vSm] rSm] eqn:vr.
    setoid_rewrite (big_op_rev_S_l [*] 1); [|lia].
    setoid_rewrite <- H0.
    unfold Tn. rewrite H.
    unfold Tmat.
    unfold divstep_vr in vr.
    destruct (0 <? dm), (Z.odd gm) eqn:E;
      do 2 eexists; inversion vr; auto_mat.
Qed.
