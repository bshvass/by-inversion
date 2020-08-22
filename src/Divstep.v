Require Import Bool ZArith micromega.Lia.

Import Z.

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

Definition divstep_full m d f g v r :=
  if (0 <? d) && Z.odd g
  then (1 - d, g, (g - f) / 2, 2 * r mod m, (r - v) mod m)
  else (1 + d, f, (g + (g mod 2) * f) / 2, 2 * v mod m, (r + (g mod 2) * v) mod m).

Fixpoint divstep_iter' d f g n :=
  match n with
  | 0%nat => (d, f, g)
  | S n => let '(d, f, g) := divstep d f g in divstep_iter' d f g n
  end.

Fixpoint divstep_iter d f g n :=
  match n with
  | 0%nat => (d, f, g)
  | S m => let '(d, f, g) := divstep_iter d f g m in divstep d f g
  end.

Lemma divstep_iter_S d f g n :
  divstep_iter d f g (S n) = let '(d', f', g') := divstep_iter d f g n in divstep d' f' g'.
Proof. reflexivity. Qed.

Lemma divstep_iter_S' d f g n :
  divstep_iter d f g (S n) = let '(d', f', g') := divstep d f g in divstep_iter d' f' g' n.
Proof.
  induction n.
  - simpl; destruct (divstep d f g) as [[d' f'] g']; reflexivity.
  - rewrite divstep_iter_S. rewrite IHn. 
    destruct (divstep d f g) as [[d' f'] g']. rewrite divstep_iter_S. reflexivity. Qed.

Lemma divstep_iter_divstep_iter' d f g n :
  divstep_iter d f g n = divstep_iter' d f g n.
Proof.
  revert d f g.
  induction n; intros.
  - reflexivity.
  - rewrite divstep_iter_S'. simpl.
    destruct (divstep d f g) as [[d' f'] g']. rewrite IHn. reflexivity. Qed.

Lemma divstep_iter_add d f g n m :
  divstep_iter d f g (n + m) =
  let '(d', f', g') := divstep_iter d f g n in
  divstep_iter d' f' g' m.
Proof. induction m. 
       - rewrite Nat.add_0_r. destruct (divstep_iter d f g n) as [[d' f'] g']. reflexivity.
       - rewrite Nat.add_succ_r. simpl. rewrite IHm.
         destruct (divstep_iter d f g n) as [[d' f'] g']. reflexivity. Qed.

Lemma divstep_iter_0 d f g d' f' n k :
  divstep_iter d f g n = (d', f', 0) -> divstep_iter d f g (n + k) = (d' + k, f', 0).
Proof.
  induction k; intros.
  - rewrite Nat.add_0_r, add_0_r. auto.
  - replace (n + S k)%nat with (S (n + k)) by lia. simpl.
    rewrite IHk by assumption.
    unfold divstep. assert (odd 0 = false) by reflexivity. rewrite H0.
    rewrite andb_false_r. rewrite mod_0_l.
    apply f_equal2; [apply f_equal2|]. lia. lia. reflexivity. lia. Qed.
