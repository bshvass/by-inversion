Require Import List Arith ZArith micromega.Lia.

From BY Require Import Matrix.

(* Local Open Scope mat_scope. *)

Lemma seq_snoc len : forall start, seq start (S len) = seq start len ++ ((start + len)%nat :: nil).
Proof.
  induction len; intros.
  { cbv [seq app]. rewrite Nat.add_0_r; reflexivity. }
  { remember (S len); simpl seq.
    rewrite (IHlen (S start)); subst; simpl seq.
    rewrite Nat.add_succ_r; reflexivity. }
Qed.

Lemma map_seq_ext {A} (f g : nat -> A) (n m k : nat)
      (H : forall i : nat, n <= i < m + k -> f i = g (i + (m - n))%nat)
      (Hnm : n <= m) :
  map f (seq n k) = map g (seq m k).
Proof.
  generalize dependent m; generalize dependent n; induction k as [|k IHk]; intros; simpl.
  - reflexivity.
  - simpl; rewrite H by lia; replace (n + (m - n))%nat with m by lia.
    rewrite (IHk (S n) (S m)); [reflexivity| |lia].
    intros; rewrite Nat.sub_succ; apply H; lia. Qed.

Section __.
  Context {A : Type}
          {op : A -> A -> A}
          {id : A}.

  Class Associative {A : Type} (op : A -> A -> A) :=
    { op_assoc : forall x y z, op x (op y z) = op (op x y) z }.

  Context {Assoc : @Associative _ op}.

  Lemma fold_left_assoc (a b : A) ls :
  op a (fold_left op ls b) = fold_left op ls (op a b).
  Proof.
    revert b; induction ls; intros b; simpl.
    - reflexivity.
    - rewrite IHls. rewrite op_assoc. reflexivity. Qed.

  Class Monoid {A : Type} (op : A -> A -> A) (id : A) {Op_assoc : Associative op} : Prop :=
    { id_l : forall x, op id x = x;
      id_r : forall x, op x id = x }.

  Context {M : Monoid op id}
          (f : nat -> A).

  Local Infix "∘" := op (at level 50).

  Definition big_op_list (l : list nat) f := fold_left op (map f l) id.
  Definition big_op f n m := big_op_list (seq n (m - n)) f.
  Definition big_op_rev f n m := big_op_list (rev (seq n (m - n))) f.

  Hint Unfold big_op big_op_rev big_op_list : bigop.

  Lemma big_op_S_r n m (nltm : n <= m) :
    big_op f n (S m) = big_op f n m ∘ f m.
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, map_app, fold_left_app, <- le_plus_minus; auto. Qed.

  Lemma big_op_S_l n m (nltm : n <= m) :
    big_op f n (S m) = f n ∘ big_op f (S n) (S m).
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, fold_left_assoc; auto.
         simpl; rewrite (id_l (f n)), (id_r (f n)); auto. Qed.

  Lemma big_op_rev_S_r n m (nltm : n <= m) :
    big_op_rev f n (S m) = big_op_rev f (S n) (S m) ∘ f n.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l by auto; simpl; rewrite map_app, fold_left_app. reflexivity. Qed.

  Lemma big_op_rev_S_l n m (nltm : n <= m) :
    big_op_rev f n (S m) = f m ∘ big_op_rev f n m.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, rev_app_distr, fold_left_assoc, <- le_plus_minus, (id_r (f m)) by auto; simpl;
           rewrite (id_l (f m)); auto. Qed.

  Lemma big_op_rev_nil n m (mltn : m <= n) :
    big_op_rev f n m = id.
  Proof. unfold big_op_rev; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_nil n m (mltn : m <= n) :
    big_op f n m = id.
  Proof. unfold big_op; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_split n m k (nmk : n <= m <= k) :
    (big_op f n m) ∘ (big_op f m k) = big_op f n k.
  Proof.
    revert nmk. revert n m.
    induction k; intros.
    unfold big_op.
    assert (n = 0) by lia.
    assert (m = 0) by lia.
    subst. unfold big_op_list. rewrite id_l. reflexivity.
    destruct (Nat.eq_dec m (S k)). subst. rewrite (big_op_nil (S k)). rewrite id_r. reflexivity. lia.
    rewrite big_op_S_r. rewrite op_assoc. rewrite IHk. rewrite <- big_op_S_r. reflexivity. lia. lia. lia. Qed.

  Lemma big_op_rev_split n m k (nmk : n <= m <= k) :
    (big_op_rev f m k) ∘ (big_op_rev f n m) = big_op_rev f n k.
  Proof.
    revert nmk. revert n m.
    induction k; intros.
    unfold big_op_rev.
    assert (n = 0) by lia.
    assert (m = 0) by lia.
    subst. unfold big_op_list. rewrite id_r. reflexivity.
    destruct (Nat.eq_dec m (S k)). subst. rewrite (big_op_rev_nil (S k)). rewrite id_l. reflexivity. lia.
    rewrite big_op_rev_S_l. rewrite <- op_assoc. rewrite IHk. rewrite <- big_op_rev_S_l. reflexivity. lia. lia. lia. Qed.

  Lemma big_op_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op f n m = big_op g (n + k) (m + k).
  Proof.
    intros.
    unfold big_op. unfold big_op_list.
    apply f_equal2.
    replace (m + k - (n + k)) with (m - n).
    apply map_seq_ext. intros.
    rewrite H. apply f_equal. lia. lia. lia. reflexivity. Qed.

  Lemma big_op_rev_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op_rev f n m = big_op_rev g (n + k) (m + k).
  Proof.
    intros.
    unfold big_op_rev. unfold big_op_list.
    apply f_equal2.
    replace (m + k - (n + k)) with (m - n). rewrite !map_rev.
    apply f_equal.
    apply map_seq_ext. intros.
    rewrite H. apply f_equal. lia. lia. lia. reflexivity. Qed.

End __.


(* Definition big_sum := @big_op _ Nat.add 0. *)

Instance N_add_associative : Associative Nat.add.
Proof. split; auto with zarith. Qed.

Instance N_add_monoid : Monoid Nat.add 0.
Proof. split; auto with zarith. Qed.

Instance Mat_mult_associative : Associative mmult.
Proof. split; auto with matrix. Qed.

Instance Mat_monoid : Monoid mmult I.
Proof. split; auto with matrix. Qed.

Instance Z_add_associative : Associative Z.add.
Proof. split; auto with zarith. Qed.

Instance Z_add_monoid : Monoid Z.add 0%Z.
Proof. split; auto with zarith. Qed.

Notation big_sum := (@big_op _ Z.add 0%Z).
Notation big_sum_nat := (@big_op _ Nat.add 0%nat).
Notation big_mmult_rev := (@big_op_rev _ mmult I).
(* Notation big_mmult_rev0 := (fun n f => @big_op_rev _ mmult I f 0 n). *)

Lemma big_sum_bound n f :
  (forall i, (i <= n)%nat -> (1 <= f i)%nat) -> (n <= big_sum_nat f 0 n)%nat.
Proof.
  induction n; intros.
  - unfold big_sum_nat. simpl. lia.
  - assert (forall i : nat, i <= n -> 1 <= f i)%nat by (intros; apply H; lia).
    apply IHn in H0. rewrite big_op_S_r by lia.
    assert (1 <= f n)%nat by (apply H; lia); lia. Qed.
