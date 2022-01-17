From Coq Require Import Arith micromega.Lia.
From BY Require Import Hierarchy.Definitions Hierarchy.SemiGroup Hierarchy.List.

Section Monoid.

  Local Open Scope mag_scope.
  Local Open Scope mon_scope.

  Context
    `{Monoid A}.
  Local Instance : Magma A. sub_class_tac. Qed.
  Local Instance : SemiGroup A. sub_class_tac. Qed.

  Instance quot_mon (rel : relation A) `{!MagmaCongruence rel} `{subrelation A (≡) rel} : @Monoid _ rel _ _.
  repeat split; try apply _;
  cbv; intros; apply is_subrelation; (apply assoc; exact _) || (apply right_id; exact _) || (apply left_id; exact _). Qed.

  Context
    (f : nat -> A).

  Definition big_op_list (l : list nat) f := fold_left (∘) (map f l) ε.
  Definition big_op f n m := big_op_list (seq n (m - n)) f.
  Definition big_op_rev f n m := big_op_list (rev (seq n (m - n))) f.

  Hint Unfold big_op big_op_rev big_op_list : bigop.

  Lemma big_op_S_r n m (nltm : n <= m) :
    big_op f n (S m) = big_op f n m ∘ f m.
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, map_app, fold_left_app, <- le_plus_minus; auto. Qed.

  Lemma big_op_S_l n m (nltm : n <= m) :
    big_op f n (S m) ≡ f n ∘ big_op f (S n) (S m).
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, fold_left_assoc. auto.
         simpl. rewrite mon_id_r, mon_id_l.
         auto. assumption. Qed.

  Lemma big_op_rev_S_r n m (nltm : n <= m) :
    big_op_rev f n (S m) = big_op_rev f (S n) (S m) ∘ f n.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l by auto; simpl; rewrite map_app, fold_left_app. reflexivity. Qed.

  Lemma big_op_rev_S_l n m (nltm : n <= m) :
    big_op_rev f n (S m) ≡ f m ∘ big_op_rev f n m.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, rev_app_distr, fold_left_assoc, <- le_plus_minus, (right_id ε (∘)) by auto; simpl;
           rewrite (left_id ε (∘)); auto. Qed.

  Lemma big_op_rev_nil n m (mltn : m <= n) :
    big_op_rev f n m = ε.
  Proof. unfold big_op_rev; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_nil n m (mltn : m <= n) :
    big_op f n m = ε.
  Proof. unfold big_op; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_split n m k (nmk : n <= m <= k) :
    (big_op f n m) ∘ (big_op f m k) ≡ big_op f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n = 0); assert (m = 0); subst; try lia. rewrite big_op_nil, (left_id ε (∘)). reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_nil (S k)), (right_id ε (∘)). reflexivity. lia.
      + rewrite big_op_S_r, (assoc (∘)), IHk, <- big_op_S_r by lia. reflexivity. Qed.

  Lemma big_op_rev_split n m k (nmk : n <= m <= k) :
    (big_op_rev f m k) ∘ (big_op_rev f n m) ≡ big_op_rev f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n = 0); assert (m = 0); try lia; subst. rewrite big_op_rev_nil, (left_id ε (∘)). reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_rev_nil (S k)), (left_id ε (∘)). reflexivity. lia.
      + rewrite big_op_rev_S_l, <- (assoc (∘)), IHk, <- big_op_rev_S_l by lia. reflexivity. Qed.

  Lemma big_op_shift g n m k :
    (forall i, f i ≡ g (i + k)) ->
    big_op f n m ≡ big_op g (n + k) (m + k).
  Proof.
    intros. unfold big_op, big_op_list. f_equiv.
    replace (m + k - (n + k)) with (m - n) by lia.
    apply map_seq_ext_equiv; intros. rewrite H3.
    replace (i + (n + k - n)) with (i + k) by lia.
    reflexivity. lia. Qed.

  Lemma big_op_rev_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op_rev f n m ≡ big_op_rev g (n + k) (m + k).
  Proof.
    intros. unfold big_op_rev, big_op_list. f_equiv.
    rewrite !map_rev. replace (m + k - (n + k)) with (m - n) by lia.

    f_equiv. apply map_seq_ext_equiv. intros.
    rewrite H3.
    replace (i + (n + k - n)) with (i + k) by lia.
    reflexivity. lia.
  Qed.
End Monoid.
