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
  
  Definition big_op_list (l : list nat) := fold_left op (map f l) id.
  Definition big_op n m := big_op_list (seq n (m - n)).
  Definition big_op_rev n m := big_op_list (rev (seq n (m - n))).

  Hint Unfold big_op big_op_rev big_op_list : bigop.
  
  Lemma big_op_S_r n m (nltm : n <= m) :
    big_op n (S m) = big_op n m ∘ f m.
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, map_app, fold_left_app, <- le_plus_minus; auto. Qed.

  Lemma big_op_S_l n m (nltm : n <= m) :
    big_op n (S m) = f n ∘ big_op (S n) (S m).
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, fold_left_assoc; auto.
         simpl; rewrite (id_l (f n)), (id_r (f n)); auto. Qed.

  Lemma big_op_rev_S_r n m (nltm : n <= m) :
    big_op_rev n (S m) = big_op_rev (S n) (S m) ∘ f n.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l by auto; simpl; rewrite map_app, fold_left_app. reflexivity. Qed.
  
  Lemma big_op_rev_S_l n m (nltm : n <= m) :
    big_op_rev n (S m) = f m ∘ big_op_rev n m.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, rev_app_distr, fold_left_assoc, <- le_plus_minus, (id_r (f m)) by auto; simpl; 
           rewrite (id_l (f m)); auto. Qed.

  Lemma big_op_nil n m (mltn : m <= n) :
    big_op n m = id.
  Proof. unfold big_op; replace (m - n) with 0 by lia; reflexivity. Qed.
End __.

(* Definition big_sum := @big_op _ Nat.add 0. *)

Instance N_add_associative : Associative Nat.add.
Proof. split; auto with zarith. Qed.

Instance N_add_monoid : @Monoid _ Nat.add 0 N_add_associative.
Proof. split; auto with zarith. Qed.

Instance Mat_mult_associative : Associative mmult.
Proof. split; auto with matrix. Qed.

Instance Mat_monoid : @Monoid _ mmult I Mat_mult_associative.
Proof. split; auto with matrix. Qed.

Instance Z_add_associative : Associative Z.add.
Proof. split; auto with zarith. Qed.

Instance Z_add_monoid : @Monoid _ Z.add 0%Z Z_add_associative.
Proof. split; auto with zarith. Qed.

(* Lemma big_mmult_rev_S n f : *)
(*   big_mmult_rev (S n) f = f n * big_mmult_rev n f. *)
(* Proof. unfold big_mmult_rev; rewrite seq_snoc, rev_app_distr; reflexivity. Qed. *)

(* Definition big_mmult_rev n (f : nat -> mat) := *)
(*   fold_right mmult I (map f (rev (seq 0 n))). *)

(* Lemma big_mmult_rev_S n f : *)
(*   big_mmult_rev (S n) f = f n * big_mmult_rev n f. *)
(* Proof. unfold big_mmult_rev; rewrite seq_snoc, rev_app_distr; reflexivity. Qed. *)

(* Definition big_sum_rev n f : nat := *)
(*   fold_right (Nat.add) 0%nat (map f (rev (seq 0 n))). *)

(* Lemma big_sum_rev_S n f : *)
(*   big_sum_rev (S n) f = (f n + big_sum_rev n f)%nat. *)
(* Proof. unfold big_sum_rev; rewrite seq_snoc, rev_app_distr; reflexivity. Qed. *)

(* Lemma big_sum_bound1 n f : *)
(*   (forall i, i <= n -> 1 <= f i) -> n <= big_sum_rev n f. *)
(* Proof. *)
(*   intros. *)

(*   induction n. *)
(*   unfold big_sum_rev. simpl. lia. *)

(*   assert (forall i : nat, i <= n -> 1 <= f i). intros; apply H. lia. *)
(*   apply IHn in H0. *)

(*   rewrite big_sum_rev_S. *)
(*   assert (1 <= f n). apply H. lia. lia. Qed. *)

(* Definition big_sum n f : Z := *)
(*   fold_right Z.add 0%Z (map f (rev (seq 0 n))). *)

(* Lemma big_sum_S n f : *)
(*   big_sum (S n) f = (f n + big_sum n f)%Z. *)
(* Proof. unfold big_sum; rewrite seq_snoc, rev_app_distr; reflexivity. Qed. *)
