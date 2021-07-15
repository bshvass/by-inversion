Require Import List QArith Qreals.

Local Open Scope Q.

Import ListNotations.
Notation Qmin := Qminmax.Qmin.

Fixpoint Qmin_list l : Q :=
  match l with
  | nil => 0
  | a :: l0 => match l0 with
            | nil => a
            | _ => Qmin a (Qmin_list l0)
            end
  end.

Lemma Qmin_list_cons a b l :
  Qmin_list (a :: b :: l) = Qmin a (Qmin_list (b :: l)).
Proof. reflexivity. Qed.

Lemma Qmin_list_snoc a b l :
  Qmin_list (a :: l ++ [b]) == Qmin (Qmin_list (a :: l)) b.
Proof.
  revert a; induction l; intros.
  - reflexivity.
  - rewrite <- app_comm_cons, Qmin_list_cons. rewrite IHl.
    rewrite Qmin_list_cons. apply Qminmax.Q.min_assoc.
Qed.

Lemma Qmin_list_cons_cons a b l :
  Qmin_list (a :: b :: l) == Qmin_list (b :: a :: l).
Proof.
  remember (rev l).
  revert l Heql0; induction l0; intros.
  - apply (f_equal (@rev Q)) in Heql0.
    rewrite rev_involutive in Heql0. simpl in Heql0. subst.
    apply Qminmax.Q.min_comm.
  - apply (f_equal (@rev Q)) in Heql0.
    rewrite rev_involutive in Heql0. simpl in Heql0. subst.
    rewrite !app_comm_cons.
    setoid_rewrite Qmin_list_snoc.
    rewrite IHl0.
    reflexivity.
    symmetry; apply rev_involutive.
Qed.

Lemma Qmin_list_spec l :
  forall a, In a l -> Qmin_list l <= a.
Proof.
  induction l; intros.
  - destruct H.
  - destruct H.
    + subst. destruct l.
      * apply Qle_refl.
      * rewrite Qmin_list_cons.
        apply Qminmax.Q.le_min_l.
    + destruct l.
      * destruct H.
      * rewrite Qmin_list_cons.
        eapply Qle_trans.
        apply Qminmax.Q.le_min_r.
        apply IHl. assumption. Qed.

Lemma Qmin_list_spec2 l (H : ~ (l = nil)) :
  exists a, In a l /\ Qmin_list l == a.
Proof.
  induction l.
  - contradiction.
  -
    destruct l.
    + simpl. exists a. split. left; reflexivity. reflexivity.
    + assert (q :: l <> nil) by congruence.
      apply IHl in H0. destruct H0 as [x []].
      destruct (Qminmax.Q.min_dec a x).
      * exists a. split. left; reflexivity. rewrite Qmin_list_cons. rewrite H1. assumption.
      * exists x. split. right; assumption. rewrite Qmin_list_cons. rewrite H1. assumption. Qed.

Lemma Qmin_list_app l k : l <> [] -> k <> [] ->
  Qmin_list (l ++ k) == Qmin (Qmin_list l) (Qmin_list k).
Proof.
  destruct k; destruct l; try congruence; intros.
  revert q k H0; induction l; intros.
  - reflexivity.
  -
    rewrite <- app_comm_cons.
    rewrite <- app_comm_cons.
    rewrite Qmin_list_cons_cons.
    rewrite Qmin_list_cons.
    setoid_rewrite IHl; try congruence.
    rewrite Qmin_list_cons_cons.
    rewrite Qmin_list_cons.
    rewrite Qminmax.Q.min_assoc. reflexivity.
Qed.

Instance Qmin_list_single_proper : Proper (Qeq ==> Qeq) (fun q => Qmin_list [q]).
Proof.
  do 2 red; intros. apply H.
Qed.

Instance Qmin_list_proper : Proper (eq ==> Qeq) Qmin_list.
Proof.
  do 2 red; intros. rewrite H. reflexivity.
Qed.

Lemma Qmin_list_single q : Qmin_list [q] = q.
Proof. reflexivity. Qed.

Inductive Qlist_eq : list Q -> list Q -> Prop :=
| Qlist_eq_nil : Qlist_eq [] []
| Qlist_eq_cons x y l k : x == y -> Qlist_eq l k -> Qlist_eq (x :: l) (y :: k).
Local Notation "l == k" := (Qlist_eq l k).

Require Import Classes.RelationClasses.

Instance Qlist_eq_refl : Reflexive Qlist_eq.
Proof. red; intros; induction x; constructor; [reflexivity|assumption]. Qed.
Instance Qlist_eq_sym : Symmetric Qlist_eq.
Proof. red; intros. induction H; [reflexivity|constructor; [symmetry|]; assumption]. Qed.
Instance Qlist_eq_trans : Transitive Qlist_eq.
Proof. red. intros x. induction x; intros.
       - inversion H; subst; assumption.
       - destruct z.
         + inversion H0; subst; assumption.
         + inversion H. subst. inversion H0. subst. constructor.
           etransitivity. eassumption. assumption.
           apply IHx with (y:=k); assumption. Qed.

Instance cons_Qlist_eq_proper : Proper (Qeq ==> Qlist_eq ==> Qlist_eq) cons.
Proof.
  red; red; intros.
  red; intros. constructor; assumption. Qed.

Instance app_Qlist_eq_proper : Proper (Qlist_eq ==> Qlist_eq ==> Qlist_eq) (@app Q).
Proof.
  red; red; intros.
  red; intros. induction H.
  - assumption.
  - rewrite <- !app_comm_cons. constructor. assumption. assumption. Qed.

Instance Qmin_list_proper2 : Proper (Qlist_eq ==> Qeq) Qmin_list.
Proof.
  do 2 red. intros.
  destruct H.
  - reflexivity.
  - induction H0.
    + assumption.
    + do 2 rewrite Qmin_list_cons_cons, Qmin_list_cons.
      setoid_rewrite IHQlist_eq.
      setoid_rewrite H0. reflexivity. Qed.
