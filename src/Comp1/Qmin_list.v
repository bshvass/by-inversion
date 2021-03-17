Require Import QArith.
Require Import List.

From BY Require Import Q AppendixF.

Local Open Scope Q.

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
