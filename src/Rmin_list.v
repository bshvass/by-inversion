Require Import List.
Require Import Reals Lra.

From BY Require Import Impl.

Local Open Scope R.

Definition Rmin a b := if Rle_dec a b then a else b.

Definition Rmin_l a b : Rmin a b <= a.
Proof. unfold Rmin. destruct (Rle_dec a b); lra. Qed.

Definition Rmin_r a b : Rmin a b <= b.
Proof. unfold Rmin. destruct (Rle_dec a b); lra. Qed.

Fixpoint Rmin_list l : R :=
  match l with
  | nil => 0
  | a :: l0 => match l0 with
            | nil => a
            | _ => Rmin a (Rmin_list l0)
            end
  end.

Lemma Rmin_list_cons a b l :
  Rmin_list (a :: b :: l) = Rmin a (Rmin_list (b :: l)).
Proof. reflexivity. Qed.

Lemma Rmin_list_spec l :
  forall a, In a l -> Rmin_list l <= a.
Proof.
  induction l; intros.
  - destruct H.
  - destruct H.
    + subst. destruct l.
      * reflexivity.
      * rewrite Rmin_list_cons.
        apply Rmin_l.
    + destruct l.
      * destruct H.
      * rewrite Rmin_list_cons.
        etransitivity. apply Rmin_r.
        apply IHl. assumption. Qed.

Lemma Rmin_list_spec2 l (H : ~ (l = nil)) :
  exists a, In a l /\ Rmin_list l = a.
Proof.
  induction l.
  - contradiction.
  - destruct l.
    + simpl. exists a. split. left; reflexivity. reflexivity.
    + assert (r :: l <> nil). intros contra. inversion contra.
      apply IHl in H0. destruct H0 as [x []].
      exists (Rmin a x).
      rewrite Rmin_list_cons.
      split. unfold Rmin. destruct Rle_dec. left; reflexivity. right. assumption. subst. reflexivity. Qed.
