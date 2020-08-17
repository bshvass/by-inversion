From Coq Require Import Setoid Morphisms Rbase Reals micromega.Lra micromega.Lia.

Local Open Scope R.

Add Parametric Relation : R Rlt transitivity proved by Rlt_trans as Rlt.
Add Parametric Morphism : Rplus with signature Rlt ==> Rlt ==> Rlt as Rlt_Rplus.
Proof. intros; lra. Qed.
Add Parametric Morphism a : (Rplus a) with signature Rlt ==> Rlt as Rlt_Rplus_r.
Proof. intros; lra. Qed.

Definition Rle_pos a b := 0 <= a <= b.
Definition Rlt_pos a b := 0 <= a < b.


Notation "a <=0 b" := (Rle_pos a b) (at level 50).
Notation "a <0 b" := (Rlt_pos a b) (at level 50).

Lemma Rle_pos_trans a b c : a <=0 b -> b <=0 c -> a <=0 c.
Proof. unfold Rle_pos; intros; nra. Qed.

Add Parametric Relation : R Rle reflexivity proved by Rle_refl transitivity proved by Rle_trans as Rle.
Add Parametric Relation : R Rle_pos transitivity proved by Rle_pos_trans as Rle_pos.

Add Parametric Morphism : Rplus with signature Rdefinitions.Rle ==> Rdefinitions.Rle ==> Rdefinitions.Rle as Rle_Rplus.
Proof. intros; lra. Qed.
Add Parametric Morphism : sqrt with signature Rdefinitions.Rle ==> Rdefinitions.Rle as Rle_sqrt.
Proof. now intros; apply sqrt_le_1_alt. Qed.

Add Parametric Morphism : Rmult with signature Rle_pos ==> Rle_pos ==> Rdefinitions.Rle as Rle_pos_Rle_Rmult.
Proof. unfold Rle_pos; intros ? ? [?] ? ? [?]; nra. Qed.

Add Parametric Morphism : Rmult with signature Rle_pos ==> Rle_pos ==> Rle_pos as Rle_pos_Rmult.
Proof. unfold Rle_pos; intros ? ? [?] ? ? [?]; nra. Qed.

Add Parametric Morphism a (Ha : 0 <= a) : (Rmult a) with signature Rle_pos ==> Rle_pos as Rle_pos_Rmult_r.
Proof. unfold Rle_pos; intros ? ? [?]. nra. Qed.
Add Parametric Morphism : Rmult with signature Rlt_pos ==> Rlt_pos ==> Rdefinitions.Rle as Rlt_pos_Rle_Rmult.
Proof. unfold Rle_pos; intros ? ? [?] ? ? [?]; nra. Qed.
  
Add Parametric Morphism a (Ha : 0 <= a) : (Rmult a) with signature Rdefinitions.Rle ==> Rdefinitions.Rle as Rle_Rmult_r.
Proof. intros; nra. Qed.
(* Add Parametric Morphism : RinvImpl.Rinv with signature Rdefinitions.Rle ==> Rdefinitions.Rle ==> Rdefinitions.Rle as Rle_Rplus. *)

(* Proof. intros; lra. Qed.  *)

(* Add Parametric Morphism a : (Rplus a) with signature Rdefinitions.Rle ==> Rdefinitions.Rle as Rle_Rplus_r. *)
(* Proof. intros; lra. Qed. *)

(* Instance Rplus_proper_l (a : R) : Proper (Rlt ==> Rlt) (Rplus a). *)
(* Proof. intros b c H; lra. Qed. *)

(* Instance Rplus_proper_r (a : R) : Proper (Rlt ==> Rlt) (fun b => Rplus b a). *)
(* Proof. intros b c H; lra. Qed. *)

(* Instance Rplus_proper : Proper (Rlt ==> Rlt ==> Rlt) Rplus. *)
(* Proof. intros a b H c d; lra. Qed. *)

(* Instance Rlt_trans : Transitive Rlt. *)
(* Proof. intros a b c; lra. Qed. *)

Lemma test_lemma a b c : a <= b -> c + a <= c + b.
Proof. intros H. rewrite H. setoid_reflexivity. Qed.

Lemma test_lemma2 a b c : a <= b -> a + c <= b + c.
Proof. intros H. rewrite H. setoid_reflexivity. Qed.

Lemma monotone a b c : 0 <= a -> 0 <= b -> b <= c -> a * b <= a * c. 
Proof. Admitted.

Lemma test_lemma3 a b c : 0 <= a -> b <= c -> (Rmult a) b <= (Rmult a) c.
Proof.
  intros. Admitted.
