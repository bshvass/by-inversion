Require Import List Reals Lia Lra.
From BY Require Import Rlemmas ListLemmas Rmin_list Zpower_nat Matrix Spectral.

Import ListNotations.

Local Open Scope R.
Local Open Scope mat_scope.

Local Coercion IZR : Z >-> R.

(***************************************************************************************)
(** The next section contains definitions of the various number series used to analyse *)
(** the complexity of the Rj number sequence (from AppendixE).                         *)
(** These are primarily used AppendixF.v                                               *)
(***************************************************************************************)

Definition M (e : nat) (q : Z) := [ 0 , 1 / (2 ^ e) ; - 1 / (2 ^ e) , q / (2 ^ (2 * e)) ].

Definition alpha_high w : R := (633/1024) ^ w.

Definition alpha (w : nat) : R :=
  match w with
  | 0%nat => 1 | 1%nat => 1 | 2%nat => 689491/2^20 | 3%nat => 779411/2^21
  | 4%nat => 880833/2^22 | 5%nat => 165219/2^20 | 6%nat => 97723/2^20 | 7%nat => 882313/2^24
  | 8%nat => 306733/2^23 | 9%nat => 92045/2^22 | 10%nat => 439213/2^25 | 11%nat => 281681/2^25
  | 12%nat => 689007/2^27 | 13%nat => 824303/2^28 | 14%nat => 257817/2^27 | 15%nat => 634229/2^29
  | 16%nat => 386245/2^29 | 17%nat => 942951/2^31 | 18%nat => 583433/2^31 | 19%nat => 713653/2^32
  | 20%nat => 432891/2^32 | 21%nat => 133569/2^31 | 22%nat => 328293/2^33 | 23%nat => 800421/2^35
  | 24%nat => 489233/2^35 | 25%nat => 604059/2^36 | 26%nat => 738889/2^37 | 27%nat => 112215/2^35
  | 28%nat => 276775/2^37 | 29%nat => 84973/2^36 | 30%nat => 829297/2^40 | 31%nat => 253443/2^39
  | 32%nat => 625405/2^41 | 33%nat => 95625/2^39 | 34%nat => 465055/2^42 | 35%nat => 286567/2^42
  | 36%nat => 175951/2^42 | 37%nat => 858637/2^45 | 38%nat => 65647/2^42 | 39%nat => 40469/2^42
  | 40%nat => 24751/2^42 | 41%nat => 240917/2^46 | 42%nat => 593411/2^48 | 43%nat => 364337/2^48
  | 44%nat => 889015/2^50 | 45%nat => 543791/2^50 | 46%nat => 41899/2^47 | 47%nat => 205005/2^50
  | 48%nat => 997791/2^53 | 49%nat => 307191/2^52 | 50%nat => 754423/2^54 | 51%nat => 57527/2^51
  | 52%nat => 281515/2^54 | 53%nat => 694073/2^56 | 54%nat => 212249/2^55 | 55%nat => 258273/2^56
  | 56%nat => 636093/2^58 | 57%nat => 781081/2^59 | 58%nat => 952959/2^60 | 59%nat => 291475/2^59
  | 60%nat => 718599/2^61 | 61%nat => 878997/2^62 | 62%nat => 534821/2^62 | 63%nat => 329285/2^62
  | 64%nat => 404341/2^63 | 65%nat => 986633/2^65 | 66%nat => 603553/2^65 | w => alpha_high w
  end.

Fixpoint alpha_aux w :=
  match w with
  | 0%nat => nil
  | S n => alpha_aux n ++ (alpha_high w / alpha w) :: nil
  end.

Lemma alpha67 i : (67 <= i)%nat -> alpha i = alpha_high i.
Proof. do 67 (destruct i as [|i]; [lia|]). reflexivity. Qed.

Lemma alpha_pos_nonneg w : (0 < alpha w).
Proof. do 67 (destruct w as [|w]; simpl; try lra); unfold alpha_high; apply pow_lt; lra. Qed.

Lemma alpha_pos w : (0 <= alpha w).
Proof. apply Rlt_le. apply alpha_pos_nonneg. Qed.

Definition alpha_quot w i :=
  (alpha (w + i)) / (alpha i).

Lemma alpha_quot_spec w i :
  (i >= 67)%nat -> alpha_quot w i = alpha_high w.
Proof.
  intros. unfold alpha_quot. rewrite !alpha67 by lia. unfold alpha_high.
  rewrite div_pow. replace (w + i - i)%nat with w by lia. reflexivity. lra. lia. Qed.

(* The following couple of definitions should probably be somewhere else *)


(* Now the interesting definitions begin again *)

Definition beta_aux (w : nat) n :=
  map_seq (alpha_quot w) 0%nat n.

Definition beta w := Rmin_list (beta_aux w 68%nat).

Lemma beta_spec w :
  forall i, beta w <= alpha_quot w i.
Proof.
  intros. apply Rmin_list_spec.
  unfold beta_aux.
  destruct (le_dec i 67).
  - apply map_seq_In; lia.
  - replace (alpha_quot w i) with (alpha_quot w 67%nat).
    apply map_seq_In. lia.
    rewrite !alpha_quot_spec. reflexivity. lia. lia. Qed.

Lemma beta_spec2 w :
  exists i, beta w = alpha_quot w i.
Proof.
  epose proof Rmin_list_spec2 (map_seq (alpha_quot w) 0%nat 68%nat) _ as [x []].
  unfold beta, beta_aux. apply In_map_seq in H. rewrite H0.
  destruct H. exists x0. congruence.
  Unshelve. apply map_seq_nonnil; lia. Qed.

Lemma beta_pos w :
  0 <= beta w.
Proof.
  pose proof beta_spec2 w as [i]. rewrite H. unfold alpha_quot.
  pose proof alpha_pos (w + i).
  pose proof alpha_pos i. apply div_pos_pos; assumption. Qed.

Definition beta_quot w j :=
  beta (w + j) * 2 ^ j * 70 / 169.

Definition gamma_aux w e n :=
  map_seq (beta_quot w) e n.

Definition gamma w e := Rmin_list (gamma_aux w e 68%nat).

Definition gamma_spec w e :
  gamma w e <= beta (w + e) * 2 ^ e * 70 / 169.
Proof.
  apply Rmin_list_spec.
  unfold gamma_aux, beta_quot. left. reflexivity. Qed.

Definition gamma_spec2 w e :
  exists i, gamma w e = beta_quot w i.
Proof.
  epose proof Rmin_list_spec2 (map_seq (beta_quot w) e 68%nat) _ as [x []].
  unfold gamma, gamma_aux. apply In_map_seq in H. rewrite H0.
  destruct H. exists x0. congruence.
  Unshelve. apply map_seq_nonnil. lia. Qed.

Lemma gamma_pos w e :
  0 <= gamma w e.
Proof.
  pose proof gamma_spec2 w as [i]. rewrite H. unfold beta_quot.
  pose proof beta_pos (w + i).
  pose proof pow_le 2 i ltac:(lra). nra. Qed.

(************************************************)
(** The definition of the recursively defined S *)
(************************************************)

Inductive inS : nat -> mat -> Prop :=
| IS : inS 0%nat I
| Sc (w : nat) (P : mat) :
    forall (e : nat) (q : Z),
    inS w P ->
    (w = 0%nat) \/ (mat_norm P > beta w) ->
    mat_norm P > (gamma w e) ->
    (1 <= e)%nat ->
    Z.odd q = true ->
    (1 <= q < 2 ^+ (S e))%Z ->
    inS (e + w) (mmult (M e q) P).
