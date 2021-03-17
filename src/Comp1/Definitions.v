Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import MSets.
Require Import List.
Require Import Orders.
Require Import OrdersEx.
Require Import OrdersAlt.
From BY Require Import Q AppendixF Qmin_list.

Import ListNotations.

Require FMapAVL.
Module ZMap := FMapAVL.Make OrderedTypeEx.Z_as_OT.
Module ZZOT <: OrderedType := PairOrderedType Z_as_OT Z_as_OT.
Module ZZOTorig <: OrderedType.OrderedType := Backport_OT ZZOT.

Module ZZMap := FMapAVL.Make ZZOTorig.

Definition emptyZ := ZMap.empty.
Definition emptyZZ := ZZMap.empty.

Fixpoint add_many_aux {T:Type} f (m : ZMap.t T) n :=
  match n with
  | 0%nat => m
  | S n => add_many_aux f (ZMap.add (Z_of_nat n) (f n) m) n
  end.

Fixpoint add_many {T:Type} f n :=
  add_many_aux f (emptyZ T) n.
Definition alphaQ_high_Z w : Q := (633/1024) ^ w.

Definition init_a_map :=
  fold_right (fun n m => ZMap.add (Z_of_nat n) (alphaQ n) m) (emptyZ Q) (seq 0 68).
Definition init_q_map := emptyZZ Q.
Definition init_b_map := emptyZ Q.
Definition init_bq_map := emptyZZ Q.
Definition init_g_map := emptyZZ Q.

Definition alphaQ_mem map w :=
  match ZMap.find w map with
  | Some a => (map, a)
  | _ => let res := ((633/1024) ^ w) in
        (ZMap.add w res map, res)
  end.

Definition alphaQ_quot_mem quot_map alpha_map w i :=
  match ZZMap.find (w, i) quot_map with
  | Some a => (quot_map, alpha_map, a)
  | _ => let (alphai_map, alphai) := alphaQ_mem alpha_map i in
        let (alphawi_map, alphawi) := alphaQ_mem alphai_map (w + i)%Z in
        let res := alphawi / alphai in
        (ZZMap.add (w, i) res quot_map, alphawi_map, res)
  end.

Definition betaQ_mem_aux q_map a_map w :=
  ((fix aux q_map a_map l n := match n with
  | 0%nat => (q_map, a_map, l)
  | S n => let '(q_map, a_map, res) := alphaQ_quot_mem q_map a_map w (Z.of_nat n) in
          aux q_map a_map (l ++ [res]) n 
  end) q_map a_map [] 68%nat).

Definition betaQ_mem b_map q_map a_map w :=
  match ZMap.find w b_map with
  | Some res => (b_map, q_map, a_map, res)
  | _ => if (w <=? 67)%Z
        then let '(q_map, a_map, l) := betaQ_mem_aux q_map a_map w in
             let res := Qmin_list l in
             (ZMap.add w res b_map, q_map, a_map, res)
        else let res := ((633/1024) ^ w) * 633^5 / (2^30 * 165219) in
             (ZMap.add w res b_map, q_map, a_map, res)
  end.

Definition alphaQ_quot w i :=
  (alphaQ (w + i)) / (alphaQ i).

Definition betaQ_aux (w : nat) :=
  map_seq (alphaQ_quot w) 0%nat 68%nat.

Definition betaQ w := Qmin_list (betaQ_aux w).

Definition betaQ_quot w j :=
  betaQ (w + j) * 2 ^ (Z.of_nat j) * 70 / 169.

Definition gammaQ_aux w e :=
  map_seq (betaQ_quot w) e 68%nat.

Definition gammaQ w e := Qmin_list (gammaQ_aux w e).

(* Eval vm_compute in snd (betaQ_mem init_b_map init_q_map init_a_map 120%Z). *)
(* Eval vm_compute in betaQ 120%nat. *)
(* Time Eval vm_compute in gammaQ 0. *)


Definition betaQ_quot_mem bq_map b_map q_map a_map w j :=
  match ZZMap.find (w, j) bq_map with
  | Some b => (bq_map, b_map, q_map, a_map, b)
  | _ => let '(b_map, q_map, a_map, bwj) := betaQ_mem b_map q_map a_map (w + j)%Z in
        let res := bwj * 2^j * 70 / 169 in
        (ZZMap.add (w, j) res bq_map, b_map, q_map, a_map, res)
  end.

Definition gammaQ_mem_aux bq_map b_map q_map a_map w e :=
  (fix aux bq_map b_map q_map a_map l n := match n with
  | 0%nat => (bq_map, b_map, q_map, a_map, l)
  | S n => let '(bq_map, b_map, q_map, a_map, res) := betaQ_quot_mem bq_map b_map q_map a_map w ((Z.of_nat n) + e) in
          aux bq_map b_map q_map a_map (l ++ [res]) n 
  end) bq_map b_map q_map a_map [] 67%nat.

(* Eval vm_compute in snd (gammaQ_mem_aux init_bq_map init_b_map init_q_map init_a_map 2 2). *)

Definition gammaQ_mem g_map bq_map b_map q_map a_map w e :=
  match ZZMap.find (w, e) g_map with
  | Some a => (g_map, bq_map, b_map, q_map, a_map, a)
  | _ => if (w <=? 67)%Z
        then let '(bq_map, b_map, q_map, a_map, l) := gammaQ_mem_aux bq_map b_map q_map a_map w e in
             let res := Qmin_list l in
             (ZZMap.add (w, e) res g_map, bq_map, b_map, q_map, a_map, res)
        else let res := 2 ^ e * ((633/1024) ^ (w + e)) * (70/169) * 633^5 / (2^30 * 165219) in
             (ZZMap.add (w, e) res g_map, bq_map, b_map, q_map, a_map, res)
  end.  

Time Eval vm_compute in snd (gammaQ_mem init_g_map init_bq_map init_b_map init_q_map init_a_map 50 50).

(* Inductive inS : nat -> mat -> Prop := *)
(* | IS : inS 0%nat I *)
(* | Sc (w : nat) (P : mat) : *)
(*     forall (e : nat) (q : Z), *)
(*     inS w P -> *)
(*     (w = 0%nat) \/ (mat_norm P > beta w) -> *)
(*     mat_norm P > (gamma w e) -> *)
(*     (1 <= e)%nat -> *)
(*     Z.odd q = true -> *)
(*     (1 <= q < 2 ^+ (S e))%Z -> *)
(*     inS (w + e) (mmult (M e q) P). *)

(* Theorem F22 : (forall w P, inS w P -> mat_norm P <= alpha w). Admitted. *)
