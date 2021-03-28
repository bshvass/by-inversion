Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import MSets.
Require Import List.
Require Import Orders.
Require Import OrdersEx.
Require Import OrdersAlt.
From BY Require Import Q AppendixF Qmin_list MatrixQ.

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

Definition alphaQ_mem_test w := snd (alphaQ_mem init_a_map w).
Definition betaQ_mem_test w := snd (betaQ_mem init_b_map init_q_map init_a_map w).
Definition gammaQ_mem_test w e := snd (gammaQ_mem init_g_map init_bq_map init_b_map init_q_map init_a_map w e).

Time Eval vm_compute in snd (gammaQ_mem init_g_map init_bq_map init_b_map init_q_map init_a_map 50 50).

Local Open Scope mat_scope.

Local Coercion inject_Z : Z >-> Q.

Definition M (e q : Z) := [ 0 , 1 / (2 ^ e) ; - 1 / (2 ^ e) , q / (2 ^ (2 * e)) ]%Q.

Definition scaledM (e q : Z) := [ 0 , 2 ^ e ; - (2 ^ e) , inject_Z q ]%Q.

Notation "a <=? b" := (match a ?= b with Gt => false | _ => true end).
Notation "a <? b" := (match a ?= b with Lt => true | _ => false end).
Notation "a =? b" := (match a ?= b with Eq => true | _ => false end).

Definition has_at_most_norm (P : mat) N :=
  let '(a, b, c, d) := P in
  let X := (2 * N ^ 2 - a - d) in
  (0 <=? X) && ((a - d) ^ 2 + 4 * b ^ 2 <=? X ^ 2).

Definition has_at_most_norm_new (P : mat) N :=
  let '(P11, P12, P21, P22) := P in
  let a := P11 ^ 2 + P21 ^ 2 in
  let b := P11 * P21 + P12 * P22 in
  let c := P11 * P21 + P12 * P22 in
  let d := P12 ^ 2 + P22 ^ 2 in
  let X := (2 * N ^ 2 - a - d) in
  (0 <=? X) && ((a - d) ^ 2 + 4 * b ^ 2 <=? X ^ 2).

Fixpoint children_aux m c w e fuel a_map b_map g_map bq_map aq_map :=
  let mm := mmult (mtrans m) m in
  let '(a_map, alpha_w) := alphaQ_mem a_map w in
  let '(b_map, aq_map, a_map, beta_w) := betaQ_mem b_map aq_map a_map w in
  if (0 <? w) && has_at_most_norm mm (4^w * beta_w)
  then Some (c, 1)
  else if negb (has_at_most_norm mm (4^w * alpha_w))
       then None
       else
         match fuel with
         | 0%nat => None
         | S fuel =>
           let '(g_map, bq_map, b_map, aq_map, a_map, gamma_w_e) := gammaQ_mem g_map bq_map b_map aq_map a_map w e in
           if has_at_most_norm mm (4^w * gamma_w_e)
           then Some (c, 2)
           else children_aux m
                             (((fix aux c n := match n with
                                               | 0%nat => c
                                               | S n => let q := (2 * n + 1)%nat in (e+w, mmult (scaledM e (Z.of_nat q)) m) :: aux c n
                                               end) [] (Z.to_nat (2 ^ e))) ++  c)
                             w (e + 1)%Z fuel a_map b_map g_map bq_map aq_map
         end.

Fixpoint depth_first_verify_aux m (nodes w : Z) fuel a_map b_map g_map bq_map aq_map (max_nodes : Z) :=
  let mm := mmult (mtrans m) m in
  let '(a_map, alpha_w) := alphaQ_mem a_map w in
  let '(b_map, aq_map, a_map, beta_w) := betaQ_mem b_map aq_map a_map w in  
  if negb (has_at_most_norm mm ((4^w) * alpha_w)) then None
  else if (0 <? w) && has_at_most_norm mm ((4^w) * beta_w)
       then Some (a_map, b_map, g_map, bq_map, aq_map, nodes, max_nodes)
       else (fix inner_loop e nodes fuel a_map b_map g_map bq_map aq_map max_nodes :=
               let b := (max_nodes <? nodes)%Z in (* 100million *)
               let max_nodes := if b then nodes else max_nodes in               
               match fuel with
               | 0%nat => None
               | S fuel => let '(g_map, bq_map, b_map, aq_map, a_map, gamma_w_e) := gammaQ_mem g_map bq_map b_map aq_map a_map w e in
                          if has_at_most_norm mm ((4^w) * gamma_w_e)
                          then Some (a_map, b_map, g_map, bq_map, aq_map, nodes, max_nodes)
                          else match
                              (fix verify_children cnodes a_map b_map g_map bq_map aq_map n max_nodes :=
                                  match n with
                                  | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes, max_nodes)
                                  | S n => let q := ((2 * n) + 1)%nat in
                                          match
                                            depth_first_verify_aux (mmult (scaledM e (Z.of_nat q)) m) 1 (e + w)%Z fuel a_map b_map g_map bq_map aq_map max_nodes with
                                          | None => None
                                          | Some (a_map, b_map, g_map, bq_map, aq_map, nodes, max_nodes) =>
                                            verify_children (nodes + cnodes)%Z a_map b_map g_map bq_map aq_map n max_nodes
                                          end
                                  end) 0%Z a_map b_map g_map bq_map aq_map (Z.to_nat (2 ^ e)) max_nodes with
                              | None => None
                              | Some (a_map, b_map, g_map, bq_map, aq_map, cnodes, max_nodes) =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel a_map b_map g_map bq_map aq_map max_nodes
                            end
               end) 1%Z nodes fuel a_map b_map g_map bq_map aq_map max_nodes.

Definition children m w fuel :=
  children_aux m [] w 1 fuel init_a_map init_b_map init_g_map init_bq_map init_q_map.

Definition depth_first_verify :=
  match depth_first_verify_aux I 1 0 1000 init_a_map init_b_map init_g_map init_bq_map init_q_map 1 with None => (-1)%Z | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) => nodes end.

Extraction "definitions" depth_first_verify.

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
