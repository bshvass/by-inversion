Require Import Bignums.BigQ.BigQ.
Require Import Bignums.BigZ.BigZ.

Require Import ZArith.
Require Import MSets.
Require Import List.
Require Import Orders.
Require Import OrdersEx.
Require Import OrdersAlt.

From BY Require Import AppendixF MatrixBigQ.

Local Open Scope bigQ.

Definition alpha_high (w : Z) : bigQ := (633/1024) ^ w.

Definition alpha (w : nat) : bigQ :=
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
  | 64%nat => 404341/2^63 | 65%nat => 986633/2^65 | 66%nat => 603553/2^65 | w => alpha_high (Z.of_nat w)
  end.

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

Definition init_a_map :=
  fold_right (fun n m => ZMap.add (Z_of_nat n) (alpha n) m) (emptyZ bigQ) (seq 0 68).
Definition init_q_map := emptyZZ bigQ.
Definition init_b_map := emptyZ bigQ.
Definition init_bq_map := emptyZZ bigQ.
Definition init_g_map := emptyZZ bigQ.

Definition alpha_mem map w :=
  match ZMap.find w map with
  | Some a => (map, a)
  | _ => let res := ((633/1024) ^ w) in
        (ZMap.add w res map, res)
  end.

Definition alpha_quot_mem aq_map a_map w i :=
  match ZZMap.find (w, i) aq_map with
  | Some a => (aq_map, a_map, a)
  | _ => let (alphai_map, alphai) := alpha_mem a_map i in
        let (alphawi_map, alphawi) := alpha_mem alphai_map (w + i)%Z in
        let res := alphawi / alphai in
        (ZZMap.add (w, i) res aq_map, alphawi_map, res)
  end.

Definition beta_mem_aux aq_map a_map w :=
  ((fix aux q_map a_map l n := match n with
  | 0%nat => (q_map, a_map, l)
  | S n => let '(q_map, a_map, res) := alpha_quot_mem q_map a_map w (Z.of_nat n) in
          aux q_map a_map (l ++ [res]) n 
  end) aq_map a_map [] 68%nat).

Fixpoint min_list l : bigQ :=
  match l with
  | nil => 0
  | a :: l0 => match l0 with
            | nil => a
            | _ => BigQ.min a (min_list l0)
            end
  end.

Definition beta_mem b_map aq_map a_map w :=
  match ZMap.find w b_map with
  | Some res => (b_map, aq_map, a_map, res)
  | _ => if (w <=? 67)%Z
        then let '(q_map, a_map, l) := beta_mem_aux aq_map a_map w in
             let res := min_list l in
             (ZMap.add w res b_map, q_map, a_map, res)
        else let res := ((633/1024) ^ w) * 633^5 / (2^30 * 165219) in
             (ZMap.add w res b_map, aq_map, a_map, res)
  end.

Definition alpha_quot w i :=
  (alpha (w + i)) / (alpha i).

Definition beta_aux (w : nat) :=
  map_seq (alpha_quot w) 0%nat 68%nat.

Definition beta w : bigQ := min_list (beta_aux w).

Definition beta_quot w j :=
  beta (w + j) * 2 ^ (Z.of_nat j) * 70 / 169.

Definition gamma_aux w e :=
  map_seq (beta_quot w) e 68%nat.

Definition gamma w e : bigQ := min_list (gamma_aux w e).

(* Eval vm_compute in snd (beta_mem init_b_map init_q_map init_a_map 120%Z). *)
(* Eval vm_compute in beta 120%nat. *)
(* Eval vm_compute in (snd (beta_mem init_b_map init_q_map init_a_map 120%Z)) ?= (beta 120%nat). *)

Definition beta_quot_mem bq_map b_map aq_map a_map w j :=
  match ZZMap.find (w, j) bq_map with
  | Some b => (bq_map, b_map, aq_map, a_map, b)
  | _ => let '(b_map, aq_map, a_map, bwj) := beta_mem b_map aq_map a_map (w + j)%Z in
        let res := bwj * 2^j * 70 / 169 in
        (ZZMap.add (w, j) res bq_map, b_map, aq_map, a_map, res)
  end.

Definition gamma_mem_aux bq_map b_map q_map a_map w e :=
  (fix aux bq_map b_map q_map a_map l n := match n with
  | 0%nat => (bq_map, b_map, q_map, a_map, l)
  | S n => let '(bq_map, b_map, q_map, a_map, res) := beta_quot_mem bq_map b_map q_map a_map w ((Z.of_nat n) + e) in
          aux bq_map b_map q_map a_map (l ++ [res]) n 
  end) bq_map b_map q_map a_map [] 67%nat.

(* Eval vm_compute in snd (gammaQ_mem_aux init_bq_map init_b_map init_q_map init_a_map 2 2). *)

Definition gamma_mem g_map bq_map b_map aq_map a_map w e :=
  match ZZMap.find (w, e) g_map with
  | Some a => (g_map, bq_map, b_map, aq_map, a_map, a)
  | _ => if (w <=? 67)%Z
        then let '(bq_map, b_map, aq_map, a_map, l) := gamma_mem_aux bq_map b_map aq_map a_map w e in
             let res := min_list l in
             (ZZMap.add (w, e) res g_map, bq_map, b_map, aq_map, a_map, res)
        else let res := 2 ^ e * ((633/1024) ^ (w + e)) * (70/169) * 633^5 / (2^30 * 165219) in
             (ZZMap.add (w, e) res g_map, bq_map, b_map, aq_map, a_map, res)
  end.

Definition alpha_mem_test w := snd (alpha_mem init_a_map w).
Definition beta_mem_test w := snd (beta_mem init_b_map init_q_map init_a_map w).
Definition gamma_mem_test w e := snd (gamma_mem init_g_map init_bq_map init_b_map init_q_map init_a_map w e).

(* Time Eval vm_compute in snd (gamma_mem init_g_map init_bq_map init_b_map init_q_map init_a_map 50 50). *)
(* Time Eval vm_compute in gamma 50 60. *)
(* Time Eval vm_compute in snd (gamma_mem init_g_map init_bq_map init_b_map init_q_map init_a_map 50 50) ?= gamma 50 50. *)

Local Open Scope mat_scope.
(* Local Coercion (fun n => n # 1) : bigZ >-> bigQ. *)

Definition M (e : Z) (q : bigZ) := [ 0 , 1 / (2 ^ e) ; - 1 / (2 ^ e) , (q # 1) / (2 ^ (2 * e)%Z) ].

Definition scaledM (e : Z) (q : bigZ) := [ 0 , 2 ^ e ; - (2 ^ e) , q # 1 ].

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
  let '(a_map, alpha_w) := alpha_mem a_map w in
  let '(b_map, aq_map, a_map, beta_w) := beta_mem b_map aq_map a_map w in
  if (0 <? w)%Z && has_at_most_norm mm (4^w * beta_w)
  then Some (c, 1)
  else if negb (has_at_most_norm mm (4^w * alpha_w))
       then None
       else
         match fuel with
         | 0%nat => None
         | S fuel =>
           let '(g_map, bq_map, b_map, aq_map, a_map, gamma_w_e) := gamma_mem g_map bq_map b_map aq_map a_map w e in
           if has_at_most_norm mm (4^w * gamma_w_e)
           then Some (c, 2)
           else children_aux m
                             (((fix aux c n := match n with
                                               | 0%nat => c
                                               | S n =>
                                                 let bign := N.of_nat n in
                                                 let q := (2 * bign + 1)%N in ((e + w)%Z, mmult (scaledM e (BigZ_of_N q)) m) :: aux c n
                                               end) [] (Z.to_nat (2 ^ e))) ++  c)
                             w (e + 1)%Z fuel a_map b_map g_map bq_map aq_map
         end.

Fixpoint depth_first_verify_aux m (nodes w : Z) fuel a_map b_map g_map bq_map aq_map (max_nodes : Z) :=
  let mm := mmult (mtrans m) m in
  let '(a_map, alpha_w) := alpha_mem a_map w in
  let '(b_map, aq_map, a_map, beta_w) := beta_mem b_map aq_map a_map w in  
  if negb (has_at_most_norm mm ((4^w) * alpha_w)) then None
  else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * beta_w)
       then Some (a_map, b_map, g_map, bq_map, aq_map, nodes, max_nodes)
       else (fix inner_loop e nodes fuel a_map b_map g_map bq_map aq_map max_nodes :=
               let b := (max_nodes <? nodes)%Z in (* 100million *)
               let max_nodes := if b then nodes else max_nodes in               
               match fuel with
               | 0%nat => None
               | S fuel => let '(g_map, bq_map, b_map, aq_map, a_map, gamma_w_e) := gamma_mem g_map bq_map b_map aq_map a_map w e in
                          if has_at_most_norm mm ((4^w) * gamma_w_e)
                          then Some (a_map, b_map, g_map, bq_map, aq_map, nodes, max_nodes)
                          else match
                              (fix verify_children cnodes a_map b_map g_map bq_map aq_map n max_nodes :=
                                  match n with
                                  | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes, max_nodes)
                                  | S n =>
                                    let bign := N.of_nat n in
                                    let q := ((2 * bign) + 1)%N in
                                          match
                                            depth_first_verify_aux (mmult (scaledM e (BigZ_of_N q)) m) 1 (e + w)%Z fuel a_map b_map g_map bq_map aq_map max_nodes with
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
  match depth_first_verify_aux I 1 0 100 init_a_map init_b_map init_g_map init_bq_map init_q_map 1 with None => (-1)%Z | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) => nodes end.

(* Time Eval vm_compute in depth_first_verify. *)
