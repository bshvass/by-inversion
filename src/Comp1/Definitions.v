Require Import ZArith micromega.Lia.
Require Import micromega.Lra.
Require Import micromega.Lqa.
Require Import List.
Require Import QArith.
Require Import Qpower.
Require Import MSets.
Require Import List.
Require Import Orders.
Require Import OrdersEx.
Require Import OrdersAlt.
From BY Require Import Q AppendixF Qmin_list Impl MatrixQ Zpower_nat.

(* From RecordUpdate Require Import RecordSet. *)

(* Import ListNotations. *)

(* Definition init_data := Build_data init_amap init_aqmap init_bmap init_bqmap init_gmap. *)


(* Set Implicit Arguments. *)
(* Set Strict Implicit. *)

(* Class Monad (m : Type -> Type) : Type := *)
(* { ret : forall {t : Type}, t -> m t *)
(* ; bind : forall {t u : Type}, m t -> (t -> m u) -> m u *)
(* }. *)

(* Definition liftM *)
(*            {m : Type -> Type} *)
(*            {M : Monad m} *)
(*            {T U : Type} (f : T -> U) : m T -> m U := *)
(*   fun x => bind x (fun x => ret (f x)). *)

(* Definition liftM2 *)
(*            {m : Type -> Type} *)
(*            {M : Monad m} *)
(*            {T U V : Type} (f : T -> U -> V) : m T -> m U -> m V := *)
(*   Eval cbv beta iota zeta delta [ liftM ] in *)
(*     fun x y => bind x (fun x => liftM (f x) y). *)

(* Definition liftM3 *)
(*            {m : Type -> Type} *)
(*            {M : Monad m} *)
(*            {T U V W : Type} (f : T -> U -> V -> W) : m T -> m U -> m V -> m W := *)
(*   Eval cbv beta iota zeta delta [ liftM2 ] in *)
(*     fun x y z => bind x (fun x => liftM2 (f x) y z). *)

(* Definition apM@{d c} *)
(*            {m : Type@{d} -> Type@{c}} *)
(*            {M : Monad m} *)
(*            {A B : Type@{d}} (fM:m (A -> B)) (aM:m A) : m B := *)
(*   bind fM (fun f => liftM f aM). *)

(* (* Left-to-right composition of Kleisli arrows. *) *)
(* Definition mcompose@{c d} *)
(*            {m:Type@{d}->Type@{c}} *)
(*            {M: Monad m} *)
(*            {T U V:Type@{d}} *)
(*            (f: T -> m U) (g: U -> m V): (T -> m V) := *)
(*   fun x => bind (f x) g. *)

(* Definition join@{d c} {m : Type@{d} -> Type@{c}} {a} `{Monad m} : m (m a) -> m a := *)
(*   fun x => bind x (fun y => y). *)

(* Declare Scope monad_scope. *)
(* Delimit Scope monad_scope with monad. *)

(* Module MonadBaseNotation. *)



(*   Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope. *)
(*   (* Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 61, right associativity) : monad_scope. *) *)

(*   Notation "e1 ;; e2" := (@bind _ _ _ _ e1%monad (fun _ => e2%monad))%monad *)
(*     (at level 61, right associativity) : monad_scope. *)

(* End MonadBaseNotation. *)

(* Module MonadNotation. *)

(*   Export MonadBaseNotation. *)

(*   Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2)) *)
(*     (at level 61, c1 at next level, right associativity) : monad_scope. *)

(*   Notation "' pat <- c1 ;; c2" := *)
(*     (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end)) *)
(*     (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope. *)

(* End MonadNotation. *)

(* Module MonadLetNotation. *)

(*   Export MonadBaseNotation. *)

(*   Notation "'let*' p ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun p => c2)) *)
(*     (at level 61, p as pattern, c1 at next level, right associativity) : monad_scope. *)

(* End MonadLetNotation. *)

(* (* Definition State S A := *) *)
(* (*   S -> (A * S). *) *)
(* (* Definition State_ret {S A} (a : A) : State S A := fun s => (a, s). *) *)
(* (* Definition State_bind {S A B} (sa : State S A) (f : A -> State S B) : State S B := *) *)
(* (*   fun r => let (a, s) := sa r in (f a) s. *) *)

(* (* Instance State_monad : State monad. *) *)

(* (* Notation "c >>= f" := (State_bind c f) (at level 50, left associativity). *) *)
(* (* Notation "x <- c1 ; c2" := (c1 >>= (fun x => c2)) *) *)
(* (*     (at level 61, c1 at next level, right associativity). *) *)
(* (* Notation "c1 ;; c2" := (c1 >>= (fun _ => c2)) (at level 61). *) *)

(* Set Implicit Arguments. *)
(* Set Strict Implicit. *)

(* Record state {S} (t : Type) : Type := *)
(*   mkState *)
(*     { runState : S -> t * S }. *)

(* Definition evalState {S t} (c : state t) (s : S) : t := *)
(*   fst (runState c s). *)

(* Definition execState {S t} (c : state t) (s : S) : S := *)
(*   snd (runState c s). *)

(* Definition state_ret {S t} := fun v : t => mkState (fun s : S => (v, s)). *)
(* Definition state_bind {S t r} := fun (c1 : state t) (c2 : t -> state r) => *)
(*                                  mkState (fun s : S => let *)
(*                                               (v,s) := runState c1 s in *)
(*                                             runState (c2 v) s). *)

(* Definition state_get {S} := mkState (fun x : S => (x, x)). *)
(* Definition state_put {S} := fun (s : S) => mkState (fun _ => (tt, s)). *)

(* Definition option_ret {A} (x : A) : option A := Some x. *)
(* Definition option_bind {A B} (m : option A) (f : A -> option B) : option B := *)
(* match m with *)
(* | Some x => f x *)
(* | None => None *)
(* end. *)

(* (* We can use the do-notation. *)
(*    Reminiscent of imperative programming. *) *)
(* (* Notation "c >>= f" := (option_bind c f) (at level 50, left associativity). *) *)
(* (* Notation "x <- c1 ;; c2" := (option_bind c1 (fun x => c2)) *) *)
(*     (* (at level 61, c1 at next level, right associativity). *) *)

(* Global Instance Monad_option : Monad option := *)
(*   { *)
(*     ret := @Some *)
(*     ; bind := fun _ _ c1 c2 => match c1 with *)
(*                             | None => None *)
(*                             | Some v => c2 v *)
(*                             end *)
(* }. *)

(* Global Instance Monad_state {S} : Monad state := *)
(*   { ret  := fun _ v => mkState (fun s : S => (v, s)) *)
(*   ; bind := fun _ _ c1 c2 => *)
(*     mkState (fun s => *)
(*       let (v,s) := runState c1 s in *)
(*       runState (c2 v) s) *)
(*   }. *)

(* Import MonadNotation. *)

(* (* Definition ZS := state Z. *) *)

(* Local Open Scope monad_scope. *)

(* Definition test (a : option Z) : option Z := *)
(*   a ;; a. *)

(* Definition alphaQ_mem w := *)
(*   s1 <- state_get ;; *)
(*      match ZMap.find w (amap s1) with *)
(*      | Some a => ret a *)
(*      | None => *)
(*        let aw := alphaQ w in *)
(*        state_put ( *)
(*        ret (alphaQ w) *)
(*      end. *)

(* Definition init_a_map := emptyZ Q. *)
(* Definition init_aq_map := emptyZZ Q. *)
(* Definition init_b_map := emptyZ Q. *)
(* Definition init_bq_map := emptyZZ Q. *)
(* Definition init_g_map := emptyZZ Q. *)





(* Add Relation (list Q) Qlist_eq reflexivity proved by Qlist_eq_refl symmetry proved by Qlist_eq_sym transitivity proved by Qlist_eq_trans as Qlist_eq_rel. *)


Definition alphaQ_mem_test w := snd (alphaQ_mem init_a_map w).
Definition betaQ_mem_test w := snd (betaQ_mem init_b_map init_aq_map init_a_map w).
Definition gammaQ_mem_test w e := snd (gammaQ_mem init_g_map init_bq_map init_b_map init_aq_map init_a_map w e).

Time Eval vm_compute in snd (gammaQ_mem init_g_map init_bq_map init_b_map init_aq_map init_a_map 50 50).
(* Time Eval vm_compute in snd (gammaQ_mem init_g_map init_bq_map init_b_map init_aq_map init_a_map 0 1). *)

(* Ltac replace_mem := *)
(*   match goal with *)
(*          | [ |- context[alphaQ_mem ?a_map ?w] ] => *)
(*            pose proof alphaQ_mem_spec a_map ltac:(assumption) w ltac:(lia); split_pairs *)
(*          | [ H : alphaQ_mem ?a_map ?w = (_, _) |- _ ] => *)
(*            let H1 := fresh in *)
(*            pose proof alphaQ_mem_spec a_map ltac:(assumption) w ltac:(lia) as H1; split_pairs; clear H; clear H1 *)
(*          | [ H : betaQ_mem_aux ?aq_map ?a_map ?w ?l ?n = _ |- _ ] => *)
(*            let H1 := fresh in *)
(*            apply betaQ_mem_aux_spec in H *)
(*            pose proof betaQ_mem_aux_spec aq_map a_map n l *)
(*                 ltac:(assumption) ltac:(assumption)  *)
(*                                          w ltac:(lia) as H1; split_pairs; clear H; clear H1 *)
(*   end. *)


(* Lemma gammaQ_0_1 : (gammaQ 0 1 == 129524113080320 # 277078859579392)%Q. *)
(* Proof. *)
(*   epose proof gammaQ_mem_spec init_g_map init_bq_map init_b_map init_aq_map init_a_map _ _ _ _ _ 0 1 ltac:(lia) ltac:(lia). *)
(*   split_pairs. *)
(*   apply (f_equal snd) in H0. *)
(*   change (Z.to_nat 0) with 0%nat in H9.  *)
(*   change (Z.to_nat 1) with 1%nat in H9. *)
(*   rewrite <- H9. *)
(*   cbn [snd] in H0. *)
(*   rewrite <- H0. *)

(*   vm_cast_no_check (Qeq_refl (129524113080320 # 277078859579392)). *)
(*   Unshelve. all: auto with init_correct. *)
(* Qed. *)

Local Open Scope mat_scope.




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

Fixpoint depth_first_verify_aux m (nodes w : Z) fuel a_map b_map g_map bq_map aq_map :=
  let mm := mmult (mtrans m) m in
  let '(a_map, alpha_w) := alphaQ_mem a_map w in
  let '(b_map, aq_map, a_map, beta_w) := betaQ_mem b_map aq_map a_map w in
  if negb (has_at_most_norm mm ((4^w) * alpha_w)) then None
  else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * beta_w)
       then Some (a_map, b_map, g_map, bq_map, aq_map, nodes)
       else (fix inner_loop e nodes fuel a_map b_map g_map bq_map aq_map :=
               match fuel with
               | 0%nat => None
               | S fuel => let '(g_map, bq_map, b_map, aq_map, a_map, gamma_w_e) := gammaQ_mem g_map bq_map b_map aq_map a_map w e in
                          if has_at_most_norm mm ((4^w) * gamma_w_e)
                          then Some (a_map, b_map, g_map, bq_map, aq_map, nodes)
                          else match
                              (fix verify_children cnodes a_map b_map g_map bq_map aq_map n :=
                                  match n with
                                  | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes)
                                  | S n => let q := ((2 * n) + 1)%nat in
                                          match
                                            depth_first_verify_aux (mmult (scaledM e (Z.of_nat q)) m) 1 (e + w)%Z fuel a_map b_map g_map bq_map aq_map with
                                          | None => None
                                          | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) =>
                                            verify_children (nodes + cnodes)%Z a_map b_map g_map bq_map aq_map n
                                          end
                                  end) 0%Z a_map b_map g_map bq_map aq_map (Z.to_nat (2 ^ e)) with
                              | None => None
                              | Some (a_map, b_map, g_map, bq_map, aq_map, cnodes) =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel a_map b_map g_map bq_map aq_map
                            end
               end) 1%Z nodes fuel a_map b_map g_map bq_map aq_map.

Fixpoint depth_first_verify_aux_two_fuel m (nodes w : Z) inner_fuel outer_fuel a_map b_map g_map bq_map aq_map :=
  match outer_fuel with
  | 0%nat => None
  | S outer_fuel =>
    let mm := mmult (mtrans m) m in
    let '(a_map, alpha_w) := alphaQ_mem a_map w in
    let '(b_map, aq_map, a_map, beta_w) := betaQ_mem b_map aq_map a_map w in
    if negb (has_at_most_norm mm ((4^w) * alpha_w)) then None
    else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * beta_w)
         then Some (a_map, b_map, g_map, bq_map, aq_map, nodes)
         else (fix inner_loop e nodes fuel a_map b_map g_map bq_map aq_map :=
                 match fuel with
                 | 0%nat => None
                 | S fuel => let '(g_map, bq_map, b_map, aq_map, a_map, gamma_w_e) := gammaQ_mem g_map bq_map b_map aq_map a_map w e in
                            if has_at_most_norm mm ((4^w) * gamma_w_e)
                            then Some (a_map, b_map, g_map, bq_map, aq_map, nodes)
                            else match
                                (fix verify_children cnodes a_map b_map g_map bq_map aq_map n :=
                                   match n with
                                   | 0%nat => Some (a_map, b_map, g_map, bq_map, aq_map, cnodes)
                                   | S n => let q := ((2 * n) + 1)%nat in
                                           match
                                             depth_first_verify_aux_two_fuel (mmult (scaledM e (Z.of_nat q)) m) 1 (e + w)%Z inner_fuel outer_fuel a_map b_map g_map bq_map aq_map with
                                           | None => None
                                           | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) =>
                                             verify_children (nodes + cnodes)%Z a_map b_map g_map bq_map aq_map n
                                           end
                                   end) 0%Z a_map b_map g_map bq_map aq_map (Z.to_nat (2 ^ e)) with
                              | None => None
                              | Some (a_map, b_map, g_map, bq_map, aq_map, cnodes) =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel a_map b_map g_map bq_map aq_map
                              end
                 end) 1%Z nodes inner_fuel a_map b_map g_map bq_map aq_map
  end.


Fixpoint depth_first_verify_aux_no_mem m (nodes w : Z) fuel :=
  let mm := mmult (mtrans m) m in
  if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None
  else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w))
       then Some nodes
       else (fix inner_loop e nodes fuel :=
               match fuel with
               | 0%nat => None
               | S fuel => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e)))
                          then Some nodes
                          else match
                              (fix verify_children cnodes n :=
                                  match n with
                                  | 0%nat => Some cnodes
                                  | S n => let q := ((2 * n) + 1)%nat in
                                          match
                                            depth_first_verify_aux_no_mem (mmult (scaledM e (Z.of_nat q)) m) 1 (e + w)%Z fuel with
                                          | None => None
                                          | Some nodes =>
                                            verify_children (nodes + cnodes)%Z n
                                          end
                                  end) 0%Z (Z.to_nat (2 ^ e)) with
                              | None => None
                              | Some cnodes =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel
                            end
               end) 1%Z nodes fuel.

Fixpoint depth_first_verify_aux_no_mem_two_fuel m (nodes w : Z) inner_fuel outer_fuel :=
  match outer_fuel with
  | 0%nat => None
  | S outer_fuel =>
    let mm := mmult (mtrans m) m in
    if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None
    else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w))
         then Some nodes
         else (fix inner_loop e nodes fuel :=
                 match fuel with
                 | 0%nat => None
                 | S fuel => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e)))
                            then Some nodes
                            else match
                                (fix verify_children cnodes n :=
                                   match n with
                                   | 0%nat => Some cnodes
                                   | S n => let q := ((2 * n) + 1)%nat in
                                           match
                                             depth_first_verify_aux_no_mem_two_fuel (mmult (scaledM e (Z.of_nat q)) m) 1 (e + w)%Z inner_fuel outer_fuel with
                                           | None => None
                                           | Some nodes =>
                                             verify_children (nodes + cnodes)%Z n
                                           end
                                   end) 0%Z (Z.to_nat (2 ^ e)) with
                              | None => None
                              | Some cnodes =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel
                              end
                 end) 1%Z nodes inner_fuel
  end.

Fixpoint depth_first_verify_aux_no_mem_three_fuel m (nodes w : Z) fuel1 fuel2 fuel3 :=
  match fuel1 with
  | 0%nat => None
  | S fuel1 =>
    let mm := mmult (mtrans m) m in
    if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None
    else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w))
         then Some nodes
         else (fix inner_loop e nodes fuel2 :=
                 match fuel2 with
                 | 0%nat => None
                 | S fuel2 => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e)))
                            then Some nodes
                            else match
                                (fix verify_children cnodes fuel3 :=
                                   match fuel3 with
                                   | 0%nat => Some cnodes
                                   | S fuel3 => let q := ((2 * fuel3) + 1)%nat in
                                           match
                                             depth_first_verify_aux_no_mem_three_fuel (mmult (scaledM e (Z.of_nat q)) m) 1 (e + w)%Z fuel1 fuel2 fuel3 with
                                           | None => None
                                           | Some nodes =>
                                             verify_children (nodes + cnodes)%Z fuel3
                                           end
                                   end) 0%Z fuel3 with
                              | None => None
                              | Some cnodes =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel2
                              end
                 end) 1%Z nodes fuel2
  end.

Fixpoint depth_first_verify_aux_no_mem_three_fuel_gen m (nodes nodes0 cnodes0 w e0 : Z) fuel1 fuel2 fuel3 :=
  match fuel1 with
  | 0%nat => None
  | S fuel1 =>
    let mm := mmult (mtrans m) m in
    if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None
    else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w))
         then Some nodes
         else (fix inner_loop e nodes fuel2 :=
                 match fuel2 with
                 | 0%nat => None
                 | S fuel2 => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e)))
                            then Some nodes
                            else match
                                (fix verify_children cnodes fuel4 :=
                                   match fuel4 with
                                   | 0%nat => Some cnodes
                                   | S fuel4 => let q := ((2 * fuel4) + 1)%nat in
                                           match
                                             depth_first_verify_aux_no_mem_three_fuel_gen (mmult (scaledM e (Z.of_nat q)) m) nodes0 nodes0 cnodes0 (e + w)%Z e0 fuel1 fuel2 fuel3 with
                                           | None => None
                                           | Some nodes =>
                                             verify_children (nodes + cnodes)%Z fuel4
                                           end
                                   end) cnodes0 fuel3 with
                              | None => None
                              | Some cnodes =>
                                inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel2
                              end
                 end) e0 nodes fuel2
  end.


(* Fixpoint verify_children m nodes w fuel e cnodes n := *)
(*   match n with *)
(*   | 0%nat => Some cnodes *)
(*   | S n => let q := ((2 * n) + 1)%nat in *)
(*           match *)
(*             depth_first_verify_aux_no_mem (mmult (scaledM e (Z.of_nat q)) m) 1 (e + w)%Z fuel with *)
(*           | None => None *)
(*           | Some nodes => *)
(*             verify_children m nodes w fuel e (nodes + cnodes)%Z n *)
(*           end *)
(*   end. *)

(* Lemma lemma m nodes w fuel : *)
(*   depth_first_verify_aux_no_mem m nodes w fuel = *)
(*   let mm := mmult (mtrans m) m in *)
(*   if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None *)
(*   else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w)) *)
(*        then Some nodes *)
(*        else (fix inner_loop e nodes fuel := *)
(*                match fuel with *)
(*                | 0%nat => None *)
(*                | S fuel => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) *)

(*                           then Some nodes *)
(*                           else match *)
(*                               verify_children m nodes w fuel e 0%Z (Z.to_nat (2 ^ e)) with *)
(*                               | None => None *)
(*                               | Some cnodes => *)
(*                                 inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel  *)
(*                             end *)
(*                end) 1%Z nodes fuel.   *)
(* Proof. induction fuel. *)
(*        reflexivity. *)
(*        simpl. reflexivity. *)
(*        cbn. reflexivity. *)

(* Lemma children_none m nodes w fuel e cnodes n : (exists q, Z.odd q = true /\ (1 <= q < 2 ^ (e + 1))%Z /\ *)
(*                                                      verify_children m nodes w (S fuel) e cnodes n = None) -> *)
(*                                                      depth_first_verify_aux_no_mem m nodes w (S fuel) = None. *)
(* Proof. *)
(*   intros. destruct H as [q [H [H0]]]. *)

(*   simpl. *)
(*   destruct fuel. simpl. *)
(*   unfold depth_first_verify_aux. *)



Lemma mem_no_mem_three_fuel m nodes w inner_fuel outer_fuel :
  (0 < w)%Z ->
  match depth_first_verify_aux_two_fuel m nodes w inner_fuel outer_fuel a_map b_map g_map bq_map aq_map with
  | Some (maps,nodes) => Some nodes
  | None => None
  end =
  depth_first_verify_aux_no_mem_two_fuel m nodes w inner_fuel outer_fuel.
Proof.
  induction inner_fuel; induction outer_fuel; intros.
  - reflexivity.
  - simpl.

    repeat match goal with
    | [ |- context[let '(_, _) := ?b in _] ] => let E := fresh in destruct b eqn:E
           end.
    memt. setoid_rewrite H9. destruct_ifs; try reflexivity.
  - reflexivity.
  - Admitted.


  Lemma mem_no_mem_aux m nodes w fuel a_map b_map g_map bq_map aq_map :
  a_map_correct a_map ->
  b_map_correct b_map ->
  g_map_correct g_map ->
  bq_map_correct bq_map ->
  aq_map_correct aq_map ->
  (0 < w)%Z ->
  match depth_first_verify_aux m nodes w fuel a_map b_map g_map bq_map aq_map with
  | Some (maps,nodes) => Some nodes
  | None => None
  end =
  depth_first_verify_aux_no_mem m nodes w fuel.
Proof.
  induction fuel; intros.
  - simpl.
    split_pairs. memt. setoid_rewrite H9.
    destruct_ifs; reflexivity.
  - cbn.
    repeat match goal with
    | [ |- context[let '(_, _) := ?b in _] ] => let E := fresh in destruct b eqn:E
           end.
    specialize (H w). rewrite H4 in H. simpl in H.
    rewrite H. Admitted.


(* rewrite H5 in H0. simpl in H. *)
(*     rewrite H.     *)
(*   intros.  *)
(*   destruct (depth_first_verify_aux m nodes w fuel init_a_map init_b_map init_g_map init_bq_map init_aq_map) as [[[[[[? ?] ?] ?] ?] z]|] eqn:E. *)
(*   unfold depth_first_verify_aux_no_mem. *)
(*   unfold depth_first_verify_aux in E. simpl. *)
(*   simpl in *. *)
(*   destruct (alphaQ_mem a_map w). *)
(*   inversion E. *)
(*   destruct (Some (maps, z)). *)

(*   unfold depth_first_verify_aux_no_mem. *)
(*   unfold depth_first_verify_aux in E. *)
(*   inversion E. *)

Require Import Bool.Bool.
From BY Require Import Zpower_nat.
Import BoolNotations.


Definition children m w fuel :=
  children_aux m [] w 1 fuel init_a_map init_b_map init_g_map init_bq_map init_aq_map.

Definition depth_first_verify_no_mem_general P w fuel :=
  depth_first_verify_aux_no_mem P 1 w fuel.
Definition depth_first_verify :=
  match depth_first_verify_aux I 1 0 100 init_a_map init_b_map init_g_map init_bq_map init_aq_map with None => None | Some (a_map, b_map, g_map, bq_map, aq_map, nodes) => Some nodes end.
Definition depth_first_verify_no_mem fuel :=
  depth_first_verify_aux_no_mem I 1 0 fuel.

Require Import Coq.extraction.ExtrOcamlZBigInt.

Extraction "definitions" depth_first_verify.

Require Import InductionPrinciples.

Fixpoint ver_child (f : nat -> option Z) cnodes n :=
         match n with
         | 0%nat => Some cnodes
         | S n => match f n with
                 | None => None
                 | Some nodes =>
                   ver_child f (nodes + cnodes)%Z n
                 end
         end.

Fixpoint in_loop (P : Z -> bool) (g : Z -> option Z) e cnodes n :=
  match n with
  | 0%nat => None
  | S n =>
    if P e
    then Some cnodes
    else match g e with
           | None => None
           | Some nodes => in_loop P g (e + 1)%Z (nodes + cnodes)%Z n
         end
  end.

Fixpoint verify m (nodes w : Z) inner_fuel outer_fuel :=
  match outer_fuel with
  | 0%nat => None
  | S outer_fuel =>
    let mm := mmult (mtrans m) m in
    if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None
    else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w))
         then Some nodes
         else in_loop (fun e => has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e))))
                      (fun e => ver_child (fun n => verify (mmult (scaledM e (Z.of_nat ((2 * n) + 1)%nat)) m) 1 (e + w)%Z inner_fuel outer_fuel) 0%Z (Z.to_nat (2 ^ e)))
                      1%Z 0%Z inner_fuel
  end.

(* Equations mut (l : nat) : option Z := { *)
(*   mut 0 := Some 0%Z; *)
(*   mut (S l) := mut2 l *)
(* } *)
(* where *)
(* mut2 (l : nat) : option Z := *)
(*   { *)
(*     mut2 0 := Some 100%Z; *)
(*     mut2 (S l) := mut3 (S l) *)
(*   } *)
(* where *)
(* mut3 (l : nat) : option Z := *)
(*   { *)
(*     mut3 0 := Some 1%Z; *)
(*     mut3 (S l) := mut (S l) *)
(* }. *)




(* Equations verif (m : mat) (w nodes : Z) (i : nat) : option Z by struct i := *)
(*   { *)
(*     verif m w nodes 0 := None; *)
(*     verif m w nodes (S i) := *)
(*       let mm := mmult (mtrans m) m in *)
(*       if negb (has_at_most_norm m ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None *)
(*       else if (0 <? w)%Z && has_at_most_norm m ((4^w) * betaQ (Z.to_nat w)) *)
(*            then Some nodes *)
(*            else inner m mm w 1 nodes i *)
(*   } *)
(* where inner (m mm : mat) (w nodes e : Z) (i : nat) : option Z := *)
(*         { *)
(*           inner m mm w nodes e 0 := None; *)
(*           inner m mm w nodes e (S i) := *)
(*             if has_at_most_norm mm ((4 ^ w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) *)
(*             then Some nodes *)
(*             else match verifc m w nodes e 1 i (Z.to_nat (2 ^ e)) with *)
(*                  | None => None *)
(*                  | Some cnodes => inner m mm w (e + 1)%Z (cnodes + nodes)%Z i *)
(*                  end *)
(* } *)
(* where verifc (m : mat) (w nodes e cnodes : Z) (i n : nat) : option Z := *)
(*         { *)
(*           verifc m w nodes e cnodes i 0 := Some cnodes; *)
(*           verifc m w nodes e cnodes i (S n) := *)
(*             match verif (mmult (scaledM e (Z.of_nat (2 * n + 1)%nat)) m) (e + w) 1 i with *)
(*             | None => None *)
(*             | Some nodes => verifc m w nodes e (nodes + cnodes)%Z i n *)
(*             end *)
(*         }. *)
(* Next Obligation. *)
(*   exact 0%nat. *)
(* Qed. *)


(* Equations verif (m : mat) (w nodes : Z) (i j : nat) : option Z := *)
(*   { *)
(*     verif m w nodes i 0 := None; *)
(*     verif m w nodes i (S j) := *)
(*       let mm := mmult (mtrans m) m in *)
(*       if negb (has_at_most_norm m ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None *)
(*       else if (0 <? w)%Z && has_at_most_norm m ((4^w) * betaQ (Z.to_nat w)) *)
(*            then Some nodes *)
(*            else inner m mm w 1 nodes j i *)
(*   } *)
(* where inner (m mm : mat) (w nodes e : Z) (j i : nat) : option Z := *)
(*         { *)
(*           inner m mm w nodes e j 0 := None; *)
(*           inner m mm w nodes e j (S i) := *)
(*             if has_at_most_norm mm ((4 ^ w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) *)
(*             then Some nodes *)
(*             else match verifc m w nodes e 1 i j (Z.to_nat (2 ^ e)) with *)
(*                  | None => None *)
(*                  | Some cnodes => inner m mm w (e + 1)%Z (cnodes + nodes)%Z j i *)
(*                  end *)
(* } *)
(* where verifc (m : mat) (w nodes e cnodes : Z) (i j n : nat) : option Z := *)
(*         { *)
(*           verifc m w nodes e cnodes i j 0 := Some cnodes; *)
(*           verifc m w nodes e cnodes i j (S n) := *)
(*             match verif (mmult (scaledM e (Z.of_nat (2 * n + 1)%nat)) m) (e + w) 1 i j with *)
(*             | None => None *)
(*             | Some nodes => verifc m w nodes e (nodes + cnodes)%Z i j n *)
(*             end *)
(*         }. *)

(*             (* match *) *)
(*               (* (fix verify_children cnodes n := *) *)
(*               (*    match n with *) *)
(*               (*    | 0%nat => Some cnodes *) *)
(*               (*    | S n => let q := ((2 * n) + 1)%nat in *) *)
(*               (*            match *) *)
(*               (*              depth_first_verify_aux_no_mem_two_fuel (mmult (scaledM e (Z.of_nat q)) m) 1 (e + w)%Z inner_fuel outer_fuel with *) *)
(*               (*            | None => None *) *)
(*               (*            | Some nodes => *) *)
(*               (*              verify_children (nodes + cnodes)%Z n *) *)
(*               (*            end *) *)
(*               (*    end) 0%Z (Z.to_nat (2 ^ e)) with *) *)
(*             (* | None => None *) *)
(*             (* | Some cnodes => *) *)
(*               (* inner mm w (e + 1)%Z (cnodes + nodes)%Z inner_fuel  *) *)
(*           (* end *) *)
(* }. *)

(*   match outer_fuel with *)
(*   | 0%nat => None *)
(*   | S outer_fuel =>  *)
(*     let mm := mmult (mtrans m) m in *)
(*     if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None *)
(*     else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w)) *)
(*          then Some nodes *)
(*          else (fix inner_loop e nodes fuel := *)
(*                  match fuel with *)
(*                  | 0%nat => None *)
(*                  | S fuel => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) *)
(*                             then Some nodes *)
(*                             else match *)
(*                                 (fix verify_children cnodes n := *)
(*                                    match n with *)
(*                                    | 0%nat => Some cnodes *)
(*                                    | S n => let q := ((2 * n) + 1)%nat in *)
(*                                            match *)
(*                                              depth_first_verify_aux_no_mem_two_fuel (mmult (scaledM e (Z.of_nat q)) m) 1 (e + w)%Z inner_fuel outer_fuel with *)
(*                                            | None => None *)
(*                                            | Some nodes => *)
(*                                              verify_children (nodes + cnodes)%Z n *)
(*                                            end *)
(*                                    end) 0%Z (Z.to_nat (2 ^ e)) with *)
(*                               | None => None *)
(*                               | Some cnodes => *)
(*                                 inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel  *)
(*                               end *)
(*                  end) 1%Z nodes inner_fuel *)
(*   end. *)

(* Equations eq_verify (m w  nodes : Z) : Z := { *)
(*                                eq_verify m w nodes => eq_verify m w (nodes - 1) *)
(*                              }. *)

(* Lemma lemma w P nodes inner_fuel outer_fuel : verify P nodes w inner_fuel (S outer_fuel) = None -> *)
(*                                               verify P nodes w inner_fuel outer_fuel = None. *)
(* Proof. *)
(*   intros. *)
(*   simpl in H. *)
(*   simpl. *)
(*   unfold in_loop in H. *)
(*   inversion H. *)


(* Lemma lemma w P nodes inner_fuel outer_fuel : depth_first_verify_aux_no_mem_two_fuel P nodes w inner_fuel (S outer_fuel) = None -> *)
(*                                               depth_first_verify_aux_no_mem_two_fuel P nodes w inner_fuel outer_fuel = None. *)
(* Proof. *)
(*   intros. revert w P nodes inner_fuel H. *)
(*   induction outer_fuel. *)
(*   - reflexivity. *)
(*   - intros. *)
(*     simpl in H. *)
(*     simpl. *)

(* Theorem comp1_con : forall w P inner_fuel outer_fuel, inSQ_scaled w P -> depth_first_verify_aux_no_mem_two_fuel P 1 w inner_fuel outer_fuel = None -> depth_first_verify_aux_no_mem_two_fuel I 1 0 inner_fuel outer_fuel = None. *)
(* Proof. *)
(*   intros. revert H0. revert inner_fuel. revert outer_fuel. *)
(*   induction H. *)
(*   - auto. *)
(*   - intros. *)
(*     apply IHinSQ_scaled. *)
(*     revert H5. *)
(*     destruct outer_fuel. reflexivity. *)
(*     intros. *)
(*     change (depth_first_verify_aux_no_mem_two_fuel P 1 w inner_fuel (S outer_fuel)) with *)
(*          (if negb (has_at_most_norm (mmult (mtrans P) P) ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None *)
(*          else if (0 <? w)%Z && has_at_most_norm (mmult (mtrans P) P) ((4^w) * betaQ (Z.to_nat w)) *)
(*               then Some 1%Z *)
(*               else (fix inner_loop e nodes fuel := *)
(*                       match fuel with *)
(*                       | 0%nat => None *)
(*                       | S fuel => if has_at_most_norm (mmult (mtrans P) P) ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) *)
(*                                  then Some nodes *)
(*                                  else match *)
(*                                      (fix verify_children cnodes n := *)
(*                                         match n with *)
(*                                         | 0%nat => Some cnodes *)
(*                                         | S n => let q := ((2 * n) + 1)%nat in *)
(*                                                 match *)
(*                                                   depth_first_verify_aux_no_mem_two_fuel (mmult (scaledM e (Z.of_nat q)) P) 1 (e + w)%Z inner_fuel outer_fuel with *)
(*                                                 | None => None *)
(*                                                 | Some nodes => *)
(*                                                   verify_children (nodes + cnodes)%Z n *)
(*                                                 end *)
(*                                         end) 0%Z (Z.to_nat (2 ^ e)) with *)
(*                                    | None => None *)
(*                                    | Some cnodes => *)
(*                                      inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel  *)
(*                                    end *)
(*                       end) 1%Z 1%Z inner_fuel). *)
(*     rewrite H0.  *)
(*     destruct (negb (has_at_most_norm (mmult (mtrans P) P) (4 ^ w * alphaQ_nat (Z.to_nat w)))); [reflexivity|]. *)
(*     revert H2. *)
(*     assert (0 <= 1)%Z by lia. generalize H2. *)
(*     generalize 1%Z at 1 2 5.  *)
(*     apply rev_1_natlike_ind. *)
(*     + destruct inner_fuel; [reflexivity|]. *)
(*       assert (depth_first_verify_aux_no_mem_two_fuel (mmult (scaledM e q) P) 1 (e + w) (S inner_fuel) outer_fuel = None). *)
(*       inversion H5. *)
(*       simpl in H5. *)

(*       rewrite H5. *)
(*     intros. destruct inner_fuel. reflexivity. *)



(*     simpl. *)
(*     induction inner_fuel. reflexivity. *)
(*     change *)
(*       (  (fix inner_loop (e0 nodes : Z) (fuel : nat) {struct fuel} : option Z := *)
(*      match fuel with *)
(*      | 0%nat => None *)
(*      | S fuel0 => *)
(*          if has_at_most_norm (mmult (mtrans P) P) (4 ^ w * gammaQ (Z.to_nat w) (Z.to_nat e0)) *)
(*          then Some nodes *)
(*          else *)
(*           match *)
(*             (fix verify_children (cnodes : Z) (n : nat) {struct n} : option Z := *)
(*                match n with *)
(*                | 0%nat => Some cnodes *)
(*                | S n0 => *)
(*                    let q0 := (2 * n0 + 1)%nat in *)
(*                    match *)
(*                      depth_first_verify_aux_no_mem_two_fuel (mmult (scaledM e0 (Z.of_nat q0)) P) 1 (e0 + w) inner_fuel outer_fuel *)
(*                    with *)
(*                    | Some nodes0 => verify_children (nodes0 + cnodes)%Z n0 *)
(*                    | None => None *)
(*                    end *)
(*                end) 0%Z (Z.to_nat (2 ^ e0)) *)
(*           with *)
(*           | Some cnodes => inner_loop (e0 + 1)%Z (cnodes + nodes)%Z fuel0 *)
(*           | None => None *)
(*           end *)
(*      end) 1%Z 1%Z inner_fuel) with *)
(*   (fix inner_loop (e0 nodes : Z) (fuel : nat) {struct fuel} : option Z := *)
(*      match fuel with *)
(*      | 0%nat => None *)
(*      | S fuel0 => *)
(*          if has_at_most_norm (mmult (mtrans P) P) (4 ^ w * gammaQ (Z.to_nat w) (Z.to_nat e0)) *)
(*          then Some nodes *)
(*          else *)
(*           match *)
(*             (fix verify_children (cnodes : Z) (n : nat) {struct n} : option Z := *)
(*                match n with *)
(*                | 0%nat => Some cnodes *)
(*                | S n0 => *)
(*                    let q0 := (2 * n0 + 1)%nat in *)
(*                    match *)
(*                      depth_first_verify_aux_no_mem_two_fuel (mmult (scaledM e0 (Z.of_nat q0)) P) 1 (e0 + w) inner_fuel outer_fuel *)
(*                    with *)
(*                    | Some nodes0 => verify_children (nodes0 + cnodes)%Z n0 *)
(*                    | None => None *)
(*                    end *)
(*                end) 0%Z (Z.to_nat (2 ^ e0)) *)
(*           with *)
(*           | Some cnodes => inner_loop (e0 + 1)%Z (cnodes + nodes)%Z fuel0 *)
(*           | None => None *)
(*           end *)
(*      end) 1%Z 1%Z inner_fuel         *)

(*     cbn. *)
(*     rewrite H5. *)
(*     simpl. *)
(*     rewrite H5. *)
(*     cbn. *)
(*     replace (depth_first_verify_aux_no_mem P 1 w fuel) with *)
(*         (let mm := mmult (mtrans P) P in *)
(*          if negb (has_at_most_norm mm ((4 ^ w) * alphaQ_nat (Z.to_nat w))) then None *)
(*          else if (0 <? w)%Z && has_at_most_norm mm ((4^w) * betaQ (Z.to_nat w)) *)
(*               then Some 1%Z *)
(*               else (fix inner_loop e nodes fuel := *)
(*                       match fuel with *)
(*                       | 0%nat => None *)
(*                       | S fuel => if has_at_most_norm mm ((4^w) * (gammaQ (Z.to_nat w) (Z.to_nat e))) *)
(*                                  then Some nodes *)
(*                                  else match *)
(*                                      (fix verify_children cnodes n := *)
(*                                         match n with *)
(*                                         | 0%nat => Some cnodes *)
(*                                         | S n => let q := ((2 * n) + 1)%nat in *)
(*                                                 match *)
(*                                                   depth_first_verify_aux_no_mem (mmult (scaledM e (Z.of_nat q)) P) 1 (e + w)%Z fuel with *)
(*                                                 | None => None *)
(*                                                 | Some nodes => *)
(*                                                   verify_children (nodes + cnodes)%Z n *)
(*                                                 end *)
(*                                         end) 0%Z (Z.to_nat (2 ^ e)) with *)
(*                                    | None => None *)
(*                                    | Some cnodes => *)
(*                                      inner_loop (e + 1)%Z (cnodes + nodes)%Z fuel  *)
(*                                    end *)
(*                       end) 1%Z 1%Z fuel). admit. *)
(*     unfold depth_first_verify_aux *)
(*     reflexivity. *)

(*     unfold depth_first_verify_aux_no_mem.  *)

(*     assert (has_at_most_norm (mmult (mtrans P) P) (4 ^ w * gammaQ (Z.to_nat w) (Z.to_nat 1)) = false). admit. *)
(*     rewrite H6. *)
(*     remember (Z.to_nat e) as enat. *)
(*     induction enat. simpl. *)

(*     rewrite H0.  *)
(*     rewrite H0. *)

(*     destruct (negb (has_at_most_norm (mmult (mtrans P) P) (4 ^ Z.of_nat w * alphaQ_nat (Z.to_nat (Z.of_nat w))))). reflexivity. *)
(*     assert ((0 <? Z.of_nat w) && has_at_most_norm (mmult (mtrans P) P) ((4 ^ Z.of_nat w) * betaQ (Z.to_nat (Z.of_nat w))) = true). *)
(*     rewrite Nat2Z.id. *)


(*     rewrite <- Zpower_nat_Z. *)
(*     Search negb. *)
(*     apply negb_false_iff. *)

(*     destruct fuel. *)
(*     + simpl in H5. *)
(*       destruct  *)
(*     destruct (negb (has_at_most_norm (mmult (mtrans P) P) (4 ^ (Z.of_nat w) * alphaQ_nat (Z.to_nat (Z.of_nat w))))). *)
(*     simpl. *)


Theorem comp1_con : (exists w P, inSQ w P /\ has_at_most_norm (mmult (mtrans P) P) (alphaQ_nat w) = false) -> (forall fuel, depth_first_verify_no_mem fuel = None).
(* Proof. *)
(*   intros. *)
(*   destruct H as [w [P [H1 H2]]]. *)
(*   revert H2. *)
(*   induction H1; intros. *)
(*   - simpl in H2. inversion H2. *)
(*   - unfold depth_first_verify_no_mem. *)

(*     unfold depth_first_verify_no_mem. *)
(*     unfold depth_first_verify_aux_no_mem. *)
(*     destruct fuel. *)
(*     + reflexivity. *)
(*     + destruct (negb (has_at_most_norm (mmult (mtrans I) I) (4 ^ 0 * alphaQ_nat (Z.to_nat 0)))). *)
(*       * reflexivity. *)
(*       * simpl in H2. *)

(*         destruct ((0 <? 0%Z) && has_at_most_norm (mmult (mtrans I) I) (4 ^ 0 * betaQ (Z.to_nat 0))) eqn:E. *)
(*         ** simpl in E. inversion E. *)
(*         ** destruct (has_at_most_norm (mmult (mtrans I) I) (4 ^ 0 * gammaQ (Z.to_nat 0) (Z.to_nat 1))) eqn:E2. *)
(*            pose proof gammaQ_0_1. *)
(*            set (gamma01 := gammaQ 0 1). *)
(*            change (gammaQ 0 1) with gamma01 in H. *)
(*            change (Z.to_nat 0) with 0%nat in E2. *)
(*            change (Z.to_nat 1) with 1%nat in E2. *)
(*            change (gammaQ 0 1) with gamma01 in E2. *)
(*            unfold has_at_most_norm in E2. *)
(*            cbn [I mtrans mmult] in E2. *)
(*            setoid_rewrite H in E2. *)
(*            cbn in E2. inversion E2. *)

(*       * destruct ((0 <? 0%Z) && has_at_most_norm (mmult (mtrans I) I) (4 ^ 0 * betaQ (Z.to_nat 0))). *)
(*       unfold has_at_most_norm. *)
(*       cbn [I mtrans mmult Z.to_nat alphaQ_nat betaQ Z.mul Z.add Z.leb Z.pow]. *)
(*       cbn [negb].       *)


(* Proof.   *)
(* Theorem comp1 : (exists n fuel, depth_first_verify_no_mem fuel = Some n) -> (forall w P, inSQ w P -> has_at_most_norm (mmult (mtrans P) P) (alphaQ_nat w) = true). *)
(* Proof. *)
(*   intros; destruct H. unfold depth_first_verify_no_mem in H. *)
(*   unfold depth_first_verify_aux_no_mem in H. *)
(*   induction H0. reflexivity. *)
(*   inversion H. *)
(*   destruct (depth_first_verify_aux MatrixQ.I 1 0 100 init_a_map init_b_map init_g_map init_bq_map init_aq_map 1) eqn:E. *)


(* Require Import Reals. *)
(* From BY Require Import Spectral. *)

(* Local Open Scope R. *)



(*     inversion H. *)


(* (* Theorem F22 : (forall w P, inS w P -> mat_norm P <= alpha w). Admitted. *) *)

(* Theorem comp1_con : (exists w P, inSQ w P /\ has_at_most_norm (mmult (mtrans P) P) (alphaQ_nat w) = true) -> *)
(*                     (forall fuel, depth_first_verify_no_mem fuel = None). *)

(* Theorem comp1 : (exists n fuel, depth_first_verify_no_mem fuel = Some n) -> *)
(*                 (forall w P, inSQ w P -> has_at_most_norm (mmult (mtrans P) P) (alphaQ_nat w) = true). *)
