Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require Import Coq.Lists.List.
Require Import Coq.Program.Program.

Import ListNotations.

Local Open Scope int63.

Definition steps := 2 ^ 44 : N.
Definition sint_max := 1 << 62 - 1.

Definition asr a := set_digit (lsr a 1) 62 (get_digit a 62).
Definition int_min a b := if a < b then a else b.

Definition divstep_int (d f g : int) :=
  if (get_digit (opp d) 62) && (negb (is_even g))
  then (1 - d, g, asr (g - f))
  else (1 + d, f, asr (g + (g land 1) * f)).

Fixpoint needs_n_steps_int (d a b : int) n :=
  match n with
  | 0%nat => true
  | S n => if (b == 0)
          then false
          else let '(d', a', b') := divstep_int d a b in needs_n_steps_int d' a' b' n
  end.

Program Fixpoint min_needs_n_steps_nat_int (a b : int) n (acc : int) fuel {measure fuel (N.lt)} :=
  match fuel with
  | 0%N => 1 << 61
  | _ =>  if (leb acc (mul a a))
              then acc
              else if (leb acc (add (mul a a) (mul b b)))
                   then min_needs_n_steps_nat_int (a + 2) 0 n acc (N.pred fuel)
                   else if needs_n_steps_int 1 a (b >> 1) n || needs_n_steps_int 1 a (opp (b >> 1)) n
                        then min_needs_n_steps_nat_int (a + 2) 0 n (int_min (a * a + b * b) acc) (N.pred fuel)
                        else min_needs_n_steps_nat_int a (b + 2) n acc (N.pred fuel)
  end.

Solve Obligations with try lia.
Next Obligation. exact (Acc_intro_generator (50) ltac:(apply measure_wf; apply N.lt_wf_0)). Defined.


Fixpoint divsteps_aux steps fuel d a b :=
  match fuel with
  | 0%nat => steps
  | S fuel => if b == 0
             then steps
             else let '(d', a', b') := divstep_int d a b in divsteps_aux (S steps) fuel d' a' b'
  end.

Definition divsteps := divsteps_aux 0 100.


Program Fixpoint table_b (a a2 b : int) (bound : int) (acc : list int) fuel {measure fuel (N.lt)} :=
  match fuel with
  | 0%N => acc
  | _ => let length := a2 + b * b in
        if (leb length bound)
        then
          let steps := divsteps 1 a (b >> 1) in
          let steps_opp := divsteps 1 a (opp (b >> 1)) in
          let n := max steps steps_opp in
          let new_list := (fix aux n i l :=
                             match n with
                             | 0%nat => l
                             | S n =>
                               let acci := nth_default sint_max acc i in
                               aux n (S i) ((if length < acci then length else acci) :: l)
                             end) n 0%nat [] in
          table_b a a2 (b + 2) bound new_list (N.pred fuel)
        else
          acc
  end.

Solve Obligations with try lia.
Next Obligation. exact (Acc_intro_generator (50) ltac:(apply measure_wf; apply N.lt_wf_0)). Defined.

Program Fixpoint table_a (a b : int) (bound : int) (acc : list int) fuel_a fuel_b {measure fuel_a (N.lt)} :=
  match fuel_a with
  | 0%N => acc
  | _ =>  let a2 := a * a in
         if (leb a2 bound)
         then
           table_a (a + 2) 0 bound (table_b a a2 b bound acc fuel_b) (N.pred fuel_a) fuel_b
         else
           acc
  end.

Solve Obligations with try lia.
Next Obligation. exact (Acc_intro_generator (50) ltac:(apply measure_wf; apply N.lt_wf_0)). Defined.
