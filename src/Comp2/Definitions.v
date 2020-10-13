Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require Import Coq.Program.Program.

Local Open Scope int63.

Definition steps := Eval vm_compute in 2 ^ 44 : N.
Definition sint_max := Eval vm_compute in 1 << 62 - 1.

Definition asr a := let b := if (get_digit a 62) then 1 << 62 else 0 in Int63.lor (lsr a 1) b.
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

Definition W n := min_needs_n_steps_nat_int 1 0 n sint_max steps.
