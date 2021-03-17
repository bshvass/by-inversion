Require Import QArith.
Require Import List.

From BY Require Import Q AppendixF Qmin_list.


(* Require Import StreamMemo. *)

Section t.
  Context {A : Type}.
  
  CoInductive lazy : Type := | Thunk : A -> lazy.
  
  CoInductive lazies : Type :=
  | Cons : lazy -> lazies -> lazies.
  
  Fixpoint nth n cst :=
    match n, cst with
    | O, Cons (Thunk xi) _ => xi
    | S p, Cons _ c => nth p c
    end.
  
  CoFixpoint mk_lazy {B} f (n : B) := Thunk (f n).
  CoFixpoint memo' f n :=
    Cons (mk_lazy f n) (memo' f (S n)).
  Definition memo f := memo' f 0.
  
End t.

Definition alphaQ_mem w := nth w (memo alphaQ).

Eval vm_compute in alphaQ_mem 70.

Definition alphaQ_quot '(w, i) :=
  alphaQ_mem (w + i)%nat / (alphaQ_mem i).
Definition alphaQ_quot_mem := nth 
