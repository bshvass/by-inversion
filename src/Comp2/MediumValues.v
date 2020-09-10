Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require Import Definitions.

Local Open Scope int63.

Definition W n := min_needs_n_steps_nat_int 1 0 n sint_max steps.

Time Definition comp231 := eq_refl 12565573 <: W 31 = 12565573.
Check comp231.
Time Definition comp232 := eq_refl 22372085 <: W 32 = 22372085.
Check comp232.
Time Definition comp233 := eq_refl 35806445 <: W 33 = 35806445.
Check comp233.
Time Definition comp234 := eq_refl 71013905 <: W 34 = 71013905.
Check comp234.
Time Definition comp235 := eq_refl 74173637 <: W 35 = 74173637.
Check comp235.
Time Definition comp236 := eq_refl 205509533 <: W 36 = 205509533.
Check comp236.
Time Definition comp237 := eq_refl 226964725 <: W 37 = 226964725.
Check comp237.
Time Definition comp238 := eq_refl 487475029 <: W 38 = 487475029.
Check comp238.
Time Definition comp239 := eq_refl 534274997 <: W 39 = 534274997.
Check comp239.
Time Definition comp240 := eq_refl 1543129037 <: W 40 = 1543129037.
Check comp240.
