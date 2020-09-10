Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require Import Coq.extraction.ExtrOCamlInt63.

Require Import BY.Comp2.Definitions.

Definition W n := min_needs_n_steps_nat_int 1 0 n sint_max steps.

Extraction "definition.ml" W.
