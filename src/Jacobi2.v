Require Import ZArith.
From stdpp Require Import decidable.
Local Open Scope Z_scope.
Global Instance Z_le_dec: RelDecision Z.le := Z_le_dec.
Global Instance Z_lt_dec: RelDecision Z.lt := Z_lt_dec.
Global Instance Z_eq_dec: RelDecision Z.eq := Z.eq_dec.

Definition σ x y :=
  if (decide ((x < 0) /\ (y < 0))) then -1
  else 1.

Definition τ x :=
  if (decide ((x mod 4) = 3)) then -1
  else 1.

Definition η x y :=
  if (decide (((x mod 4) = 3) /\ (y mod 4) = 3)) then -1
  else 1.

Definition ν x :=
  if (decide (((x mod 8) = 3) \/ (x mod 8) = 5)) then -1
  else 1.

Axiom legendre : Z -> Z -> Z.
Axiom leg_add :
  forall x y k, legendre (x + k * y) y = legendre x y.
Axiom leg_mul :
  forall x1 x2 y, legendre (x1 * x2) y = legendre x1 y * legendre x2 y.
Axiom leg_rec :
  forall x y, legendre x y * legendre y x = σ x y * η x y.

Require Import Divstep.

Definition divstep_jac d f g u v q r k :=
  if (decide ((g mod 2 = 1) /\ (0 < d)))
  then (1 - d, g, (g - f) / 2, u - q, v - r, 2 * u, 2 * v, k * σ g (-f) * η g (-f) * ν (-f))
  else (1 + d, f, (g + (g mod 2) * f) / 2, u + (g mod 2) * q, v + (g mod 2) * r, 2 * q, 2 * r, k * ν f).
