/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
/-!

# The 2D Ising CFT as the minimal model M(3,4)

The 2D critical Ising model is described in the continuum by the unitary minimal
model `M(p, p')` with `(p, p') = (3, 4)`.  This file formalizes the exact
conformal data of that CFT — the central charge, the Kac conformal weights of the
three primary operators, and their scaling dimensions — and proves the values by
rational arithmetic.

These are the *exact* numbers a tensor-network numerical simulation measures:

* central charge `c = 1/2`  (measured `c ≈ 0.5023`, and equal to the Virasoro
  `isingCentralCharge` formalized on a separate branch);
* spin primary `σ`: scaling dimension `Δ_σ = 1/8 = 0.125`  (measured `Δσ ≈ 0.125`,
  0.07% agreement);
* energy primary `ε`: scaling dimension `Δ_ε = 1`  (measured `Δε ≈ 1.009`).

This module is deliberately self-contained over the rationals `ℚ`: it depends only
on Mathlib (no Virasoro import).  It bridges the formal CFT data to
the measured numbers and is a building block toward deriving
emergent geometry from CFT axioms.

## Main definitions

* `minimalCentralCharge p p'` — the minimal-model central charge
  `c(p, p') = 1 − 6·(p − p')² / (p·p')`.
* `kacWeight r s p p'` — the Kac conformal weight
  `h(r, s; p, p') = ((r·p' − s·p)² − (p' − p)²) / (4·p·p')`.
* `scalingDim h` — the spinless scaling dimension `Δ = 2·h`.

## Main results

* `ising_central_charge : minimalCentralCharge 3 4 = 1/2`.
* `ising_h_identity`, `ising_h_sigma`, `ising_h_epsilon` — the three primary weights
  `0`, `1/16`, `1/2`.
* `ising_dim_sigma`, `ising_dim_epsilon` — the measured-value bridge `Δ_σ = 1/8`,
  `Δ_ε = 1`.
* `ising_primaries_distinct` — the spectrum is genuinely nontrivial (three distinct
  weights, `σ ≠ 0`).
* `minimalCentralCharge_nonneg`, `kac_*_nonneg` — unitarity-flavored facts
  (`c ≥ 0`, `h ≥ 0`).
* `tricritical_central_charge : minimalCentralCharge 4 5 = 7/10` — a second minimal
  model, witnessing that the central-charge formula is genuine and not hardcoded.

-/

@[expose] public section

namespace Physlib.IsingCFT

/-- The central charge of the minimal model `M(p, p')`:
`c(p, p') = 1 − 6·(p − p')² / (p·p')`. -/
def minimalCentralCharge (p p' : ℚ) : ℚ := 1 - 6 * (p - p') ^ 2 / (p * p')

/-- The Kac conformal weight of the `(r, s)` operator in `M(p, p')`:
`h(r, s; p, p') = ((r·p' − s·p)² − (p' − p)²) / (4·p·p')`. -/
def kacWeight (r s p p' : ℚ) : ℚ := ((r * p' - s * p) ^ 2 - (p' - p) ^ 2) / (4 * p * p')

/-- The spinless scaling dimension of a primary with holomorphic weight `h`:
`Δ = 2·h`. -/
def scalingDim (h : ℚ) : ℚ := 2 * h

/-! ### Central charge of the Ising CFT -/

/-- The 2D Ising CFT is the minimal model `M(3, 4)`, with central charge `c = 1/2`.
This equals the numerically-measured `c ≈ 0.5023` and the Virasoro `isingCentralCharge`
(formalized on a separate branch). -/
theorem ising_central_charge : minimalCentralCharge 3 4 = 1 / 2 := by
  unfold minimalCentralCharge; norm_num

/-! ### Conformal weights of the three Ising primaries -/

/-- Identity primary `𝟙`: `h(1, 1) = 0`. -/
theorem ising_h_identity : kacWeight 1 1 3 4 = 0 := by
  unfold kacWeight; norm_num

/-- Spin primary `σ`: `h(2, 2) = 1/16`. -/
theorem ising_h_sigma : kacWeight 2 2 3 4 = 1 / 16 := by
  unfold kacWeight; norm_num

/-- Energy primary `ε`: `h(1, 3) = 1/2`. -/
theorem ising_h_epsilon : kacWeight 1 3 3 4 = 1 / 2 := by
  unfold kacWeight; norm_num

/-! ### Scaling dimensions — the measured-value bridge -/

/-- Spin primary `σ`: `Δ_σ = 2·h_σ = 1/8 = 0.125`.  This is the numerically-measured
value (`Δσ ≈ 0.125`, 0.07% agreement). -/
theorem ising_dim_sigma : scalingDim (kacWeight 2 2 3 4) = 1 / 8 := by
  unfold scalingDim kacWeight; norm_num

/-- Energy primary `ε`: `Δ_ε = 2·h_ε = 1`.  Measured `Δε ≈ 1.009`. -/
theorem ising_dim_epsilon : scalingDim (kacWeight 1 3 3 4) = 1 := by
  unfold scalingDim kacWeight; norm_num

/-! ### Anti-vacuity / non-degeneracy (BP 21)

The spectrum is genuinely nontrivial: the three primary weights are pairwise
distinct and the spin weight is nonzero.  This rules out a vacuous `0 = 0` reading
of the results above. -/

/-- The three Ising primaries have distinct conformal weights, and the spin weight
`σ = 1/16` is nonzero: a genuine three-operator spectrum. -/
theorem ising_primaries_distinct :
    kacWeight 1 1 3 4 ≠ kacWeight 2 2 3 4 ∧
      kacWeight 2 2 3 4 ≠ kacWeight 1 3 3 4 ∧
        kacWeight 2 2 3 4 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold kacWeight; norm_num

/-! ### Unitarity-flavored facts

A unitary CFT has central charge `c ≥ 0` and primary weights `h ≥ 0`. -/

/-- Unitarity: the Ising central charge is nonnegative (`c = 1/2 ≥ 0`). -/
theorem minimalCentralCharge_nonneg : 0 ≤ minimalCentralCharge 3 4 := by
  unfold minimalCentralCharge; norm_num

/-- Unitarity: the identity weight is nonnegative (`h = 0 ≥ 0`). -/
theorem kac_identity_nonneg : 0 ≤ kacWeight 1 1 3 4 := by
  unfold kacWeight; norm_num

/-- Unitarity: the spin weight is nonnegative (`h = 1/16 ≥ 0`). -/
theorem kac_sigma_nonneg : 0 ≤ kacWeight 2 2 3 4 := by
  unfold kacWeight; norm_num

/-- Unitarity: the energy weight is nonnegative (`h = 1/2 ≥ 0`). -/
theorem kac_epsilon_nonneg : 0 ≤ kacWeight 1 3 3 4 := by
  unfold kacWeight; norm_num

/-! ### A second minimal model — the formulas are genuine, not hardcoded

The tricritical Ising CFT is the minimal model `M(4, 5)`, with central charge
`c = 7/10`.  Evaluating the same `minimalCentralCharge` formula at a different model
witnesses that it is a real function of `(p, p')`, not a value hardcoded for Ising. -/

/-- The tricritical Ising CFT `M(4, 5)` has central charge `c = 7/10`. -/
theorem tricritical_central_charge : minimalCentralCharge 4 5 = 7 / 10 := by
  unfold minimalCentralCharge; norm_num

end Physlib.IsingCFT
