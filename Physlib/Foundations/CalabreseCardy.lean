/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
/-!

# The Calabrese–Cardy entanglement-entropy law

For a 1+1D conformal field theory (CFT) of central charge `c`, the entanglement entropy of an
interval of length `ℓ` on the infinite line (with UV cutoff `a`) is the Calabrese–Cardy law
(Calabrese–Cardy 2004):

  `S(ℓ) = (c/3) · log(ℓ/a) + c₁`,

where `c₁` is a non-universal constant. Absorbing the cutoff `a` into `c₁` (equivalently `a = 1`)
gives `ccEntropy c ℓ c₁ = (c/3) · log ℓ + c₁`.

The **universal** content is the *coefficient* `c/3` of the logarithm: the central charge is
*extracted from entanglement* as `c = 3 · (log-slope of S)`. This is exactly the procedure that
fits `S(ℓ)` to measure the central charge (e.g. `c = 1/2` for the 2D Ising CFT). The non-universal
constant `c₁` cancels in any entropy *difference*, giving a cutoff-independent universal observable.

This file formalizes, over `ℝ`:
* `ccEntropy` — the interval entropy (infinite line);
* `cc_entropy_difference` — the cutoff-independent universal difference `(c/3)·log(ℓ₂/ℓ₁)`;
* `central_charge_from_entropy` — the extraction `c = 3·ΔS / log(ℓ₂/ℓ₁)` (the CFT-central-charge →
  entanglement bridge);
* the Ising instance (`isingLogSlope = 1/6`) and a concrete *nonzero* universal observable
  (anti-vacuity);
* `ccEntropyFinite` — the finite-size (periodic) form the numerics actually fit.

The `(c/3) log ℓ` divergence is the Ryu–Takayanagi geodesic-length divergence near the AdS boundary:
this law is the CFT-central-charge → entanglement → RT-geometry link, a building block toward
CFT ⟹ emergent geometry.

-/

@[expose] public section

namespace Physlib.CalabreseCardy

open Real

/-- The Calabrese–Cardy entanglement entropy of an interval of length `ℓ` on the infinite line, for
a 1+1D CFT of central charge `c`. The UV cutoff is absorbed into the non-universal constant `c₁`
(equivalently `a = 1`):
`S(ℓ) = (c/3) · log ℓ + c₁`. -/
noncomputable def ccEntropy (c ℓ c₁ : ℝ) : ℝ := (c / 3) * Real.log ℓ + c₁

/-- **Universal, cutoff-independent entropy difference.** The non-universal constant `c₁` cancels,
leaving the measurable `(c/3) · log(ℓ₂/ℓ₁)`. This is the cutoff-independent observable the numerics
actually extract. -/
theorem cc_entropy_difference (c ℓ₁ ℓ₂ c₁ : ℝ) (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) :
    ccEntropy c ℓ₂ c₁ - ccEntropy c ℓ₁ c₁ = (c / 3) * Real.log (ℓ₂ / ℓ₁) := by
  unfold ccEntropy
  rw [Real.log_div (ne_of_gt h₂) (ne_of_gt h₁)]
  ring

/-- **Central charge from entanglement — the bridge.** With `ℓ₁ ≠ ℓ₂` (so `log(ℓ₂/ℓ₁) ≠ 0`), the
central charge is recovered exactly from the entropy difference:
`c = 3 · (S(ℓ₂) − S(ℓ₁)) / log(ℓ₂/ℓ₁)`.
This is the exact numeric extraction procedure, now formalized. -/
theorem central_charge_from_entropy (c ℓ₁ ℓ₂ c₁ : ℝ) (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂)
    (hne : ℓ₁ ≠ ℓ₂) :
    3 * (ccEntropy c ℓ₂ c₁ - ccEntropy c ℓ₁ c₁) / Real.log (ℓ₂ / ℓ₁) = c := by
  have hne' : ℓ₂ / ℓ₁ ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq (ne_of_gt h₁)]
    exact fun h => hne h.symm
  have hlog : Real.log (ℓ₂ / ℓ₁) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (div_pos h₂ h₁) hne'
  rw [cc_entropy_difference c ℓ₁ ℓ₂ c₁ h₁ h₂]
  field_simp

/-! ### Ising instance

The 2D Ising CFT has central charge `c = 1/2`, so its Calabrese–Cardy log-slope is
`c/3 = 1/6`. This is the coefficient an entanglement-entropy fit recovers for the
Ising CFT. -/

/-- The Calabrese–Cardy log-slope `c/3` at the Ising central charge `c = 1/2`. -/
noncomputable def isingLogSlope : ℝ := (1 / 2) / 3

/-- The Ising log-slope is `1/6`. -/
theorem ising_log_slope : isingLogSlope = 1 / 6 := by
  unfold isingLogSlope; norm_num

/-- **Anti-vacuity (BP 21): the Ising log-slope is nonzero.** The universal coefficient `c/3 = 1/6`
is a genuine nonzero quantity, not `0 = 0`. -/
theorem ising_log_slope_ne_zero : isingLogSlope ≠ 0 := by
  rw [ising_log_slope]; norm_num

/-- **Ising instance of the extraction.** Plugging the Ising central charge `c = 1/2` into
`central_charge_from_entropy` with any admissible interval pair recovers `c = 1/2` exactly. Here we
use `ℓ₁ = 1`, `ℓ₂ = 2`. -/
theorem ising_central_charge_recovered (c₁ : ℝ) :
    3 * (ccEntropy (1 / 2) 2 c₁ - ccEntropy (1 / 2) 1 c₁) / Real.log ((2 : ℝ) / 1) = 1 / 2 :=
  central_charge_from_entropy (1 / 2) 1 2 c₁ (by norm_num) (by norm_num) (by norm_num)

/-- **Anti-vacuity (BP 21): a concrete nonzero universal observable.** For the Ising CFT, the
entropy difference between intervals of length `2` and `1` equals `(1/6) · log 2`, a specific value
built from the universal slope. -/
theorem ising_entropy_difference (c₁ : ℝ) :
    ccEntropy (1 / 2) 2 c₁ - ccEntropy (1 / 2) 1 c₁ = (1 / 6) * Real.log 2 := by
  rw [cc_entropy_difference (1 / 2) 1 2 c₁ (by norm_num) (by norm_num)]
  norm_num

/-- **Anti-vacuity (BP 21): the concrete Ising entropy difference is strictly positive.** Since
`log 2 > 0` and the slope `1/6 > 0`, `S(2) − S(1) = (1/6) log 2 > 0` — a genuine nonzero universal
observable, not a vacuous `0 = 0`. -/
theorem ising_entropy_difference_pos (c₁ : ℝ) :
    0 < ccEntropy (1 / 2) 2 c₁ - ccEntropy (1 / 2) 1 c₁ := by
  rw [ising_entropy_difference c₁]
  have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-! ### Finite-size (periodic) form

The Calabrese–Cardy law on a periodic system of `N` sites replaces the interval length `ℓ` by the
chord `(N/π)·sin(π ℓ / N)`; this is the form a finite-size numerical fit actually uses. It reduces to the
infinite-line form for `ℓ ≪ N` (where `sin(πℓ/N) ≈ πℓ/N`, so the chord `≈ ℓ`). Provided as a
definition; no heavy proof required. -/

/-- The finite-size (periodic) Calabrese–Cardy entropy on `N` sites:
`S(ℓ) = (c/3) · log((N/π)·sin(π ℓ / N)) + c₁`. Reduces to `ccEntropy` for `ℓ ≪ N`. -/
noncomputable def ccEntropyFinite (c ℓ N c₁ : ℝ) : ℝ :=
  (c / 3) * Real.log ((N / Real.pi) * Real.sin (Real.pi * ℓ / N)) + c₁

end Physlib.CalabreseCardy
