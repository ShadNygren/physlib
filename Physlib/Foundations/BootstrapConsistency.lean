/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic

/-!

# Conformal-bootstrap consistency: falsification by a positivity bound

This file formalizes the *algebraic core* of the conformal bootstrap as a
**falsification-by-contradiction** argument (a swampland-style no-go).

## The physics, in plain language

A consistent unitary conformal field theory (CFT) has a four-point correlation
function that can be expanded in *conformal blocks* in two different channels.
Equating the two expansions gives the **crossing sum rule**. **Unitarity** forces
every squared OPE (operator-product-expansion) coefficient to be non-negative.

If one hypothesizes a spectrum of operators and can exhibit a linear functional
that is non-negative on every conformal block in that spectrum while the identity
operator contributes a strictly positive amount, then the crossing sum rule —
a sum of non-negative terms that must vanish — is contradicted. Hence the
hypothesized spectrum is **inconsistent**: it is *ruled out*, i.e. it lies in the
"swampland." This is the "assume consistency ⟹ sharp positivity bound ⟹ any
violation is `False`" pattern that underlies numerical bootstrap exclusion plots.

## What is axiomatized vs. proved

The genuinely CFT-specific content — that `blockValue` and `opeCoeffSq` really are
conformal-block data satisfying a crossing equation — is **axiomatized** into the
`BootstrapData` structure (its fields are the physical inputs). What is **proved**
is the purely algebraic exclusion mechanism: non-negativity of each summand,
non-negativity of the sum, and the resulting strict-positivity contradiction with
the crossing equation.

## Key results

- `BootstrapData` : the axiomatized bootstrap inputs (unitarity + crossing sum rule).
- `bootstrap_exclusion` : block-positivity + positive identity ⟹ `False`.
- `spectrum_in_swampland` : the packaged no-go (same content, packaged hypothesis).
- `excluded_crossing_lhs_pos` / `excludedData_fires` : anti-vacuity witness (a) — an
  explicit datum whose crossing LHS is `3 > 0`, on which `bootstrap_exclusion` fires.
- `allowedSpectrum_not_excludable` / `allowedData` : anti-vacuity witness (b) — an
  explicit datum satisfying crossing whose block-positivity hypothesis provably
  *fails*, so the bound is non-trivial (it does not rule out everything).

-/

@[expose] public section

open Finset

namespace Physlib.Foundations

variable {𝕜 : Type*} {ι : Type*}

/-- Axiomatized conformal-bootstrap data over an ordered ring `𝕜`, indexed by a
finite operator set `ι`.

- `opeCoeffSq i` is the squared OPE coefficient of the `i`-th operator; **unitarity**
  is the field `opeCoeffSq_nonneg`.
- `blockValue i` is the value of the crossing linear functional on the `i`-th
  conformal block.
- `identityContribution` is the (functional applied to the) identity operator's block.
- `crossing` is the **crossing sum rule**: identity plus the OPE-weighted block sum
  vanishes.

That these fields are *honest conformal-block data* is the axiomatized physics. -/
structure BootstrapData (𝕜 : Type*) (ι : Type*) [Ring 𝕜] [PartialOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Fintype ι] where
  /-- Squared OPE coefficient of the `i`-th operator. -/
  opeCoeffSq : ι → 𝕜
  /-- Unitarity: every squared OPE coefficient is non-negative. -/
  opeCoeffSq_nonneg : ∀ i, 0 ≤ opeCoeffSq i
  /-- Value of the crossing functional on the `i`-th conformal block. -/
  blockValue : ι → 𝕜
  /-- Value of the crossing functional on the identity block. -/
  identityContribution : 𝕜
  /-- The crossing sum rule: the functional annihilates the full crossing equation. -/
  crossing : identityContribution + ∑ i, opeCoeffSq i * blockValue i = 0

variable [Ring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype ι]

/-- **Bootstrap exclusion.** If the crossing functional is non-negative on every
conformal block in the spectrum (`hblock`) while contributing strictly positively on
the identity (`hid`), then the crossing sum rule is contradicted — the LHS is
strictly positive yet must equal `0`. Hence the hypothesized spectrum is ruled out. -/
theorem bootstrap_exclusion (D : BootstrapData 𝕜 ι)
    (hblock : ∀ i, 0 ≤ D.blockValue i) (hid : 0 < D.identityContribution) : False := by
  -- Each summand `opeCoeffSq i * blockValue i` is non-negative (unitarity × block ≥ 0).
  have hsummand : ∀ i ∈ (univ : Finset ι), 0 ≤ D.opeCoeffSq i * D.blockValue i :=
    fun i _ => mul_nonneg (D.opeCoeffSq_nonneg i) (hblock i)
  -- Hence the whole OPE-weighted sum is non-negative.
  have hsum : 0 ≤ ∑ i, D.opeCoeffSq i * D.blockValue i := Finset.sum_nonneg hsummand
  -- identity (> 0) + sum (≥ 0) > 0, but crossing says it equals 0.
  have hpos : 0 < D.identityContribution + ∑ i, D.opeCoeffSq i * D.blockValue i :=
    add_pos_of_pos_of_nonneg hid hsum
  rw [D.crossing] at hpos
  exact lt_irrefl 0 hpos

/-- **Spectrum in the swampland.** The packaged no-go: a datum whose crossing
functional is block-positive and identity-positive cannot correspond to a consistent
theory. Same content as `bootstrap_exclusion`, with the exclusion hypotheses bundled. -/
theorem spectrum_in_swampland (D : BootstrapData 𝕜 ι)
    (hexcluding : (∀ i, 0 ≤ D.blockValue i) ∧ 0 < D.identityContribution) : False :=
  bootstrap_exclusion D hexcluding.1 hexcluding.2

/-! ## Anti-vacuity witnesses

Two explicit witnesses show the exclusion mechanism is neither vacuous nor
all-excluding. -/

/-- Squared OPE coefficient `= 1` for the excluded witness. -/
def excludedOpeCoeffSq : Fin 1 → ℚ := fun _ => 1

/-- Block value `= 2` for the excluded witness. -/
def excludedBlockValue : Fin 1 → ℚ := fun _ => 2

/-- The crossing-rule LHS of the excluded witness (identity `= 1`, `opeCoeffSq = 1`,
`blockValue = 2`) evaluates to `1 + 1·2 = 3`, hence `> 0`. Because the crossing sum
rule demands this LHS equal `0`, the value being a *nonzero* `3` is precisely what
makes the exclusion genuine: the spectrum cannot be realized by any consistent
theory. -/
theorem excluded_crossing_lhs_pos :
    (0 : ℚ) < 1 + ∑ i, excludedOpeCoeffSq i * excludedBlockValue i := by
  simp only [excludedOpeCoeffSq, excludedBlockValue, Fin.sum_univ_one]
  norm_num

/-- **Witness (a), EXCLUDED (the exclusion fires).** *Any* `BootstrapData ℚ (Fin 1)`
carrying the excluded parameters — a positive identity contribution (`> 0`) and the
non-negative block value `2 ≥ 0` — is ruled out: `bootstrap_exclusion` yields `False`.
Equivalently, no such `BootstrapData` can exist, because its `crossing` field would
force the strictly-positive LHS `excluded_crossing_lhs_pos` witnesses to vanish. This
is a *genuine, nonzero* exclusion (the LHS is `3`, not `0`). -/
theorem excludedData_fires (D : BootstrapData ℚ (Fin 1))
    (hblock : D.blockValue = excludedBlockValue) (hid : 0 < D.identityContribution) :
    False := by
  refine bootstrap_exclusion D (fun i => ?_) hid
  rw [hblock]; simp only [excludedBlockValue]; norm_num

/-- Witness (b), ALLOWED: an explicit `BootstrapData ℚ (Fin 1)` with identity `= 1`,
squared OPE coefficient `= 1`, and block value `= -1`. It *does* satisfy crossing
(`1 + 1·(-1) = 0`), so it is a legitimate datum — yet its block value is negative, so
the block-positivity hypothesis of the exclusion cannot hold. This shows the bound is
non-trivial: it rules out *some* spectra, not all. -/
def allowedData : BootstrapData ℚ (Fin 1) where
  opeCoeffSq := fun _ => 1
  opeCoeffSq_nonneg := by intro i; norm_num
  blockValue := fun _ => -1
  identityContribution := 1
  crossing := by simp only [Fin.sum_univ_one]; norm_num

/-- The allowed spectrum is *not* excludable: its block-positivity hypothesis
provably fails (block value `-1 < 0`), so `bootstrap_exclusion` does not apply. The
bound therefore does not rule out everything. -/
theorem allowedSpectrum_not_excludable :
    ¬ (∀ i, 0 ≤ allowedData.blockValue i) := by
  intro h
  have h0 := h 0
  simp only [allowedData] at h0
  norm_num at h0

end Physlib.Foundations
