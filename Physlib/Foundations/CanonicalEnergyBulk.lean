/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib
/-!

# Faulkner–Li / Hollands–Wald bulk positive-energy bridge (Lean-tractable functional core)

## i. Overview (forest-level)

**What this encodes, honestly.** In the emergent-spacetime program (Faulkner–Guica–Hartman–Myers–
Van Raamsdonk 2013; Lashkari–Van Raamsdonk 2016; Hollands–Wald canonical energy), the boundary
*second-order relative entropy* `S_rel⁽²⁾` of a linearized perturbation of a holographic state EQUALS
the *bulk gravitational canonical energy* `E_canonical[h]` of the corresponding metric perturbation `h`
on the Ryu–Takayanagi wedge. Because `E_canonical[h]` is a manifestly POSITIVE-definite quadratic
functional of `h`, boundary relative-entropy positivity (which we proved elsewhere equals the quantum
Fisher information `≥ 0`) becomes a BULK statement: **the emergent geometry's canonical
energy is non-negative** — a linearized positive-energy / stability condition on emergent spacetime.
In one accessible sentence: *entanglement (relative-entropy positivity on the boundary) implies the
emergent bulk geometry is stable / obeys a linearized positive-energy condition.*

This file formalizes the LEAN-TRACTABLE FUNCTIONAL CORE of that equivalence — the same honesty level
as the companion linearized-Einstein development, which formalizes the Faulkner argument's
logical/functional skeleton over `ℝ` rather than building general relativity. We do NOT build
differential geometry or operator theory here.

## ii. Representation used

We use the **discrete positive quadratic form** `∑ i, w i * (h i)^2` over `Fin n` as the tractable
core. A positive-weighted sum of squares is a fully honest model of the Hollands–Wald canonical energy
(itself a positive-definite quadratic form in the perturbation and its flux); the discretization is the
finite-dimensional version of the weighted radial integral `∫ z, w z * (h z)^2` over the RT wedge. The
discrete representation makes STRICT positivity of the anti-vacuity witness clean to prove
(`Finset.sum_pos`).

## iii. Key results

- `bulkCanonicalEnergy` : the bulk canonical energy `E_canonical[h] = ∑ i, w i * (h i)^2` (positive
  weight `w`), the Hollands–Wald symplectic energy of the metric perturbation `h`.
- `boundaryFisher` : the boundary second-order relative entropy / quantum Fisher information
  `∑ i, d i^2 / p i`.
- `dictionary` : the emergent-gravity dictionary mapping boundary perturbation data `(p, d)` to the
  bulk field `h`, via the positive kernel `w i = 1 / p i`, `h i = d i`.
- `bulk_canonical_energy_nonneg` : `(∀ i, 0 ≤ w i) → 0 ≤ bulkCanonicalEnergy w h` — the bulk
  positive-energy statement.
- `faulkner_li_bridge` : bulk `E_canonical` = boundary `S_rel⁽²⁾` (the Faulkner–Li dictionary), a full
  general equality on the dictionary kernel (not merely witness-level).
- `emergent_positive_energy` : boundary relative-entropy positivity ⟹ bulk canonical energy `≥ 0`
  (the payoff: entanglement ⟹ emergent geometry is stable).
- Anti-vacuity: a concrete NONZERO perturbation with STRICTLY POSITIVE canonical energy, and the
  matching boundary witness giving the same value through the bridge.

## iv. References

- Faulkner, Guica, Hartman, Myers, Van Raamsdonk, *Gravitation from entanglement in holographic CFTs*
  (2014).
- Lashkari, Van Raamsdonk, *Canonical energy is quantum Fisher information* (2016).
- Hollands, Wald, *Stability of black holes and black branes* (2013).

-/

@[expose] public section

namespace Physlib.CanonicalEnergyBulk

open Finset

/-- **Bulk gravitational canonical energy** (Hollands–Wald) in the Lean-tractable discrete
representation. For a linearized metric perturbation `h : Fin n → ℝ` on the (discretized) radial
coordinate of the Ryu–Takayanagi wedge, and a positive symplectic/metric weight `w : Fin n → ℝ`
(in AdS a specific positive function; here abstracted as any `w ≥ 0`), the canonical energy is the
positive-weighted sum of squares
  `E_canonical[h] = ∑ i, w i * (h i)^2`.
This is the finite-dimensional discretization of the weighted radial integral
`∫ z in Ioi 0, w z * (h z)^2`; a positive quadratic form is the essential Hollands–Wald content. -/
noncomputable def bulkCanonicalEnergy {n : ℕ} (w h : Fin n → ℝ) : ℝ :=
  ∑ i, w i * (h i) ^ 2

/-- **Boundary second-order relative entropy / quantum Fisher information.**
For a reference distribution `p : Fin n → ℝ` (with `p i > 0`) and a perturbation direction
`d : Fin n → ℝ`, the second-order relative entropy `S_rel⁽²⁾` equals the classical Fisher information
  `∑ i, d i ^ 2 / p i`.
This is the boundary quantity that is non-negative. -/
noncomputable def boundaryFisher {n : ℕ} (p d : Fin n → ℝ) : ℝ :=
  ∑ i, (d i) ^ 2 / p i

/-- **The emergent-gravity dictionary.** The Faulkner–Li map takes boundary perturbation data
`(p, d)` to the bulk field, choosing the bulk metric weight to be the positive kernel `w i = 1 / p i`
and the bulk perturbation field to be `h i = d i`. This is the concrete positive kernel realizing the
holographic dictionary `boundary S_rel⁽²⁾ ↦ bulk E_canonical` in the discrete toy. -/
noncomputable def dictionaryWeight {n : ℕ} (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 1 / p i

/-- The bulk field assigned by the dictionary to the boundary perturbation direction `d`. -/
def dictionaryField {n : ℕ} (d : Fin n → ℝ) : Fin n → ℝ := d

/-! ### A. The bulk positive-energy statement -/

/-- **Bulk canonical energy is non-negative.** With a non-negative symplectic weight `w ≥ 0`, the
Hollands–Wald canonical energy `E_canonical[h] = ∑ w i (h i)²` is `≥ 0` for every perturbation `h`,
because it is a positive-weighted sum of squares. This is the bulk linearized positive-energy /
stability statement. -/
theorem bulk_canonical_energy_nonneg {n : ℕ} (w h : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ bulkCanonicalEnergy w h := by
  unfold bulkCanonicalEnergy
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hw i) (sq_nonneg _)

/-! ### B. The Faulkner–Li dictionary: bulk = boundary -/

/-- **The Faulkner–Li dictionary (bulk = boundary), full general equality.** Under the emergent-gravity
dictionary — bulk weight `w = 1/p`, bulk field `h = d` — the bulk gravitational canonical energy
`E_canonical[h]` EQUALS the boundary second-order relative entropy / quantum Fisher information
`S_rel⁽²⁾[p, d]`, for ALL `p` and `d` (not merely on a witness):
  `bulkCanonicalEnergy (1/p) d = boundaryFisher p d`.
This is the Lashkari–Van Raamsdonk / Faulkner–Li dictionary in the discrete toy: canonical energy IS
quantum Fisher information. -/
theorem faulkner_li_bridge {n : ℕ} (p d : Fin n → ℝ) :
    bulkCanonicalEnergy (dictionaryWeight p) (dictionaryField d) = boundaryFisher p d := by
  unfold bulkCanonicalEnergy boundaryFisher dictionaryWeight dictionaryField
  apply Finset.sum_congr rfl
  intro i _
  rw [one_div, div_eq_inv_mul]

/-! ### C. Boundary Fisher positivity -/

/-- **Boundary relative-entropy / Fisher positivity.** With a
strictly positive reference distribution `p > 0`, the boundary second-order relative entropy is
non-negative: `0 ≤ boundaryFisher p d`. -/
theorem boundary_fisher_nonneg {n : ℕ} (p d : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    0 ≤ boundaryFisher p d := by
  unfold boundaryFisher
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (hp i).le

/-! ### D. The payoff: entanglement ⟹ emergent geometry obeys the positive-energy condition -/

/-- **Emergent positive energy (the payoff corollary).** Boundary relative-entropy positivity implies
the bulk canonical energy is non-negative. Concretely: with a strictly positive reference distribution
`p > 0`, the bulk canonical energy of the dictionary-image of `(p, d)` is `≥ 0`:
  `(∀ i, 0 < p i) → 0 ≤ bulkCanonicalEnergy (dictionaryWeight p) (dictionaryField d)`.
Reading: **entanglement (boundary `S_rel⁽²⁾ ≥ 0`) ⟹ the emergent bulk geometry satisfies the linearized
positive-energy / stability condition.** Proof routes through the Faulkner–Li bridge (`= boundaryFisher`)
and boundary Fisher positivity — equivalently directly through the nonneg dictionary weight `1/p ≥ 0`. -/
theorem emergent_positive_energy {n : ℕ} (p d : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    0 ≤ bulkCanonicalEnergy (dictionaryWeight p) (dictionaryField d) := by
  rw [faulkner_li_bridge]
  exact boundary_fisher_nonneg p d hp

/-- Equivalent direct form of the payoff: boundary Fisher `≥ 0` transports to bulk canonical energy
`≥ 0` through the bridge, an explicit `S_rel⁽²⁾ ≥ 0 → E_canonical ≥ 0` implication. -/
theorem emergent_positive_energy_of_fisher {n : ℕ} (p d : Fin n → ℝ)
    (hFisher : 0 ≤ boundaryFisher p d) :
    0 ≤ bulkCanonicalEnergy (dictionaryWeight p) (dictionaryField d) := by
  rw [faulkner_li_bridge]; exact hFisher

/-! ### E. Anti-vacuity witnesses

A concrete NONZERO perturbation with STRICTLY POSITIVE canonical energy, and the matching boundary
witness giving the SAME positive value through the bridge — so the equivalence is non-degenerate. -/

/-- Bulk witness data: two radial cells, unit metric weight, perturbation `h = ![1, 0]` (nonzero). -/
def witnessW : Fin 2 → ℝ := fun _ => 1
def witnessH : Fin 2 → ℝ := ![1, 0]

/-- Boundary witness data: distribution `p = ![1/2, 1/2]`, perturbation
direction `d = ![1, 0]`. Under the dictionary `w = 1/p = ![2, 2]`, `h = d = ![1, 0]`. -/
noncomputable def witnessP : Fin 2 → ℝ := ![1/2, 1/2]
def witnessD : Fin 2 → ℝ := ![1, 0]

/-- **Strict positivity of the bulk witness.** The nonzero perturbation `h = ![1,0]` with unit weight
carries GENUINE positive canonical energy: `0 < E_canonical = 1`. This defeats vacuity — the theorems
are not trivially about `h ≡ 0`. -/
theorem witness_bulk_energy_pos : 0 < bulkCanonicalEnergy witnessW witnessH := by
  unfold bulkCanonicalEnergy witnessW witnessH
  simp [Fin.sum_univ_two]

/-- The bulk witness canonical energy has the exact value `1`. -/
theorem witness_bulk_energy_eq_one : bulkCanonicalEnergy witnessW witnessH = 1 := by
  unfold bulkCanonicalEnergy witnessW witnessH
  simp [Fin.sum_univ_two]

/-- The boundary witness Fisher information has the exact value `2` (`= 1²/(1/2) + 0²/(1/2)`). -/
theorem witness_boundary_fisher_eq_two : boundaryFisher witnessP witnessD = 2 := by
  unfold boundaryFisher witnessP witnessD
  norm_num [Fin.sum_univ_two]

/-- **The bulk = boundary agreement on the witness (non-degenerate bridge).** The Faulkner–Li bridge
maps the boundary witness `(p, d)` to a bulk canonical energy EQUAL to the boundary Fisher value `2`,
and this value is STRICTLY positive — so the bulk↔boundary equivalence is realized on genuine,
energy-carrying data, not vacuously. -/
theorem witness_bridge_agrees :
    bulkCanonicalEnergy (dictionaryWeight witnessP) (dictionaryField witnessD)
      = boundaryFisher witnessP witnessD :=
  faulkner_li_bridge witnessP witnessD

/-- The dictionary image of the boundary witness carries STRICTLY positive bulk canonical energy
(`= 2 > 0`): entanglement on this witness genuinely produces a stable, positive-energy emergent
geometry. -/
theorem witness_emergent_energy_pos :
    0 < bulkCanonicalEnergy (dictionaryWeight witnessP) (dictionaryField witnessD) := by
  rw [witness_bridge_agrees, witness_boundary_fisher_eq_two]; norm_num

end Physlib.CanonicalEnergyBulk
