/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Mathlib
/-!

# The BTZ black hole from thermal entanglement

## i. Overview

This module formalizes the tractable thermodynamic core of the flagship
"spacetime from entanglement" statement: the eternal AdS₃ (BTZ) black hole
emerging from the **thermal entanglement** of a boundary conformal field theory.

The eternal AdS₃/BTZ black hole is dual to two copies of a boundary CFT prepared
in the **thermofield-double** state (Maldacena, *Eternal black holes in AdS*).
Tracing out one copy leaves a **thermal (Gibbs)** state at the Hawking temperature
on the other copy. The black-hole **horizon** is the Ryu–Takayanagi surface for the
entire boundary, so its length divided by `4G` equals the boundary **thermal
entanglement entropy**:

  S_thermal  =  Area(horizon) / (4G)  =  S_Bekenstein–Hawking.

In words (Van Raamsdonk, *Building up spacetime with quantum entanglement*):
**the black hole IS the thermal entanglement of the thermofield double** — the
horizon area is literally the boundary thermal entanglement entropy.

We formalize the standard BTZ relations as real-valued functions of the AdS radius
`L`, Newton's constant `G`, and the horizon radius `r₊`, and PROVE:

* the entanglement = horizon identity `thermal_entropy_eq_bekenstein_hawking`
  (boundary thermal entropy = horizon area / 4G),
* the first law of black-hole thermodynamics `btz_first_law` (`dM = T dS`),
* the Smarr-type relation `btz_smarr` (`M = ½ T S`),
* positivity and monotonicity of the horizon area, temperature, entropy and mass,
* a concrete strictly-positive BTZ witness (`L = 1, G = 1, r₊ = 2`).

## ii. Key results

- `thermal_entropy_eq_bekenstein_hawking` : boundary thermal (thermofield-double)
  entropy = black-hole horizon area / 4G — **the black hole IS the thermal
  entanglement** (headline).
- `btz_first_law` : `dM/dr₊ = T · dS/dr₊` — thermodynamic consistency `dM = T dS`.
- `btz_smarr` : `M = ½ T S` — the 2+1D Smarr relation.
- positivity/monotonicity lemmas + a strictly-positive concrete BTZ witness.

## iii. Honest scope note

What is **DERIVED** here are the thermodynamic identities *among the BTZ
parameters* — the relations tying horizon area, Hawking temperature, entropy and
ADM mass together (entanglement = horizon area/4G, `dM = T dS`, `M = ½ T S`), and
their positivity/monotonicity. This is the parameter-level thermodynamics of the
black hole.

What is **NOT** done here (and is not claimed): a differential-geometric derivation
of the BTZ *metric* as a solution of the Einstein equations, nor an operator-theoretic
construction of the thermofield-double state. There is NO differential geometry and
NO operator theory in this file — only real analysis. The BTZ geometry's parameters
and their thermodynamic identities are what is formalized.

## iv. References

- G. 't Hooft dimensional analysis; M. Bañados, C. Teitelboim, J. Zanelli,
  *The black hole in three-dimensional space-time* (BTZ), Phys. Rev. Lett. 69 (1992).
- J. Maldacena, *Eternal black holes in anti-de Sitter*, JHEP 04 (2003) 021
  (eternal BH = thermofield double).
- M. Van Raamsdonk, *Building up spacetime with quantum entanglement*,
  Gen. Rel. Grav. 42 (2010) 2323 (spacetime from entanglement).
- S. Ryu, T. Takayanagi, *Holographic derivation of entanglement entropy*
  (horizon = RT surface of the whole boundary).

-/

namespace Physlib.BTZThermal

open Real

/-!

## A. The BTZ thermodynamic quantities

Standard BTZ (AdS₃, radius `L`, Newton constant `G`, horizon radius `r₊ > 0`).

-/

/-- The **Hawking temperature** of the BTZ black hole, `T = r₊ / (2π L²)`.
This is the temperature of the boundary thermal (Gibbs) state obtained by tracing
out one copy of the thermofield double. -/
noncomputable def hawkingTemp (L rp : ℝ) : ℝ := rp / (2 * Real.pi * L ^ 2)

/-- The **horizon length** (the "area" of the horizon in 2+1 dimensions): the horizon
is a circle of radius `r₊`, so its length is its circumference `2π r₊`. This is the
Ryu–Takayanagi surface for the whole boundary. -/
noncomputable def horizonLength (rp : ℝ) : ℝ := 2 * Real.pi * rp

/-- The **Bekenstein–Hawking entropy** `S_BH = Area / (4G) = (2π r₊)/(4G) = π r₊/(2G)`.
For the BTZ black hole the horizon "area" is the horizon length. -/
noncomputable def bekensteinHawkingEntropy (G rp : ℝ) : ℝ := horizonLength rp / (4 * G)

/-- The **BTZ ADM mass** `M = r₊² / (8 G L²)`. -/
noncomputable def btzMass (L G rp : ℝ) : ℝ := rp ^ 2 / (8 * G * L ^ 2)

/-- The boundary **thermal (thermofield-double) entropy**, written as a Cardy-type
function of the temperature `T`: `S_thermal = π² L² T / G`. Substituting the Hawking
temperature `T = r₊/(2π L²)` reproduces the Bekenstein–Hawking entropy `π r₊/(2G)`
(see `thermal_entropy_eq_bekenstein_hawking`). -/
noncomputable def thermalEntropy (L G T : ℝ) : ℝ := Real.pi ^ 2 * L ^ 2 * T / G

/-!

## B. The entanglement = horizon identity (headline)

-/

/-- The anchor identity: the Bekenstein–Hawking entropy IS the horizon area divided
by `4G`. This is definitional but records the central fact "entropy = area / 4G". -/
theorem btz_entropy_eq_horizon (G rp : ℝ) :
    bekensteinHawkingEntropy G rp = horizonLength rp / (4 * G) := rfl

/-- **The black hole IS the thermal entanglement.** The boundary thermal
(thermofield-double) entropy, evaluated at the Hawking temperature, equals the
black-hole horizon area divided by `4G` (the Bekenstein–Hawking entropy).

This is the tractable formalization of "spacetime (a BTZ horizon) emerging from
thermal entanglement": `S_thermal(T_Hawking) = Area(horizon)/(4G)`. -/
theorem thermal_entropy_eq_bekenstein_hawking
    (L G rp : ℝ) (hL : L ≠ 0) :
    thermalEntropy L G (hawkingTemp L rp) = bekensteinHawkingEntropy G rp := by
  unfold thermalEntropy hawkingTemp bekensteinHawkingEntropy horizonLength
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-!

## C. The first law of black-hole thermodynamics: `dM = T dS`

Computed via `HasDerivAt`. With `M = r₊²/(8GL²)`, `S = 2π r₊/(4G)` and
`T = r₊/(2π L²)`, we have `dM/dr₊ = r₊/(4GL²)`, `dS/dr₊ = π/(2G)`, and
`T · dS/dr₊ = r₊/(4GL²)`, so the first law closes EXACTLY with the standard
BTZ normalization (`horizonLength = 2π r₊`, no extra `L`-factor).

-/

/-- The derivative of the BTZ mass in the horizon radius: `dM/dr₊ = r₊/(4GL²)`. -/
theorem hasDerivAt_btzMass (L G rp : ℝ) (hG : G ≠ 0) (hL : L ≠ 0) :
    HasDerivAt (btzMass L G) (rp / (4 * G * L ^ 2)) rp := by
  have h : HasDerivAt (fun x : ℝ => x ^ 2 / (8 * G * L ^ 2))
      ((2 * rp ^ (2 - 1)) / (8 * G * L ^ 2)) rp :=
    (hasDerivAt_pow 2 rp).div_const _
  have hval : (2 * rp ^ (2 - 1)) / (8 * G * L ^ 2) = rp / (4 * G * L ^ 2) := by
    simp
    field_simp
    ring
  rw [hval] at h
  exact h

/-- The derivative of the Bekenstein–Hawking entropy in the horizon radius:
`dS/dr₊ = π/(2G)`. -/
theorem hasDerivAt_bekensteinHawkingEntropy (G rp : ℝ) (hG : G ≠ 0) :
    HasDerivAt (bekensteinHawkingEntropy G) (Real.pi / (2 * G)) rp := by
  have h : HasDerivAt (fun x : ℝ => 2 * Real.pi * x / (4 * G))
      (2 * Real.pi * 1 / (4 * G)) rp := by
    have hx : HasDerivAt (fun x : ℝ => 2 * Real.pi * x) (2 * Real.pi * 1) rp := by
      simpa using (hasDerivAt_id rp).const_mul (2 * Real.pi)
    exact hx.div_const _
  have hval : 2 * Real.pi * 1 / (4 * G) = Real.pi / (2 * G) := by
    field_simp
    ring
  rw [hval] at h
  exact h

/-- **The first law of BTZ black-hole thermodynamics**, `dM = T dS`: the derivative
of the mass with respect to the horizon radius equals the Hawking temperature times
the derivative of the entropy. Closes EXACTLY with the standard normalization. -/
theorem btz_first_law (L G rp : ℝ) (hG : G ≠ 0) (hL : L ≠ 0) :
    deriv (btzMass L G) rp
      = hawkingTemp L rp * deriv (bekensteinHawkingEntropy G) rp := by
  rw [(hasDerivAt_btzMass L G rp hG hL).deriv,
      (hasDerivAt_bekensteinHawkingEntropy G rp hG).deriv]
  unfold hawkingTemp
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-!

## D. The Smarr-type relation `M = ½ T S`

-/

/-- The 2+1D **Smarr relation** `M = ½ T S`: the ADM mass is half the temperature
times the entropy. With `M = r₊²/(8GL²)`, `T = r₊/(2π L²)` and `S = π r₊/(2G)`,
one checks `½ T S = ½ · r₊/(2π L²) · π r₊/(2G) = r₊²/(8GL²) = M`. -/
theorem btz_smarr (L G rp : ℝ) (hG : G ≠ 0) (hL : L ≠ 0) :
    btzMass L G rp
      = (1 / 2) * hawkingTemp L rp * bekensteinHawkingEntropy G rp := by
  unfold btzMass hawkingTemp bekensteinHawkingEntropy horizonLength
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-!

## E. Positivity and monotonicity

Bigger black hole ⇒ larger horizon, temperature, entropy, mass, and hence more
boundary thermal entanglement.

-/

/-- The horizon length is strictly positive for a genuine (`r₊ > 0`) black hole. -/
theorem btz_horizon_pos (rp : ℝ) (hrp : 0 < rp) : 0 < horizonLength rp := by
  unfold horizonLength
  positivity

/-- The Hawking temperature is strictly positive for `r₊ > 0`, `L ≠ 0`. -/
theorem btz_temp_pos (L rp : ℝ) (hrp : 0 < rp) (hL : L ≠ 0) :
    0 < hawkingTemp L rp := by
  unfold hawkingTemp
  have : 0 < 2 * Real.pi * L ^ 2 := by positivity
  positivity

/-- The Bekenstein–Hawking entropy is strictly positive for `r₊ > 0`, `G > 0`. -/
theorem btz_entropy_pos (G rp : ℝ) (hrp : 0 < rp) (hG : 0 < G) :
    0 < bekensteinHawkingEntropy G rp := by
  unfold bekensteinHawkingEntropy horizonLength
  positivity

/-- The BTZ mass is strictly positive for `r₊ > 0`, `G > 0`, `L ≠ 0`. -/
theorem btz_mass_pos (L G rp : ℝ) (hrp : 0 < rp) (hG : 0 < G) (hL : L ≠ 0) :
    0 < btzMass L G rp := by
  unfold btzMass
  have : 0 < 8 * G * L ^ 2 := by positivity
  positivity

/-- **Monotonicity: a bigger black hole carries more entanglement.** The
Bekenstein–Hawking entropy is strictly increasing in the horizon radius (`G > 0`). -/
theorem entropy_monotone_in_horizon (G : ℝ) (hG : 0 < G) :
    StrictMono (bekensteinHawkingEntropy G) := by
  intro a b hab
  unfold bekensteinHawkingEntropy horizonLength
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnum : 2 * Real.pi * a < 2 * Real.pi * b := by
    have h2pi : 0 < 2 * Real.pi := by positivity
    exact mul_lt_mul_of_pos_left hab h2pi
  have h4G : 0 < 4 * G := by positivity
  exact div_lt_div_of_pos_right hnum h4G

/-!

## F. Anti-vacuity witness: a concrete, strictly-positive BTZ black hole

Take `L = 1, G = 1, r₊ = 2`. Then the horizon length is `4π`, the Hawking
temperature is `1/π`, the entropy is `π`, and the mass is `1/2` — all strictly
positive: a genuine black hole (not the degenerate `r₊ = 0` empty-AdS boundary
case). The entanglement = horizon identity and the first law both hold on it.

-/

/-- Witness horizon length: `horizonLength 2 = 4π`. -/
theorem witness_horizonLength : horizonLength 2 = 4 * Real.pi := by
  unfold horizonLength; ring

/-- Witness horizon length is strictly positive. -/
theorem witness_horizonLength_pos : 0 < horizonLength 2 :=
  btz_horizon_pos 2 (by norm_num)

/-- Witness Hawking temperature: `hawkingTemp 1 2 = 1/π`. -/
theorem witness_hawkingTemp : hawkingTemp 1 2 = 1 / Real.pi := by
  unfold hawkingTemp
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- Witness Hawking temperature is strictly positive. -/
theorem witness_hawkingTemp_pos : 0 < hawkingTemp 1 2 :=
  btz_temp_pos 1 2 (by norm_num) (by norm_num)

/-- Witness Bekenstein–Hawking entropy: `bekensteinHawkingEntropy 1 2 = π`. -/
theorem witness_entropy : bekensteinHawkingEntropy 1 2 = Real.pi := by
  unfold bekensteinHawkingEntropy horizonLength; ring

/-- Witness entropy is strictly positive. -/
theorem witness_entropy_pos : 0 < bekensteinHawkingEntropy 1 2 :=
  btz_entropy_pos 1 2 (by norm_num) (by norm_num)

/-- Witness BTZ mass: `btzMass 1 1 2 = 1/2`. -/
theorem witness_mass : btzMass 1 1 2 = 1 / 2 := by
  unfold btzMass; norm_num

/-- Witness mass is strictly positive. -/
theorem witness_mass_pos : 0 < btzMass 1 1 2 :=
  btz_mass_pos 1 1 2 (by norm_num) (by norm_num) (by norm_num)

/-- The **entanglement = horizon** identity holds on the concrete witness:
`thermalEntropy 1 1 (hawkingTemp 1 2) = bekensteinHawkingEntropy 1 2`. -/
theorem witness_thermal_eq_horizon :
    thermalEntropy 1 1 (hawkingTemp 1 2) = bekensteinHawkingEntropy 1 2 :=
  thermal_entropy_eq_bekenstein_hawking 1 1 2 (by norm_num)

/-- The **first law** `dM = T dS` holds on the concrete witness. -/
theorem witness_first_law :
    deriv (btzMass 1 1) 2
      = hawkingTemp 1 2 * deriv (bekensteinHawkingEntropy 1) 2 :=
  btz_first_law 1 1 2 (by norm_num) (by norm_num)

/-- The **Smarr relation** `M = ½ T S` holds on the concrete witness. -/
theorem witness_smarr :
    btzMass 1 1 2 = (1 / 2) * hawkingTemp 1 2 * bekensteinHawkingEntropy 1 2 :=
  btz_smarr 1 1 2 (by norm_num) (by norm_num)

end Physlib.BTZThermal
