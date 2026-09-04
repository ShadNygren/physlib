/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
/-!

# The Ryu–Takayanagi formula and the Brown–Henneaux match

The **Ryu–Takayanagi (RT) formula** states that the entanglement entropy of a boundary region
equals the length of the minimal bulk geodesic anchored on that region's boundary, divided by
`4G` (Newton's constant):

  `S(ℓ) = Length_geodesic(ℓ) / (4G)`.

This is the sharpest statement of *"spacetime from entanglement"*: an entanglement quantity (`S`)
of the boundary CFT is computed by a purely *geometric* quantity (a minimal-length curve) of the
bulk gravity dual.

In AdS₃/CFT₂ (AdS radius `L_AdS`), the regularized length of the minimal geodesic in the
hyperbolic bulk subtending a boundary interval of length `ℓ` (with UV cutoff `a`) is

  `Length(ℓ) = 2 · L_AdS · log(ℓ/a)`,

so the RT entropy is

  `S_RT(ℓ) = (2 · L_AdS)/(4G) · log(ℓ/a) = (L_AdS/(2G)) · log(ℓ/a)`.

Matching this to the **Calabrese–Cardy** CFT result `S(ℓ) = (c/3) · log(ℓ/a)`
(`Physlib.CalabreseCardy`) forces the log-coefficients to agree, giving the
**Brown–Henneaux relation**

  `c = 3 · L_AdS/(2G)` :

the CFT central charge equals a *bulk geometric quantity*. This closes the loop
**entanglement (S) ↔ geometry (geodesic length) ↔ central charge (c)**. The shared
`log(ℓ/a)` divergence is the CFT UV divergence = the bulk near-boundary divergence: the same
physics on both sides.

This file formalizes, over `ℝ` and with honest side-conditions (`G ≠ 0`, `ℓ, a > 0`):
* `geodesicLength` — the regularized AdS₃ minimal-geodesic length `2·L_AdS·log(ℓ/a)`;
* `rtEntropy` — the RT entropy `Length/(4G)`;
* `rt_entropy_eq` — `rtEntropy = (L_AdS/(2G)) · log(ℓ/a)` (the log-coefficient is a bulk quantity);
* `rt_matches_calabrese_cardy` — under Brown–Henneaux `c = 3·L_AdS/(2G)`, the *bulk geodesic
  length reproduces the Calabrese–Cardy CFT entropy* `(c/3)·log(ℓ/a)` exactly;
* `brown_henneaux_central_charge` — the extraction `c = 3·L_AdS/(2G)`, and the cutoff-independent
  RT entropy difference `(L_AdS/(2G))·log(ℓ₂/ℓ₁)`;
* the **Ising instance** (`L_AdS = 1, G = 3` ⟹ `c = 1/2`) with a nonzero (`1/6`) log-coefficient
  and a strictly positive concrete geodesic length / entropy (anti-vacuity).

This is the keystone step *"entanglement builds geometry,"* building toward
`CFT axioms ⟹ emergent spacetime`. The `c = 1/2` instance is the 2D Ising CFT,
with numerically-measured `c ≈ 0.5023`.

-/

@[expose] public section

namespace Physlib.RyuTakayanagi

open Real

/-- The regularized minimal bulk-geodesic length in AdS₃ (radius `Lads`) subtending a boundary
interval of length `ℓ`, with UV cutoff `a`:
`Length(ℓ) = 2 · Lads · log(ℓ/a)`. This is the *geometric* side of Ryu–Takayanagi. -/
noncomputable def geodesicLength (Lads ℓ a : ℝ) : ℝ := 2 * Lads * Real.log (ℓ / a)

/-- The **Ryu–Takayanagi entropy** `S = Length / (4G)`: the boundary entanglement entropy is the
bulk minimal-geodesic length divided by `4G`. -/
noncomputable def rtEntropy (Lads G ℓ a : ℝ) : ℝ := geodesicLength Lads ℓ a / (4 * G)

/-- **The RT entropy is `(Lads/(2G)) · log(ℓ/a)`.** Unfolding `Length/(4G)`, the log-coefficient is
the *bulk-geometry-determined* quantity `Lads/(2G)`. (`G ≠ 0`.) -/
theorem rt_entropy_eq (Lads G ℓ a : ℝ) (hG : G ≠ 0) :
    rtEntropy Lads G ℓ a = (Lads / (2 * G)) * Real.log (ℓ / a) := by
  unfold rtEntropy geodesicLength
  field_simp
  ring

/-- **Ryu–Takayanagi ↔ Calabrese–Cardy (the bridge).** Given the **Brown–Henneaux** relation
`c = 3·Lads/(2G)` and `G ≠ 0`, the RT entropy — computed from the *bulk geodesic length* — equals
the Calabrese–Cardy CFT entanglement entropy `(c/3)·log(ℓ/a)` exactly. This is *entanglement =
geometry*, machine-checked: the same `log(ℓ/a)` on both sides, with the coefficient matched. -/
theorem rt_matches_calabrese_cardy (Lads G c ℓ a : ℝ) (hG : G ≠ 0)
    (hBH : c = 3 * Lads / (2 * G)) :
    rtEntropy Lads G ℓ a = (c / 3) * Real.log (ℓ / a) := by
  rw [rt_entropy_eq Lads G ℓ a hG, hBH]
  have h2G : (2 * G) ≠ 0 := by simpa using hG
  field_simp

/-- **Brown–Henneaux central charge.** The CFT central charge is *extracted from bulk geometry*:
matching the RT log-coefficient `Lads/(2G)` to the Calabrese–Cardy coefficient `c/3` holds **iff**
`c = 3·Lads/(2G)`. (`G ≠ 0`.) -/
theorem brown_henneaux_central_charge (Lads G c : ℝ) (hG : G ≠ 0) :
    Lads / (2 * G) = c / 3 ↔ c = 3 * Lads / (2 * G) := by
  have h2G : (2 * G) ≠ 0 := by simpa using hG
  rw [div_eq_div_iff h2G (by norm_num : (3 : ℝ) ≠ 0)]
  constructor
  · intro h; field_simp; linarith [h]
  · intro h; field_simp; field_simp at h; linarith [h]

/-- **Cutoff-independent RT entropy difference.** The UV cutoff `a` cancels in a difference of RT
entropies for two intervals `ℓ₁, ℓ₂ > 0`, leaving the geometric, cutoff-independent observable
`(Lads/(2G))·log(ℓ₂/ℓ₁)`. This is the universal content shared by RT and Calabrese–Cardy. -/
theorem rt_entropy_difference (Lads G ℓ₁ ℓ₂ a : ℝ) (hG : G ≠ 0)
    (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) (ha : 0 < a) :
    rtEntropy Lads G ℓ₂ a - rtEntropy Lads G ℓ₁ a
      = (Lads / (2 * G)) * Real.log (ℓ₂ / ℓ₁) := by
  rw [rt_entropy_eq Lads G ℓ₂ a hG, rt_entropy_eq Lads G ℓ₁ a hG]
  rw [Real.log_div (ne_of_gt h₂) (ne_of_gt ha), Real.log_div (ne_of_gt h₁) (ne_of_gt ha),
    Real.log_div (ne_of_gt h₂) (ne_of_gt h₁)]
  ring

/-! ### Ising instance (anti-vacuity)

Choosing `Lads = 1`, `G = 3` gives, via Brown–Henneaux, `c = 3·1/(2·3) = 1/2`: the 2D **Ising**
central charge (numerically-measured `c ≈ 0.5023`). We prove the relation numerically, the
resulting RT log-coefficient is the nonzero `1/6`, and a concrete geodesic length / entropy is
strictly positive — a genuine non-vacuous witness. -/

/-- **Ising Brown–Henneaux.** With `Lads = 1`, `G = 3`, the Brown–Henneaux central charge is
`3·1/(2·3) = 1/2` — the Ising CFT. -/
theorem ising_brown_henneaux : 3 * (1 : ℝ) / (2 * 3) = 1 / 2 := by norm_num

/-- The RT log-coefficient `Lads/(2G)` at the Ising instance `Lads = 1, G = 3`. -/
noncomputable def isingRTSlope : ℝ := (1 : ℝ) / (2 * 3)

/-- The Ising RT log-slope is `1/6` — equal to the Calabrese–Cardy Ising slope `c/3 = (1/2)/3`. -/
theorem ising_rt_slope : isingRTSlope = 1 / 6 := by unfold isingRTSlope; norm_num

/-- **Anti-vacuity (BP 21): the Ising RT log-slope is nonzero.** The bulk-geometric log-coefficient
`1/6` is a genuine nonzero quantity, not `0 = 0`. -/
theorem ising_rt_slope_ne_zero : isingRTSlope ≠ 0 := by rw [ising_rt_slope]; norm_num

/-- **Ising RT reproduces Calabrese–Cardy.** At `Lads = 1, G = 3` (so `c = 1/2` by Brown–Henneaux),
the RT entropy equals the Ising Calabrese–Cardy entropy `(1/6)·log(ℓ/a)` exactly, for any `ℓ, a`. -/
theorem ising_rt_matches_cc (ℓ a : ℝ) :
    rtEntropy 1 3 ℓ a = ((1 / 2 : ℝ) / 3) * Real.log (ℓ / a) := by
  rw [rt_matches_calabrese_cardy 1 3 (1 / 2) ℓ a (by norm_num) (by norm_num)]

/-- **Anti-vacuity (BP 21): a concrete strictly-positive geodesic length.** For the Ising instance
`Lads = 1` and the interval `ℓ = 2`, cutoff `a = 1`, the minimal-geodesic length is
`2·log 2 > 0`: a genuine positive length, not a vacuous `0 = 0`. -/
theorem geodesic_length_pos : 0 < geodesicLength 1 2 1 := by
  unfold geodesicLength
  have hlog : (0 : ℝ) < Real.log (2 / 1) := by
    rw [div_one]; exact Real.log_pos (by norm_num)
  positivity

/-- **Anti-vacuity (BP 21): the concrete Ising RT entropy is strictly positive.** For `ℓ = 2, a = 1`
at the Ising instance `Lads = 1, G = 3`, `S_RT = (1/6)·log 2 > 0` — a nonzero entanglement entropy
built from a nonzero bulk geodesic length. -/
theorem ising_rt_entropy_pos : 0 < rtEntropy 1 3 2 1 := by
  rw [ising_rt_matches_cc 2 1]
  have hlog : (0 : ℝ) < Real.log (2 / 1) := by
    rw [div_one]; exact Real.log_pos (by norm_num)
  have : ((1 / 2 : ℝ) / 3) = 1 / 6 := by norm_num
  rw [this]
  positivity

end Physlib.RyuTakayanagi
