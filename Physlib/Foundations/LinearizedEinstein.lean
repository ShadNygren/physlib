/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib

/-!

# Linearized Einstein equations from the entanglement first law (Faulkner et al. 2013)

## i. Overview (forest level)

This file formalizes, in a Lean-tractable 1+1D / AdS₃ toy form, the keystone result of
Faulkner, Guica, Hartman, Myers and Van Raamsdonk (*Gravitation from Entanglement in
Holographic CFTs*, JHEP 2014, arXiv:1312.7856): **the entanglement "first law" of a
holographic CFT, together with the Ryu–Takayanagi formula, implies the LINEARIZED
Einstein equations of the emergent bulk geometry.**

In plain terms: if the quantum entanglement of every boundary region behaves the way
thermodynamics demands (the first law `δS = δ⟨H_mod⟩`), then the spacetime it "weaves"
must, to first order, obey Einstein's equations. Gravity is not put in by hand — it is
*forced* by entanglement. That is the emergent-dynamics half of the program (the
emergent-kinematics half being that entropy = geodesic length via Ryu–Takayanagi).

## ii. The physics chain being encoded

1. **RT + first law.** For a ball-shaped boundary region (in 1+1D CFT, an interval of
   half-width `ℓ` centered at `p`), the entanglement entropy `S` equals a bulk
   minimal-surface area over `4G` (Ryu–Takayanagi), and the modular Hamiltonian `H_mod`
   generates the first law `δS = δ⟨H_mod⟩` under a first-order variation `δ` of the state.

2. **Modular energy = smeared boundary stress tensor.** For an interval, the modular
   energy is the boundary stress tensor `⟨T⟩` integrated against the interval's conformal
   Killing vector `ξ`, whose profile is the *parabolic ball weight*
   `w(x) = ℓ² − (x − p)²` — positive in the interior, vanishing at the two endpoints.

3. **RT area variation = a bulk (canonical-energy) integral.** Faulkner et al. re-express
   `δ(Area/4G)`, via Stokes' theorem and the Hamiltonian constraint, as a bulk integral of
   the *linearized Einstein tensor* `δG` contracted with `ξ`, plus the boundary
   stress-tensor term. Setting the two sides equal gives, for every region, a weighted
   integral identity between `δG` and `δT`.

4. **"For all regions" ⟹ "pointwise" — the crux.** The first law holding for *every*
   interval (all centers `p`, all sizes `ℓ`) forces the bulk integrand to vanish
   pointwise: `δG(x) = 8πG · δT(x)`. This "an integral that vanishes over every centered
   window has zero integrand" step is the *fundamental lemma of the calculus of
   variations* for the ball weight — and it is the mathematical heart of the derivation.

## iii. The Lean encoding (honest toy)

Building covariant tensors / differential geometry in Mathlib is intractable, so we
formalize the **logical skeleton** with the physical densities as real functions of a
single bulk/boundary coordinate `x : ℝ` (sufficient for the 1+1D toy):

* `δG δT : ℝ → ℝ`      — linearized Einstein-tensor density and stress-tensor density.
* `ballWeight p ℓ x = ℓ² − (x − p)²`   — the conformal Killing / modular weight.
* `modularIntegral f p ℓ = ∫ x in (p−ℓ)..(p+ℓ), ballWeight p ℓ x * f x`
                          — the smeared quantity (`δS`-side or `δ⟨H_mod⟩`-side).
* `firstLaw`: `∀ p ℓ, 0 < ℓ → modularIntegral δG p ℓ = 8πG · modularIntegral δT p ℓ`
                          — the entanglement first law, region by region.

The **main theorem** `linearized_einstein_of_first_law` is step 4: `firstLaw` for all
regions, plus continuity of `δG, δT`, implies `∀ x, δG x = 8πG · δT x` — the pointwise
linearized Einstein equation. Its engine is `fundamental_lemma_ball_weight`, the
fundamental lemma of the calculus of variations for `ballWeight`, proved here from scratch
by a shrinking-window / normalized-limit argument (no calculus-of-variations library is
assumed): the window mass `∫ ballWeight = 4ℓ³/3` is positive, and continuity makes the
weighted average converge to the pointwise value, so a value that is `0` for every window
must be `0` at the point.

## iv. Non-vacuity

We verify the machinery is not vacuous: the closed form `modularIntegral 1 0 1 = 4/3`
(positive window mass), a trivial satisfying instance (`δG = δT = 0`), and a *nonzero*
satisfying instance (`δT = 1`, `δG = 8π`, `G = 1`) where the first law holds with both
sides equal and the conclusion is the genuine nonzero relation `δG x = 8π · 1`.

-/

@[expose] public section

namespace Physlib.LinearizedEinstein

open intervalIntegral MeasureTheory

/-- The Einstein coupling constant `8πG` for a given Newton constant `G`. -/
noncomputable def einsteinConstant (G : ℝ) : ℝ := 8 * Real.pi * G

/-- The conformal Killing / modular weight of the interval of half-width `ℓ` centered at
`p`: the parabola `ℓ² − (x − p)²`, positive strictly inside the interval and vanishing at
the two endpoints `p ± ℓ`. This is the profile of the boundary conformal Killing vector
`ξ` that generates modular flow for an interval in a 1+1D CFT. -/
def ballWeight (p ℓ x : ℝ) : ℝ := ℓ ^ 2 - (x - p) ^ 2

/-- The modular integral of a density `f` over the interval of half-width `ℓ` centered at
`p`: `∫_{p-ℓ}^{p+ℓ} ballWeight · f`. On the `δS`-side (`f = δG`) this is the RT
area-variation; on the `δ⟨H_mod⟩`-side (`f = δT`) it is the smeared boundary stress
tensor. The entanglement first law equates the two. -/
noncomputable def modularIntegral (f : ℝ → ℝ) (p ℓ : ℝ) : ℝ :=
  ∫ x in (p - ℓ)..(p + ℓ), ballWeight p ℓ x * f x

/-- **Window mass.** The total mass of the ball weight over its interval is
`∫_{p-ℓ}^{p+ℓ} (ℓ² − (x−p)²) dx = 4ℓ³/3`. For `ℓ > 0` this is strictly positive, which is
what makes the normalized shrinking-window average a genuine average (and drives the
fundamental lemma below). Proved by the fundamental theorem of calculus with the explicit
antiderivative `ℓ²x − (x−p)³/3`. -/
theorem weight_mass (p ℓ : ℝ) :
    ∫ x in (p - ℓ)..(p + ℓ), ballWeight p ℓ x = 4 * ℓ ^ 3 / 3 := by
  unfold ballWeight
  have key : ∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2)
      = (ℓ ^ 2 * (p + ℓ) - ((p + ℓ) - p) ^ 3 / 3)
        - (ℓ ^ 2 * (p - ℓ) - ((p - ℓ) - p) ^ 3 / 3) := by
    apply integral_eq_sub_of_hasDerivAt (f := fun x => ℓ ^ 2 * x - (x - p) ^ 3 / 3)
    · intro x _
      have h1 : HasDerivAt (fun x : ℝ => ℓ ^ 2 * x) (ℓ ^ 2) x := by
        simpa using (hasDerivAt_id x).const_mul (ℓ ^ 2)
      have h2 : HasDerivAt (fun x : ℝ => (x - p) ^ 3 / 3) ((x - p) ^ 2) x := by
        have h := ((hasDerivAt_id x).sub_const p).pow 3
        simp only [id_eq, Nat.cast_ofNat] at h
        have h' := h.div_const 3
        have e : (3 : ℝ) * (x - p) ^ (3 - 1) * 1 / 3 = (x - p) ^ 2 := by norm_num
        rw [e] at h'
        exact h'
      exact h1.sub h2
    · exact (by fun_prop : Continuous fun x : ℝ => (ℓ ^ 2 - (x - p) ^ 2)).intervalIntegrable _ _
  rw [key]; ring

/-- **Fundamental lemma of the calculus of variations for the ball weight** (the crux of
the Faulkner argument, step 4). If `H` is continuous and its modular integral over *every*
centered window vanishes, then `H p = 0` for every `p`.

Proof: fix `p` and suppose `H p ≠ 0`, so `c := |H p| > 0`. By continuity choose `δ` with
`|H x − H p| < c/2` for `|x − p| < δ`, and take `ℓ = δ/2`. Split the (zero) window integral
as `∫ w·(H − H p) + H p · ∫ w`; the second term is `H p · 4ℓ³/3` by `weight_mass`. On the
window `|w| ≤ ℓ²` and `|H − H p| ≤ c/2`, so the first term is bounded by
`(ℓ²·c/2)·(2ℓ) = c·ℓ³`. Hence `c · 4ℓ³/3 = |∫ w·(H − H p)| ≤ c·ℓ³`, i.e. `4/3 ≤ 1` — a
contradiction. So `H p = 0`. -/
theorem fundamental_lemma_ball_weight (H : ℝ → ℝ) (hH : Continuous H) (p : ℝ)
    (hzero : ∀ ℓ, 0 < ℓ → modularIntegral H p ℓ = 0) :
    H p = 0 := by
  unfold modularIntegral ballWeight at hzero
  by_contra hne
  set c := |H p| with hc
  have hcpos : 0 < c := abs_pos.mpr hne
  have hCA : ContinuousAt H p := hH.continuousAt
  rw [Metric.continuousAt_iff] at hCA
  obtain ⟨δ, hδ, hδp⟩ := hCA (c / 2) (by linarith)
  set ℓ := δ / 2 with hℓdef
  have hℓ : 0 < ℓ := by positivity
  have hle : p - ℓ ≤ p + ℓ := by linarith
  -- Uniform smallness of `|ballWeight · (H − H p)|` on the window.
  have hwbound : ∀ x ∈ Set.uIoc (p - ℓ) (p + ℓ),
      |ℓ ^ 2 - (x - p) ^ 2| * |H x - H p| ≤ ℓ ^ 2 * (c / 2) := by
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    have hsq : (x - p) ^ 2 ≤ ℓ ^ 2 := by nlinarith [hx.1, hx.2]
    have hw : |ℓ ^ 2 - (x - p) ^ 2| ≤ ℓ ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - p)]
    have hdist : dist x p < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
    have hM' : |H x - H p| ≤ c / 2 := by
      have := hδp hdist; rw [Real.dist_eq] at this; exact le_of_lt this
    exact mul_le_mul hw hM' (abs_nonneg _) (by positivity)
  -- Split the window integral: `∫ w·H = ∫ w·(H − H p) + H p · ∫ w`.
  have hint_split : (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2) * H x)
      = (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p))
        + H p * (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · congr 1; funext x; ring
    · exact ((by fun_prop :
        Continuous fun x : ℝ => (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p))).intervalIntegrable _ _
    · exact ((by fun_prop :
        Continuous fun x : ℝ => H p * (ℓ ^ 2 - (x - p) ^ 2))).intervalIntegrable _ _
  have hzero_ℓ := hzero ℓ hℓ
  have hwm : (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2)) = 4 * ℓ ^ 3 / 3 := by
    have := weight_mass p ℓ; unfold ballWeight at this; exact this
  rw [hint_split, hwm] at hzero_ℓ
  -- Therefore `∫ w·(H − H p) = −(H p · 4ℓ³/3)`.
  have heq : (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p))
      = -(H p * (4 * ℓ ^ 3 / 3)) := by linarith
  -- Bound the first term: `≤ (ℓ²·c/2)·(2ℓ)`.
  have hbnd : |∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p)|
      ≤ (ℓ ^ 2 * (c / 2)) * (2 * ℓ) := by
    have hbb := intervalIntegral.norm_integral_le_of_norm_le_const (a := p - ℓ) (b := p + ℓ)
      (C := ℓ ^ 2 * (c / 2)) (f := fun x => (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p)) ?_
    · simp only [Real.norm_eq_abs] at hbb
      have habs : |p + ℓ - (p - ℓ)| = 2 * ℓ := by rw [abs_of_nonneg (by linarith)]; ring
      rw [habs] at hbb; exact hbb
    · intro x hx
      simp only [Real.norm_eq_abs, abs_mul]
      exact hwbound x hx
  rw [heq] at hbnd
  -- `|−(H p · 4ℓ³/3)| = c · 4ℓ³/3`, contradicting the bound `c·ℓ³` since `4/3 > 1`.
  have hlhs : |(-(H p * (4 * ℓ ^ 3 / 3)))| = c * (4 * ℓ ^ 3 / 3) := by
    rw [abs_neg, abs_mul, ← hc]; congr 1; rw [abs_of_pos (by positivity)]
  rw [hlhs] at hbnd
  nlinarith [hbnd, hcpos, pow_pos hℓ 3]

/-- **The entanglement first law**, region by region: the RT area-variation (smeared
`δG`) equals `8πG` times the smeared boundary stress tensor (`δT`), for every interval. -/
def FirstLaw (δG δT : ℝ → ℝ) (G : ℝ) : Prop :=
  ∀ p ℓ, 0 < ℓ → modularIntegral δG p ℓ = einsteinConstant G * modularIntegral δT p ℓ

/-- **Main theorem — linearized Einstein equations from the entanglement first law**
(Faulkner–Guica–Hartman–Myers–Van Raamsdonk, toy AdS₃/CFT₂ form).

If the entanglement first law `δS = δ⟨H_mod⟩` — encoded as the smeared identity
`modularIntegral δG p ℓ = 8πG · modularIntegral δT p ℓ` — holds for **every** interval
(all centers `p`, all half-widths `ℓ > 0`), and the bulk densities `δG, δT` are
continuous, then the **pointwise linearized Einstein equation** `δG x = 8πG · δT x` holds
at every point `x`. The "for all regions ⟹ pointwise" step is discharged by
`fundamental_lemma_ball_weight`. -/
theorem linearized_einstein_of_first_law
    (δG δT : ℝ → ℝ) (G : ℝ) (hδG : Continuous δG) (hδT : Continuous δT)
    (hfl : FirstLaw δG δT G) :
    ∀ x, δG x = einsteinConstant G * δT x := by
  intro x
  -- Let `H = δG − 8πG · δT`; the first law says `modularIntegral H = 0` for every window.
  set H : ℝ → ℝ := fun y => δG y - einsteinConstant G * δT y with hHdef
  have hHcont : Continuous H := by fun_prop
  have hHzero : ∀ ℓ, 0 < ℓ → modularIntegral H x ℓ = 0 := by
    intro ℓ hℓ
    have := hfl x ℓ hℓ
    -- modularIntegral H = modularIntegral δG − 8πG · modularIntegral δT
    have hsplit : modularIntegral H x ℓ
        = modularIntegral δG x ℓ - einsteinConstant G * modularIntegral δT x ℓ := by
      unfold modularIntegral ballWeight
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
      · congr 1; funext y; simp only [hHdef]; ring
      · exact ((by fun_prop :
          Continuous fun y : ℝ => (ℓ ^ 2 - (y - x) ^ 2) * δG y)).intervalIntegrable _ _
      · exact ((by fun_prop :
          Continuous fun y : ℝ =>
            einsteinConstant G * ((ℓ ^ 2 - (y - x) ^ 2) * δT y))).intervalIntegrable _ _
    rw [hsplit, hfl x ℓ hℓ]; ring
  have := fundamental_lemma_ball_weight H hHcont x hHzero
  simp only [hHdef] at this
  linarith

/-! ### Non-vacuity witnesses -/

/-- **Closed-form witness.** The modular integral of the constant density `1` over the
unit interval `[−1, 1]` is `4/3 > 0`: the window has strictly positive mass, so the
`modularIntegral` machinery genuinely computes and the first law is a non-degenerate
constraint (not `∫ = ∫` collapsing to `0 = 0`). -/
theorem modularIntegral_one_zero_one : modularIntegral (fun _ => 1) 0 1 = 4 / 3 := by
  unfold modularIntegral ballWeight
  have : (fun x : ℝ => ((1 : ℝ) ^ 2 - (x - 0) ^ 2) * (1 : ℝ))
      = fun x : ℝ => ((1 : ℝ) ^ 2 - (x - 0) ^ 2) := by funext x; ring
  rw [this]
  have := weight_mass 0 1
  unfold ballWeight at this
  rw [this]; norm_num

/-- **Trivial satisfying instance** (hypotheses are consistent): with `δG = δT = 0` the
first law holds and the conclusion `δG x = 8πG · δT x` holds — the theorem is not proving
`False → anything`. -/
theorem witness_trivial (G : ℝ) :
    FirstLaw (fun _ => 0) (fun _ => 0) G
      ∧ (∀ x, (fun _ : ℝ => (0 : ℝ)) x = einsteinConstant G * (fun _ : ℝ => (0 : ℝ)) x) := by
  refine ⟨?_, ?_⟩
  · intro p ℓ _
    unfold modularIntegral ballWeight
    simp
  · intro x; simp

/-- **Nonzero satisfying instance** (non-vacuous content): take `G = 1`, `δT = 1`,
`δG = 8π`. The first law holds (both sides equal `8π · modularIntegral 1`, with
`modularIntegral 1 0 1 = 4/3 ≠ 0` by `modularIntegral_one_zero_one`, so the identity is a
genuine equality of nonzero smeared quantities), and the theorem's conclusion is the
honest nonzero relation `δG x = 8π · 1`. This certifies the main theorem is not vacuously
true. -/
theorem witness_nonzero :
    FirstLaw (fun _ => 8 * Real.pi) (fun _ => 1) 1
      ∧ modularIntegral (fun _ : ℝ => (1 : ℝ)) 0 1 = 4 / 3
      ∧ (∀ x, (fun _ : ℝ => 8 * Real.pi) x = einsteinConstant 1 * (fun _ : ℝ => (1 : ℝ)) x) := by
  refine ⟨?_, modularIntegral_one_zero_one, ?_⟩
  · intro p ℓ _
    unfold modularIntegral ballWeight einsteinConstant
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  · intro x; unfold einsteinConstant; ring

/-- **Non-vacuity certificate for the witness.** The nonzero witness carries a positive
smeared quantity: `modularIntegral 1 0 1 = 4/3 > 0`. -/
theorem witness_nonzero_positive :
    (0 : ℝ) < modularIntegral (fun _ : ℝ => (1 : ℝ)) 0 1 := by
  rw [modularIntegral_one_zero_one]; norm_num

/-! ### The multicomponent (tensor-shaped) localization

The linearized Einstein tensor `δG_μν` is not a single scalar: it has finitely many
independent components. Here we take the first faithful step toward the genuine tensor
identity by extending the scalar localization
(`linearized_einstein_of_first_law`) to a **finite family** of scalar components
`δG δT : Fin n → ℝ → ℝ`, each localized componentwise by the very same fundamental lemma.

**Honest scope (do NOT overclaim).** This is a *tensor-shaped* (componentwise-scalar)
localization: a finite family of scalar components, each localized by the fundamental
lemma. It is **NOT** the covariant Einstein tensor. The genuine covariant `δG_μν[h]` built
from Ricci/Riemann curvature and the metric perturbation `h` requires Mathlib's
covariant-derivative / curvature framework, which is **absent from Mathlib** (a separate,
much larger effort). Treating each abstract component as an independent scalar density is
a placeholder for that structure; the map from real tensor components to these scalar
fields — and the covariant `δG_μν[h]` from curvature — is future work. -/

/-- **The per-component entanglement first law** for a finite family of scalar densities.
For every component `i : Fin n` and every interval (center `p`, half-width `ℓ > 0`), the
smeared `δG i` equals `8πG` times the smeared `δT i` — the scalar `FirstLaw` holding
component by component. -/
def FirstLawMulti {n : ℕ} (δG δT : Fin n → ℝ → ℝ) (G : ℝ) : Prop :=
  ∀ (i : Fin n) p ℓ, 0 < ℓ →
    modularIntegral (δG i) p ℓ = einsteinConstant G * modularIntegral (δT i) p ℓ

/-- **Multicomponent (tensor-shaped) linearized Einstein equations.** If the per-component
first law `FirstLawMulti` holds for a finite family `δG δT : Fin n → ℝ → ℝ` of continuous
scalar densities, then the pointwise linearized Einstein equation `δG i x = 8πG · δT i x`
holds for **every component `i` and every point `x`**. The proof simply applies the
scalar theorem `linearized_einstein_of_first_law` at each component `i`, whose scalar
`FirstLaw` is exactly `hfl i`.

Honest scope: componentwise scalar localization, *not* the covariant `δG_μν[h]` from
curvature (Mathlib lacks Ricci/Riemann/Einstein — a separate effort). -/
theorem linearized_einstein_multicomponent {n : ℕ}
    (δG δT : Fin n → ℝ → ℝ) (G : ℝ)
    (hδG : ∀ i, Continuous (δG i)) (hδT : ∀ i, Continuous (δT i))
    (hfl : FirstLawMulti δG δT G) :
    ∀ (i : Fin n) x, δG i x = einsteinConstant G * δT i x := by
  intro i x
  exact linearized_einstein_of_first_law (δG i) (δT i) G (hδG i) (hδT i)
    (fun p ℓ hℓ => hfl i p ℓ hℓ) x

/-- **Nonzero multicomponent witness** (non-vacuous content). A concrete `n = 2` family
with `G = 1`: component `0` has `δT ≡ 1`, `δG ≡ 8π`; component `1` has `δT ≡ 2`,
`δG ≡ 16π`. The per-component first law `FirstLawMulti` holds — each component's `δG i`
smears to `einsteinConstant 1` times its `δT i` (both constant multiples of the *positive*
window mass `modularIntegral 1 0 1 = 4/3 ≠ 0`) — and the theorem's conclusion is the
*honest nonzero* relation `δG i x = 8π · δT i x` (`8π ≠ 0`, `16π ≠ 0`), NOT a vacuous
`0 = 0`. This certifies `linearized_einstein_multicomponent` is non-degenerate. -/
theorem witness_multicomponent_nonzero :
    FirstLawMulti
        (![fun _ => 8 * Real.pi, fun _ => 16 * Real.pi] : Fin 2 → ℝ → ℝ)
        (![fun _ => 1, fun _ => 2] : Fin 2 → ℝ → ℝ) 1
      ∧ modularIntegral (fun _ : ℝ => (1 : ℝ)) 0 1 = 4 / 3
      ∧ (∀ (i : Fin 2) x,
          (![fun _ => 8 * Real.pi, fun _ => 16 * Real.pi] : Fin 2 → ℝ → ℝ) i x
            = einsteinConstant 1
              * (![fun _ => 1, fun _ => 2] : Fin 2 → ℝ → ℝ) i x)
      ∧ (8 : ℝ) * Real.pi ≠ 0 ∧ (16 : ℝ) * Real.pi ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨?_, modularIntegral_one_zero_one, ?_, by positivity, by positivity⟩
  · intro i p ℓ _
    fin_cases i <;>
      (simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Fin.isValue, Fin.mk_zero, Fin.mk_one];
        unfold modularIntegral ballWeight einsteinConstant;
        rw [← intervalIntegral.integral_const_mul];
        congr 1; funext x; ring)
  · intro i x
    fin_cases i <;>
      (simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Fin.isValue, Fin.mk_zero, Fin.mk_one];
        unfold einsteinConstant; ring)

end Physlib.LinearizedEinstein
