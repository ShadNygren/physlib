/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib

/-!

# The resolvent-integral representation of the Kubo–Mori weight

The **Kubo–Mori (KM) Fisher metric** is the quantum information metric associated with the
Kubo–Mori–Bogoliubov inner product; it is the metric that governs the second-order (non-linear)
content of the quantum first law. For a full-rank density matrix `ρ` with spectral decomposition
`ρ = Σ pᵢ |i⟩⟨i|`, the KM metric of a self-adjoint direction `A` admits the **operator-integral
representation**
```
K_ρ(A) = ∫₀^∞ Tr[ A (ρ+s)⁻¹ A (ρ+s)⁻¹ ] ds
```
and the **closed form**
```
K_ρ(A) = Σᵢⱼ |A_ij|² · L(pᵢ, pⱼ),   L(a,b) = (log a − log b)/(a − b),  L(a,a) = 1/a.
```

The bridge between these two — the reason the operator integral EQUALS the closed form — is a
purely *scalar*, eigenvalue-level real-analysis fact: in `ρ`'s eigenbasis the `(i,j)` matrix element
of `∫₀^∞ (ρ+s)⁻¹ A (ρ+s)⁻¹ ds` is `A_ij · ∫₀^∞ 1/((pᵢ+s)(pⱼ+s)) ds`, and this scalar integral is
exactly the KM weight `L(pᵢ, pⱼ)`. This file formalizes that scalar identity — the real content:

* `integral_resolvent_product` : for `a ≠ b`,
  `∫₀^∞ 1/((a+s)(b+s)) ds = (log a − log b)/(a − b)`.
* `integral_resolvent_sq` : the degenerate case `∫₀^∞ 1/(a+s)² ds = 1/a`.
* `integral_resolvent_eq_kmWeight` : both branches unified through `kmWeight`.

## Why this is foundational

1. It **rigorously grounds the closed form** `K_ρ(A) = Σ |A_ij|² L(pᵢ,pⱼ)` from its defining
   resolvent integral — the closed form is no longer asserted, it is derived (eigenvalue-wise).
2. It **builds the resolvent-integral machinery** needed for the next result — the quantum
   operator-convex CPTP-monotonicity of the KM metric — whose proof runs through exactly this
   `∫₀^∞ (ρ+s)⁻¹ · (ρ+s)⁻¹ ds` integral representation.

The whole result is self-contained real analysis over `ℝ`: no operator theory is required. The proof
is the antiderivative route — an explicit antiderivative `G`, the fundamental theorem of calculus on
each `[0,t]`, and the improper limit `t → ∞` — packaged by
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`.

## Key results

- `kmWeight` : the Kubo–Mori weight `L(a,b)`, restated locally.
- `integral_resolvent_product`, `integral_resolvent_sq`, `integral_resolvent_eq_kmWeight`.
- `integral_witness_log2`, `integral_witness_one` : concrete non-vacuous witnesses
  (`∫₀^∞ ds/((s+2)(s+1)) = log 2` and `∫₀^∞ ds/(s+1)² = 1`), with `log 2 ≠ 0`.

-/

@[expose] public section

open MeasureTheory intervalIntegral Filter Topology Set

namespace Physlib.KuboMoriIntegral

/-- The **Kubo–Mori weight** `L(a,b)`: the divided difference of `Real.log`, with the degenerate
value `L(a,a) = 1/a` filling the removable singularity. This is the scalar (eigenvalue-level) weight
appearing in the closed form `K_ρ(A) = Σᵢⱼ |A_ij|² · L(pᵢ,pⱼ)`. Restated locally so this file has
no cross-branch dependency. -/
noncomputable def kmWeight (a b : ℝ) : ℝ :=
  if a = b then 1 / a else (Real.log a - Real.log b) / (a - b)

@[simp] theorem kmWeight_self (a : ℝ) : kmWeight a a = 1 / a := by
  simp [kmWeight]

theorem kmWeight_of_ne {a b : ℝ} (hab : a ≠ b) :
    kmWeight a b = (Real.log a - Real.log b) / (a - b) := by
  simp [kmWeight, hab]

/-!
### The scalar resolvent integrals

The core deliverable. Both are proved in the FULL improper-integral form
`∫ s in Set.Ioi 0, … = …` (not a finite-interval fallback), via the antiderivative route.
-/

/-- **Non-degenerate resolvent integral.** For `a, b > 0` with `a ≠ b`,
`∫₀^∞ 1/((a+s)(b+s)) ds = (log a − log b)/(a − b) = kmWeight a b`.

This is the scalar form of the `(i,j ; i≠j)` matrix element of the operator integral
`∫₀^∞ (ρ+s)⁻¹ A (ρ+s)⁻¹ ds` in `ρ`'s eigenbasis, and it is exactly the KM weight `L(pᵢ,pⱼ)`.

Proof: the explicit antiderivative `G(s) = (log(a+s) − log(b+s))/(b−a)` has derivative
`1/((a+s)(b+s))` on `(0,∞)`, tends to `0` as `s → ∞` (because `(a+s)/(b+s) → 1`), and is continuous
at `0`; the fundamental theorem of calculus for improper integrals gives the value `0 − G(0)`. -/
theorem integral_resolvent_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ∫ s in Set.Ioi (0 : ℝ), 1 / ((a + s) * (b + s)) = (Real.log a - Real.log b) / (a - b) := by
  set G : ℝ → ℝ := fun s => (Real.log (a + s) - Real.log (b + s)) / (b - a) with hG
  have hdba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- Derivative of the antiderivative `G` on `(0,∞)`.
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt G (1 / ((a + s) * (b + s))) s := by
    intro s hs
    have hs' : 0 < s := hs
    have has : a + s ≠ 0 := by positivity
    have hbs : b + s ≠ 0 := by positivity
    have hd1 : HasDerivAt (fun s => Real.log (a + s)) (a + s)⁻¹ s := by
      have h := ((hasDerivAt_id s).const_add a).log has; simpa using h
    have hd2 : HasDerivAt (fun s => Real.log (b + s)) (b + s)⁻¹ s := by
      have h := ((hasDerivAt_id s).const_add b).log hbs; simpa using h
    have hsub := (hd1.sub hd2).div_const (b - a)
    have hval : ((a + s)⁻¹ - (b + s)⁻¹) / (b - a) = 1 / ((a + s) * (b + s)) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; field_simp; ring
    rw [hval] at hsub; exact hsub
  -- `G(s) → 0` as `s → ∞`.
  have hlim : Tendsto G atTop (𝓝 0) := by
    have hbase : Tendsto (fun t : ℝ => Real.log (a + t) - Real.log (b + t)) atTop (𝓝 0) := by
      have hev : (fun t : ℝ => Real.log (a + t) - Real.log (b + t))
          =ᶠ[atTop] (fun t : ℝ => Real.log ((a + t) / (b + t))) := by
        filter_upwards [eventually_gt_atTop 0] with t ht
        rw [Real.log_div (by positivity) (by positivity)]
      rw [tendsto_congr' hev]
      have hratio : Tendsto (fun t : ℝ => (a + t) / (b + t)) atTop (𝓝 1) := by
        have h0 : Tendsto (fun t : ℝ => (a - b) / (b + t)) atTop (𝓝 0) := by
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_left atTop b tendsto_id
        have heq : (fun t : ℝ => (a + t) / (b + t))
            =ᶠ[atTop] (fun t : ℝ => 1 + (a - b) / (b + t)) := by
          filter_upwards [eventually_gt_atTop 0] with t ht
          have hbs : b + t ≠ 0 := by positivity
          field_simp; ring
        rw [tendsto_congr' heq]; simpa using h0.const_add 1
      have hcomp := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
      simp only [Real.log_one] at hcomp; exact hcomp
    simpa [hG] using hbase.div_const (b - a)
  -- `G` continuous at `0` within `[0,∞)`.
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div_const
    apply ContinuousAt.sub
    · exact (Real.continuousAt_log (by positivity)).comp (by fun_prop)
    · exact (Real.continuousAt_log (by positivity)).comp (by fun_prop)
  -- The integrand is nonnegative, hence integrable on `(0,∞)`.
  have hnonneg : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ 1 / ((a + s) * (b + s)) := by
    intro s hs; have : 0 < s := hs; positivity
  have hint : IntegrableOn (fun s => 1 / ((a + s) * (b + s))) (Ioi 0) volume :=
    integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg hlim
  -- Fundamental theorem of calculus for improper integrals: value is `0 − G 0`.
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [hmain]
  simp only [hG, add_zero]
  rw [zero_sub, ← neg_div, div_eq_div_iff hdba (sub_ne_zero.mpr hab)]
  ring

/-- **Degenerate resolvent integral.** For `a > 0`,
`∫₀^∞ 1/(a+s)² ds = 1/a = kmWeight a a`.

This is the diagonal (`i = j`) matrix element of the operator integral; the antiderivative is
`G(s) = −(a+s)⁻¹`. -/
theorem integral_resolvent_sq {a : ℝ} (ha : 0 < a) :
    ∫ s in Set.Ioi (0 : ℝ), 1 / (a + s) ^ 2 = 1 / a := by
  set G : ℝ → ℝ := fun s => -(a + s)⁻¹ with hG
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt G (1 / (a + s) ^ 2) s := by
    intro s hs
    have hs' : 0 < s := hs
    have has : a + s ≠ 0 := by positivity
    have h1 : HasDerivAt (fun s : ℝ => a + s) 1 s := (hasDerivAt_id s).const_add a
    have hinv : HasDerivAt (fun s : ℝ => (a + s)⁻¹) (-1 / (a + s) ^ 2) s := h1.inv has
    have hneg : HasDerivAt (fun s : ℝ => -(a + s)⁻¹) (-(-1 / (a + s) ^ 2)) s := hinv.neg
    have hval : -(-1 / (a + s) ^ 2) = 1 / (a + s) ^ 2 := by ring
    rwa [hval] at hneg
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => (a + s)⁻¹) atTop (𝓝 0) := by
      apply Tendsto.inv_tendsto_atTop
      exact tendsto_atTop_add_const_left atTop a tendsto_id
    simpa [hG] using h.neg
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.neg
    apply ContinuousAt.inv₀ _ (by positivity)
    fun_prop
  have hnonneg : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ 1 / (a + s) ^ 2 := by
    intro s hs; have : 0 < s := hs; positivity
  have hint : IntegrableOn (fun s => 1 / (a + s) ^ 2) (Ioi 0) volume :=
    integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg hlim
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [hmain]
  simp only [hG, add_zero, zero_sub, neg_neg, one_div]

/-- **Unified statement via `kmWeight`.** For `a, b > 0`, the resolvent-product integral equals the
Kubo–Mori weight `kmWeight a b` — its `a ≠ b` and `a = b` branches are `integral_resolvent_product`
and `integral_resolvent_sq` respectively. In the degenerate branch the integrand `1/((a+s)(b+s))`
is `1/(a+s)²`.

This is the exact statement of the operator-integral → closed-form bridge: the eigenbasis
matrix element `A_ij · ∫₀^∞ 1/((pᵢ+s)(pⱼ+s)) ds` equals `A_ij · kmWeight pᵢ pⱼ = A_ij · L(pᵢ,pⱼ)`. -/
theorem integral_resolvent_eq_kmWeight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ s in Set.Ioi (0 : ℝ), 1 / ((a + s) * (b + s)) = kmWeight a b := by
  by_cases hab : a = b
  · subst hab
    rw [kmWeight_self]
    have : (fun s : ℝ => 1 / ((a + s) * (a + s))) = fun s : ℝ => 1 / (a + s) ^ 2 := by
      funext s; rw [sq]
    rw [this, integral_resolvent_sq ha]
  · rw [kmWeight_of_ne hab, integral_resolvent_product ha hb hab]

/-!
### Anti-vacuity witnesses

Concrete evaluations proving the identity yields specific nonzero values, and that hypotheses are
satisfiable.
-/

/-- Concrete witness at `a = 2, b = 1`: `∫₀^∞ ds/((s+2)(s+1)) = log 2`, a specific nonzero value
(`Real.log 2 ≠ 0`, established below). -/
theorem integral_witness_log2 :
    ∫ s in Set.Ioi (0 : ℝ), 1 / ((s + 2) * (s + 1)) = Real.log 2 := by
  have hcongr : ∫ s in Set.Ioi (0 : ℝ), 1 / ((s + 2) * (s + 1))
      = ∫ s in Set.Ioi (0 : ℝ), 1 / (((2 : ℝ) + s) * ((1 : ℝ) + s)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    show 1 / ((s + 2) * (s + 1)) = 1 / ((2 + s) * (1 + s))
    rw [add_comm s 2, add_comm s 1]
  rw [hcongr, integral_resolvent_product (a := 2) (b := 1)
      (by norm_num) (by norm_num) (by norm_num)]
  simp only [Real.log_one, sub_zero]
  norm_num

/-- The witness value is genuinely nonzero: `Real.log 2 ≠ 0`. Combined with
`integral_witness_log2`, this proves the resolvent integral is not vacuously zero. -/
theorem log_two_ne_zero : Real.log 2 ≠ 0 :=
  ne_of_gt (Real.log_pos one_lt_two)

/-- Concrete witness at the degenerate `a = 1`: `∫₀^∞ ds/(s+1)² = 1`, a specific nonzero value. -/
theorem integral_witness_one :
    ∫ s in Set.Ioi (0 : ℝ), 1 / (s + 1) ^ 2 = 1 := by
  have hcongr : ∫ s in Set.Ioi (0 : ℝ), 1 / (s + 1) ^ 2
      = ∫ s in Set.Ioi (0 : ℝ), 1 / ((1 : ℝ) + s) ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simp only [add_comm]
  rw [hcongr, integral_resolvent_sq (a := 1) (by norm_num), div_one]

/-!
### The operator-integral connection (documentation)

For a full-rank `ρ = Σᵢ pᵢ |i⟩⟨i|` and self-adjoint `A` with eigenbasis matrix elements
`A_ij = ⟨i| A |j⟩`, the resolvent `(ρ+s)⁻¹` is diagonal with entries `(pᵢ+s)⁻¹`, so the `(i,j)`
matrix element of the operator integrand `(ρ+s)⁻¹ A (ρ+s)⁻¹` is `(pᵢ+s)⁻¹ A_ij (pⱼ+s)⁻¹`.
Integrating over `s ∈ (0,∞)` and using `integral_resolvent_eq_kmWeight` on each entry gives, for the
KM metric,
```
K_ρ(A) = ∫₀^∞ Tr[A (ρ+s)⁻¹ A (ρ+s)⁻¹] ds
       = Σᵢⱼ A_ij conj(A_ij) · ∫₀^∞ 1/((pᵢ+s)(pⱼ+s)) ds
       = Σᵢⱼ |A_ij|² · kmWeight pᵢ pⱼ
       = Σᵢⱼ |A_ij|² · L(pᵢ, pⱼ),
```
which is exactly the closed form. The finite-dimensional operator statement (Tr of the operator
integral = the closed-form sum) lives on the QuantumKuboMori branch, which imports this file for the
scalar identity above; here we record the bridge as documentation to avoid a cross-branch dependency.
-/

end Physlib.KuboMoriIntegral
