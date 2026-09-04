/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

/-!
# Classical Fisher information: data-processing / monotonicity

The classical Fisher information metric
`F(p, d) = ∑ᵢ dᵢ² / pᵢ`
is the diagonal (commuting) case of the Kubo–Mori metric. Physically it is the
holographic **canonical energy**: the quadratic response of relative entropy to a
perturbation `d` of the state `p`. The result here is its **data-processing
inequality** (monotonicity under coarse-graining):

> Applying a stochastic map (coarse-graining) `T` can only DECREASE the Fisher
> information: `F(Tp, Td) ≤ F(p, d)`.

You cannot gain distinguishing power by processing data. Holographically this is
the **RG / coarse-graining monotonicity of canonical energy**: the emergent
geometry's second-order response cannot increase under information loss (Petz;
Faulkner–Guica–Hartman–Myers–Van Raamsdonk).

## Proof strategy

The proof is a per-output Cauchy–Schwarz (conditional-Jensen) argument. Writing
`uᵢ = dᵢ / pᵢ` and per-output weights `wᵢ = T k i · pᵢ ≥ 0` with
`∑ᵢ wᵢ = (Tp)_k`, one has `(Td)_k = ∑ᵢ wᵢ uᵢ`, and
`(Td)_k² ≤ (∑ᵢ wᵢ)(∑ᵢ wᵢ uᵢ²) = (Tp)_k · ∑ᵢ T k i · dᵢ²/pᵢ`.
Dividing by `(Tp)_k` and summing over `k`, column-stochasticity `∑ₖ T k i = 1`
collapses the bound back to `F(p, d)`.

## Scope: classical vs quantum

This is the **classical / commuting** data-processing inequality — the honest,
fully self-contained core, provable from Mathlib's finite-sum Cauchy–Schwarz. It
is the diagonal case of the full quantum Kubo–Mori CPTP-monotonicity exactly as
the classical Fisher positivity is the diagonal case of the quantum
Kubo–Mori positivity.

The **full quantum** statement (CPTP-monotonicity of the Kubo–Mori metric)
requires operator-convexity machinery (Lieb concavity / Petz recovery) not yet
available in Mathlib; it is deferred as future work (a later branch), mirroring
the positivity progression.

## Main results

* `sq_weighted_sum_le` — per-output Cauchy–Schwarz: `(∑ wᵢuᵢ)² ≤ (∑ wᵢ)(∑ wᵢuᵢ²)`.
* `fisher_data_processing` — `F(Tp, Td) ≤ F(p, d)` for stochastic `T`, positive `p`,
  positive push-forward.
* `canonicalEnergyMonotone` — the same statement stated as RG-monotonicity of
  canonical energy.
* `mergeMap_strict_contraction` — anti-vacuity witness: the total-merge map
  `T = !![1, 1]` strictly destroys Fisher information (`0 < 4`).
-/

@[expose] public section

namespace Physlib.FisherMonotone

open Finset

variable {n m : ℕ}

/-- Classical Fisher information of a perturbation `d` at a probability vector `p`:
`F(p, d) = ∑ᵢ dᵢ² / pᵢ`. This is the classical `fisherInfo`, the diagonal case of the
Kubo–Mori metric. -/
noncomputable def fisherInfo (p d : Fin n → ℝ) : ℝ := ∑ i, d i ^ 2 / p i

/-- A **column-stochastic** matrix (a classical coarse-graining / stochastic map):
nonnegative entries with each column summing to one, so it maps probability
vectors to probability vectors. -/
def IsStochastic (T : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ k i, 0 ≤ T k i) ∧ (∀ i, ∑ k, T k i = 1)

/-- Push-forward of a vector `p` on `n` outcomes to a vector on `m` outcomes by a
stochastic map `T`: `(T p)_k = ∑ᵢ T k i · pᵢ`. (Definitionally `T *ᵥ p`.) -/
def pushforward (T : Matrix (Fin m) (Fin n) ℝ) (p : Fin n → ℝ) : Fin m → ℝ :=
  fun k => ∑ i, T k i * p i

/-- The **per-output Cauchy–Schwarz** step: for nonnegative weights `wᵢ`,
`(∑ᵢ wᵢ uᵢ)² ≤ (∑ᵢ wᵢ)(∑ᵢ wᵢ uᵢ²)`.

Proof: apply `Finset.sum_mul_sq_le_sq_mul_sq` with `fᵢ = √wᵢ`, `gᵢ = √wᵢ uᵢ`,
using `√wᵢ · √wᵢ = wᵢ` for `wᵢ ≥ 0`. -/
theorem sq_weighted_sum_le (w u : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * u i) ^ 2 ≤ (∑ i, w i) * (∑ i, w i * u i ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * u i)
  -- Rewrite the three sums appearing in `hcs` into the desired form.
  have e1 : ∀ i, Real.sqrt (w i) * (Real.sqrt (w i) * u i) = w i * u i := by
    intro i
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have e2 : ∀ i, (Real.sqrt (w i)) ^ 2 = w i := by
    intro i; rw [Real.sq_sqrt (hw i)]
  have e3 : ∀ i, (Real.sqrt (w i) * u i) ^ 2 = w i * u i ^ 2 := by
    intro i; rw [mul_pow, Real.sq_sqrt (hw i)]
  simp only [e1, e2, e3] at hcs
  exact hcs

/-- **Classical Fisher data-processing inequality.**

For a stochastic (coarse-graining) map `T`, a strictly positive probability vector
`p`, and a perturbation `d`, if the push-forward `T p` is strictly positive on
every output then
`F(T p, T d) ≤ F(p, d)`.

Coarse-graining cannot increase Fisher information. Note: the trace-preserving
hypothesis `∑ᵢ dᵢ = 0` is **not** needed — the inequality is purely the quadratic
Cauchy–Schwarz bound — so it is omitted. -/
theorem fisher_data_processing (T : Matrix (Fin m) (Fin n) ℝ) (p d : Fin n → ℝ)
    (hT : IsStochastic T) (hp : ∀ i, 0 < p i)
    (hTp : ∀ k, 0 < pushforward T p k) :
    fisherInfo (pushforward T p) (pushforward T d) ≤ fisherInfo p d := by
  obtain ⟨hTnn, hTcol⟩ := hT
  -- Per-output bound: `(Td)_k² / (Tp)_k ≤ ∑ᵢ T k i · dᵢ²/pᵢ`.
  have per_output : ∀ k,
      (pushforward T d k) ^ 2 / (pushforward T p k)
        ≤ ∑ i, T k i * (d i ^ 2 / p i) := by
    intro k
    -- weights wᵢ = T k i · pᵢ ≥ 0 ; uᵢ = dᵢ / pᵢ.
    set w : Fin n → ℝ := fun i => T k i * p i with hw_def
    set u : Fin n → ℝ := fun i => d i / p i with hu_def
    have hw : ∀ i, 0 ≤ w i := fun i =>
      mul_nonneg (hTnn k i) (le_of_lt (hp i))
    -- (Td)_k = ∑ wᵢ uᵢ
    have hTd : pushforward T d k = ∑ i, w i * u i := by
      simp only [pushforward, hw_def, hu_def]
      apply Finset.sum_congr rfl
      intro i _
      have hpi : p i ≠ 0 := ne_of_gt (hp i)
      field_simp
    -- (Tp)_k = ∑ wᵢ
    have hTp' : pushforward T p k = ∑ i, w i := by
      simp only [pushforward, hw_def]
    -- ∑ wᵢ uᵢ² = ∑ᵢ T k i · dᵢ²/pᵢ
    have hsum2 : (∑ i, w i * u i ^ 2) = ∑ i, T k i * (d i ^ 2 / p i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [hw_def, hu_def]
      have hpi : p i ≠ 0 := ne_of_gt (hp i)
      rw [div_pow]
      field_simp
    have hcs := sq_weighted_sum_le w u hw
    rw [← hTd, ← hTp', hsum2] at hcs
    -- from  (Td)² ≤ (Tp) * S  and  Tp > 0  conclude  (Td)²/(Tp) ≤ S
    rw [div_le_iff₀ (hTp k)]
    calc (pushforward T d k) ^ 2
        ≤ (pushforward T p k) * (∑ i, T k i * (d i ^ 2 / p i)) := hcs
      _ = (∑ i, T k i * (d i ^ 2 / p i)) * (pushforward T p k) := by ring
  -- Sum the per-output bound over k, then swap sums and use column-stochasticity.
  calc fisherInfo (pushforward T p) (pushforward T d)
      = ∑ k, (pushforward T d k) ^ 2 / (pushforward T p k) := rfl
    _ ≤ ∑ k, ∑ i, T k i * (d i ^ 2 / p i) :=
        Finset.sum_le_sum (fun k _ => per_output k)
    _ = ∑ i, ∑ k, T k i * (d i ^ 2 / p i) := Finset.sum_comm
    _ = ∑ i, (∑ k, T k i) * (d i ^ 2 / p i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
    _ = ∑ i, (d i ^ 2 / p i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hTcol i, one_mul]
    _ = fisherInfo p d := rfl

/-- **RG-monotonicity of canonical energy.** Holographically, `fisherInfo` is the
canonical energy — the second-order response of relative entropy. This is the same
data-processing inequality: coarse-graining (an RG / stochastic map) cannot
increase the emergent geometry's second-order response. -/
theorem canonicalEnergyMonotone (T : Matrix (Fin m) (Fin n) ℝ) (p d : Fin n → ℝ)
    (hT : IsStochastic T) (hp : ∀ i, 0 < p i)
    (hTp : ∀ k, 0 < pushforward T p k) :
    fisherInfo (pushforward T p) (pushforward T d) ≤ fisherInfo p d :=
  fisher_data_processing T p d hT hp hTp

/-! ## Anti-vacuity: a strictly contracting coarse-graining

The **total-merge** map on `n = 2` outcomes to `m = 1` output,
`T = !![1, 1]`, collapses both outcomes into one. It is stochastic, and it
DESTROYS all Fisher information of the traceless perturbation `d = ![1, -1]` at
the uniform distribution `p = ![1/2, 1/2]`: `F(Tp, Td) = 0 < 4 = F(p, d)`. This
witnesses genuine strict contraction (a real information loss, not the trivial
identity map). -/

/-- The total-merge coarse-graining `Fin 2 → Fin 1`, sending every outcome to the
single output. -/
def mergeMap : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]

/-- The uniform distribution on two outcomes. -/
noncomputable def unifP : Fin 2 → ℝ := ![1/2, 1/2]

/-- A traceless perturbation on two outcomes. -/
def antiD : Fin 2 → ℝ := ![1, -1]

theorem mergeMap_isStochastic : IsStochastic mergeMap := by
  constructor
  · intro k i
    fin_cases k
    fin_cases i <;> simp [mergeMap]
  · intro i
    fin_cases i <;> simp [mergeMap]

theorem mergeMap_pushforward_pos : ∀ k, 0 < pushforward mergeMap unifP k := by
  intro k
  fin_cases k
  simp only [pushforward, mergeMap, unifP, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem fisher_before : fisherInfo unifP antiD = 4 := by
  simp only [fisherInfo, unifP, antiD, Fin.sum_univ_two]
  norm_num

theorem fisher_after :
    fisherInfo (pushforward mergeMap unifP) (pushforward mergeMap antiD) = 0 := by
  simp [fisherInfo, pushforward, mergeMap, unifP, antiD, Fin.sum_univ_two]

/-- **Strict-contraction witness (anti-vacuity).** The total-merge map
strictly decreases Fisher information: `F(Tp, Td) = 0 < 4 = F(p, d)`. The
hypotheses of `fisher_data_processing` are all satisfied (`mergeMap` is
stochastic, `unifP` is strictly positive, the push-forward is strictly positive),
so the inequality is genuine and non-vacuous. -/
theorem mergeMap_strict_contraction :
    fisherInfo (pushforward mergeMap unifP) (pushforward mergeMap antiD)
      < fisherInfo unifP antiD := by
  rw [fisher_after, fisher_before]
  norm_num

end Physlib.FisherMonotone
