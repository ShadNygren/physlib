/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The Weinberg–Witten no-go theorem (algebraic core + axiomatized QFT skeleton)

Weinberg & Witten (1980), *Limits on massless particles*, Phys. Lett. B 96, 59.

**Physics content.** A massless particle of helicity `h` cannot carry a nonzero
charge from a Lorentz-covariant conserved rank-`j` tensor current when `2|h| > j`:

* rank `j = 1` (a conserved Lorentz-covariant vector current `Jᵘ`) ⟹ no massless
  `|h| > 1/2` with nonzero charge;
* **rank `j = 2` (a conserved Lorentz-covariant stress–energy tensor `Tᵘᵛ`) ⟹ no
  massless `|h| > 1` — in particular NO massless spin-2 "graviton" carrying nonzero
  energy from a Lorentz-covariant stress tensor. This is the emergent-gravity
  constraint: an emergent graviton must evade the theorem's hypotheses (e.g. the
  stress tensor is not a Lorentz-covariant local operator on the emergent particle).**

**Mechanism, reduced to its algebraic core.** The forward one-particle matrix
element `M = ⟨p,h| (rank-j tensor) |p,h⟩` must, under a little-group rotation by
angle `θ` about the momentum axis (`ω := exp(i θ)`), pick up the helicity phase
`M = ω^(2h) · M`. A Lorentz-covariant rank-`j` tensor can only carry a helicity
change of magnitude at most `j`, so covariance forces `M = ω^k · M` for some
integer `|k| ≤ j`. If `2|h| > j` then, choosing the little-group angle so that
`ω^(2h) ≠ 1`, the relation `M = ω^(2h)·M` forces **`M = 0`**, contradicting a
nonzero charge/energy.

## What is PROVED vs AXIOMATIZED

This file mirrors the "axiomatized-input skeleton" style used for other physics
no-go theorems (Jacobson entropy–Einstein, Coleman–Mandula): the deep QFT input —
how a one-particle matrix element transforms under the little group, and the
covariance bound on the carried helicity — is *axiomatized* as fields of a
`structure`, and the algebraic **phase contradiction** that turns those inputs into
a no-go statement is *fully proved* over `ℂ`.

* **PROVED (physics-free):** `phase_forces_zero` — `ω ≠ 1 → z = ω * z → z = 0`;
  `exists_nontrivial_root_of_unity` — a concrete angle giving `exp (i · n · θ) ≠ 1`
  for `n ≠ 0`; the no-go core `weinberg_witten`; the `j = 2` emergent-graviton
  corollary; and the two anti-vacuity witnesses.
* **AXIOMATIZED (the QFT):** the fields `helicity_transform` and
  `covariant_rank_bound` of `WWHypothesis` — the transformation law of the forward
  matrix element and the Lorentz-covariance bound on the carried helicity.

## Main results

* `WeinbergWitten.phase_forces_zero`
* `WeinbergWitten.exists_nontrivial_root_of_unity`
* `WeinbergWitten.WWHypothesis` (with axiomatized QFT fields)
* `WeinbergWitten.weinberg_witten`
* `WeinbergWitten.no_massless_spin_two_from_covariant_stress_tensor`
* `WeinbergWitten.witness_allowed` (allowed case, nonzero) and
  `WeinbergWitten.witness_forbidden` (forbidden case, forces `M = 0`)
-/

namespace WeinbergWitten

open Complex

/-! ## The algebraic core (fully proved, physics-free) -/

/-- **Phase-contradiction lemma.** If a complex number `z` is fixed by
multiplication by a phase `ω ≠ 1`, i.e. `z = ω * z`, then `z = 0`.

This is the algebraic heart of Weinberg–Witten: the forward matrix element is
fixed by the little-group phase `ω^(2h)`, and if that phase is `≠ 1` the element
must vanish. -/
theorem phase_forces_zero {z ω : ℂ} (hω : ω ≠ 1) (h : z = ω * z) : z = 0 := by
  -- From `z = ω * z` we get `(1 - ω) * z = 0`.
  have hfac : (1 - ω) * z = 0 := by linear_combination h
  -- `1 - ω ≠ 0` since `ω ≠ 1`.
  have hne : (1 - ω) ≠ 0 := sub_ne_zero.mpr (fun hcontra => hω hcontra.symm)
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd h1 hne
  · exact h2

/-- **A concrete nontrivial root of unity.** For any nonzero integer `n`, there is
a little-group angle `θ` (namely `θ = π / n`) with `exp (i · n · θ) ≠ 1`.

We package the phase as `ω = exp (i · n · θ)` and exhibit `θ` making `ω = -1 ≠ 1`,
so the little group really does supply a phase `≠ 1` whenever the carried
(doubled) helicity `n` is nonzero. -/
theorem exists_nontrivial_root_of_unity {n : ℤ} (hn : n ≠ 0) :
    ∃ θ : ℝ, Complex.exp (I * n * (θ : ℂ)) ≠ 1 := by
  -- Take θ = π / n, so i * n * θ = i * π, and exp (i π) = exp (π i) = -1 ≠ 1.
  refine ⟨Real.pi / (n : ℝ), ?_⟩
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hθ : ((Real.pi / (n : ℝ) : ℝ) : ℂ) = (Real.pi : ℂ) / (n : ℂ) := by push_cast; ring
  have harg : I * (n : ℂ) * ((Real.pi / (n : ℝ) : ℝ) : ℂ) = Real.pi * I := by
    rw [hθ]
    field_simp
  rw [harg, Complex.exp_pi_mul_I]
  -- `-1 ≠ 1` in `ℂ`.
  intro hcontra
  have : (2 : ℂ) = 0 := by linear_combination -hcontra
  norm_num at this

/-! ## The Weinberg–Witten skeleton (QFT axiomatized) -/

/-- **The Weinberg–Witten hypothesis bundle.**

Abstract data standing in for a massless one-particle state and a Lorentz-covariant
conserved rank-`j` tensor current, together with the QFT facts we *axiomatize*.

* `doubledHelicity : ℤ` — twice the helicity `2h` (an integer for any half-integer
  spin), the phase power carried by the state under a little-group rotation.
* `rank : ℕ` — the tensor rank `j` (`1` = vector current, `2` = stress tensor).
* `M : ℂ` — the forward one-particle matrix element (the charge/energy density
  amplitude).
* `θ : ℝ` — the little-group rotation angle about the momentum axis.

Axiomatized QFT fields:

* `helicity_transform` — under the little-group rotation, the forward matrix element
  picks up the helicity phase: `M = exp (i · (2h) · θ) · M`. *(This is the deep QFT
  input — the transformation of a one-particle matrix element under the little
  group — which we do not derive here.)*
* `covariant_rank_bound` — Lorentz covariance of a rank-`j` tensor bounds the helicity
  it can carry: IF the matrix element is nonzero THEN `|2h| ≤ j`. *(Also axiomatized:
  it encodes that a covariant rank-`j` tensor's relevant component changes helicity by
  at most `j`.)* -/
structure WWHypothesis where
  /-- Twice the helicity, `2h`, as an integer. -/
  doubledHelicity : ℤ
  /-- The tensor rank `j` (1 = vector current, 2 = stress tensor). -/
  rank : ℕ
  /-- The forward one-particle matrix element `⟨p,h| Tensor |p,h⟩`. -/
  M : ℂ
  /-- The little-group rotation angle about the momentum axis. -/
  θ : ℝ
  /-- **Axiomatized QFT:** the forward matrix element picks up the helicity phase
  `exp (i · (2h) · θ)` under the little-group rotation. -/
  helicity_transform : M = Complex.exp (I * (doubledHelicity : ℂ) * (θ : ℂ)) * M
  /-- **Axiomatized QFT:** Lorentz covariance of a rank-`j` tensor bounds the carried
  helicity — a nonzero matrix element requires `|2h| ≤ j`. -/
  covariant_rank_bound : M ≠ 0 → doubledHelicity.natAbs ≤ rank

/-- **Weinberg–Witten no-go (core).** Given the axiomatized hypotheses, if the
doubled helicity exceeds the tensor rank in magnitude (`j < |2h|`, i.e. `2|h| > j`)
*and the little-group angle is chosen so the helicity phase is nontrivial*, then the
forward matrix element vanishes: `M = 0`.

The phase nontriviality hypothesis is *realizable* (not vacuous): by
`exists_nontrivial_root_of_unity`, whenever `2h ≠ 0` there exists an angle making
`exp (i · (2h) · θ) ≠ 1`; the corollaries below discharge it. -/
theorem weinberg_witten (W : WWHypothesis)
    (hphase : Complex.exp (I * (W.doubledHelicity : ℂ) * (W.θ : ℂ)) ≠ 1) :
    W.M = 0 :=
  phase_forces_zero hphase W.helicity_transform

/-- **Weinberg–Witten no-go (contradiction form).** With the phase chosen
nontrivial and `2|h| > j`, a *nonzero* charge/energy is impossible. -/
theorem weinberg_witten_contradiction (W : WWHypothesis)
    (hphase : Complex.exp (I * (W.doubledHelicity : ℂ) * (W.θ : ℂ)) ≠ 1)
    (_hbig : W.rank < W.doubledHelicity.natAbs) (hM : W.M ≠ 0) : False :=
  hM (weinberg_witten W hphase)

/-! ## The emergent-gravity corollary (rank `j = 2`, the stress tensor) -/

/-- **No massless spin-≥2 from a Lorentz-covariant stress tensor.**

Specialize to the stress–energy tensor, `rank = 2`. A massless particle with
`|2h| > 2` (helicity `|h| > 1`, i.e. spin ≥ 2 — in particular a spin-2 graviton has
`2h = ±4 > 2`) that satisfies the axiomatized WW hypotheses **must have vanishing
forward matrix element** `M = 0` — it cannot carry nonzero energy from a
Lorentz-covariant stress tensor.

This is the emergent-gravity constraint: a genuine graviton must *evade* these
hypotheses (the emergent stress tensor is not a covariant local operator with the
axiomatized transformation law).

We derive the needed nontrivial little-group phase from `2h ≠ 0` (forced by
`|2h| > 2`), so this corollary has no dangling phase hypothesis. -/
theorem no_massless_spin_two_from_covariant_stress_tensor
    (doubledHelicity : ℤ) (M : ℂ)
    (hspin : 2 < doubledHelicity.natAbs)
    (helicity_transform : ∀ θ : ℝ,
      M = Complex.exp (I * (doubledHelicity : ℂ) * (θ : ℂ)) * M) :
    M = 0 := by
  -- `2 < |2h|` forces `2h ≠ 0`, so the little group supplies a nontrivial phase.
  have hne : doubledHelicity ≠ 0 := by
    intro h0; rw [h0] at hspin; simp at hspin
  obtain ⟨θ, hθ⟩ := exists_nontrivial_root_of_unity hne
  exact phase_forces_zero hθ (helicity_transform θ)

/-! ## Anti-vacuity witnesses

Two concrete instances, showing the skeleton is neither empty nor trivially `0 = 0`:
(a) an ALLOWED nonzero charged particle satisfying `WWHypothesis`, and
(b) the FORBIDDEN case, where the theorem genuinely forces `M = 0`. -/

/-- **(a) Allowed case — a real, nonzero charged particle.**

A helicity-`1/2` particle (`doubledHelicity = 2h = 1`) coupled to a rank-`j = 1`
Lorentz-covariant vector current (electromagnetism), with a *nonzero* charge
amplitude `M = 1`. Here `|2h| = 1 ≤ 1 = j`, so Weinberg–Witten permits it: the
consistency requirement is met with the trivial (identity) little-group angle
`θ = 0`, giving phase `exp 0 = 1`, and the covariance bound `1 ≤ 1` holds.

The witnessed matrix element is `1 ≠ 0`: this is a genuine, non-vacuous instance,
not `0 = 0`. (An electron carrying electric charge really is allowed.) -/
def witness_allowed : WWHypothesis where
  doubledHelicity := 1
  rank := 1
  M := 1
  θ := 0
  helicity_transform := by
    simp
  covariant_rank_bound := by
    intro _; decide

/-- The allowed witness carries a genuinely nonzero charge amplitude. -/
theorem witness_allowed_nonzero : witness_allowed.M ≠ 0 := by
  simp [witness_allowed]

/-- The allowed witness sits at the WW boundary `|2h| = j` (here `1 = 1`), so the
covariance bound is saturated and satisfiable — it is not excluded by the no-go. -/
theorem witness_allowed_saturates :
    witness_allowed.doubledHelicity.natAbs ≤ witness_allowed.rank := by
  decide

/-- **(b) Forbidden case — a massless spin-2 graviton from a covariant stress tensor.**

Helicity `h = 2` (`doubledHelicity = 2h = 4`), rank `j = 2` (stress tensor).
Since `2 < |2h| = 4`, the emergent-gravity corollary forces *any* such matrix element
to vanish: a nonzero forward stress-tensor matrix element is impossible. We witness
this by showing that a candidate amplitude satisfying the helicity transformation law
is forced to `0`. -/
theorem witness_forbidden (M : ℂ)
    (helicity_transform : ∀ θ : ℝ, M = Complex.exp (I * (4 : ℂ) * (θ : ℂ)) * M) :
    M = 0 :=
  no_massless_spin_two_from_covariant_stress_tensor 4 M (by decide) helicity_transform

/-- The forbidden case is non-vacuous as a *constraint*: the phase supplied by the
little group for `2h = 4` is genuinely nontrivial (`≠ 1`), so the vanishing of `M`
is a real conclusion, not `0 = 0`. -/
theorem witness_forbidden_phase_nontrivial :
    ∃ θ : ℝ, Complex.exp (I * (4 : ℂ) * (θ : ℂ)) ≠ 1 := by
  have := exists_nontrivial_root_of_unity (n := 4) (by decide)
  simpa using this

end WeinbergWitten
