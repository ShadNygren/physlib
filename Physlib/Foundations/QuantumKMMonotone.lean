/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Mathlib
/-!

# Quantum monotonicity of the Kubo–Mori Fisher metric

This file formalizes the *quantum data-processing* content of the Kubo–Mori (KM) Fisher
information metric for the canonical-energy program. The KM metric is the second-order
term of the quantum relative entropy and equals the holographic canonical energy; its
**monotonicity under quantum channels** is exactly the statement that canonical energy cannot
increase under quantum coarse-graining.

For a state `ρ` diagonal in an eigenbasis with eigenvalues `p_i > 0`, and an observable `A`
written in that eigenbasis (entries `A_ij`), the Kubo–Mori metric has the closed form

  `K_ρ(A) = ∑_{i,j} |A_ij|² · L(p_i, p_j)`,     where   `L(a,b) = (log a - log b)/(a - b)`,
                                                        `L(a,a) = 1/a`  (the diagonal / classical weight).

`L` is the *logarithmic mean reciprocal* (the resolvent-integral weight); `L(a,a)=1/a`
recovers the classical Fisher weight, so the diagonal entries reproduce the classical Fisher
information `∑_i |A_ii|²/p_i`.

## What is proved here (SCOPE)

The full CPTP monotonicity theorem — `K` nonincreasing under *every* completely-positive
trace-preserving map — requires operator convexity / Lieb concavity of `x ↦ x log x`
(Petz's theorem) and is the remaining frontier (documented below, NOT built here).
This file delivers the tractable **quantum data-processing core**, provable directly from the
closed form:

* **Reversible (relabeling / unitary-in-eigenbasis) invariance.**
  `kuboMori_perm_invariant`: permuting the eigen-indices by any `σ : Equiv.Perm` while
  correspondingly relabeling `A` leaves `K` invariant. This is the discrete/eigenbasis image
  of unitary invariance `K_{UρU†}(UAU†) = K_ρ(A)`: reversible evolution does not change the
  metric.

* **Pinching (completely-dephasing) monotonicity — THE HEADLINE.**
  `pinching_monotone`: the completely-dephasing CPTP channel, which zeroes the off-diagonal
  entries of `A` (projecting onto ρ's eigenbasis), does **not increase** `K`:

    `K_ρ(diagPart A) ≤ K_ρ(A)`.

  This is immediate from the closed form — dropping the nonnegative off-diagonal sum
  `∑_{i≠j} |A_ij|² L(p_i,p_j) ≥ 0` can only decrease `K`. Pinching is a genuine CPTP channel,
  so this is a true *quantum* data-processing inequality. Moreover `kuboMori_diagPart_eq`
  shows pinching recovers the **classical Fisher information** `∑_i |A_ii|²/p_i`, i.e. the
  quantum → classical data-processing bridge:

    `classicalFisher (|A_ii|²) ≤ K_ρ(A)`.

  The anti-vacuity witness `pinching_witness_strict` exhibits *strict* decrease on a genuinely
  non-commuting observable (`ρ = diag(2/3,1/3)`, `A = Pauli-X`): `0 = K_ρ(diagPart A) < K_ρ(A)`.

## Remaining frontier (NOT built here, documented only)

Full monotonicity `K_{Φ(ρ)}(Φ(A)) ≤ K_ρ(A)` under an arbitrary CPTP map `Φ` follows from the
**joint convexity of the KM metric in `(ρ,A)`**, which is equivalent to the Lieb concavity of
`(X,Y) ↦ Tr X^s K Y^{1-s} K†` / operator convexity of `x ↦ x log x` (Petz, *Quasi-entropies for
finite quantum systems*; Lieb, *Convex trace functions and the Wigner–Yanase–Dyson conjecture*;
Faulkner–Guica–Hartman–Myers–Van Raamsdonk canonical-energy program). Mathlib currently lacks
operator convexity of the matrix logarithm, so this is deferred. The pinching channel above
is the canonical quantum → classical *data-processing instance* of that general theorem, and
the relabeling invariance its reversible (equality) instance; together they are the tractable core.

## Building blocks

* Classical Fisher information (the diagonal case).
* The closed form `K_ρ(A) = ∑ |A_ij|² L(p_i,p_j)` — re-stated locally here as `kuboMori`.
* Classical data-processing monotonicity — completed into the quantum regime here.
* The resolvent-integral representation of the weight `L` — used conceptually; only `L`'s
  positivity is needed here and is proved directly.
-/

@[expose] public section

namespace Physlib.QuantumKMMonotone

open scoped BigOperators
open Finset

/-! ### Definitions (the closed form, re-stated locally) -/

/-- The Kubo–Mori weight `L(a,b)`: the logarithmic-mean reciprocal.
For `a ≠ b` it is `(log a - log b)/(a - b)`; on the diagonal `L(a,a) = 1/a`, the classical
Fisher weight. This is the resolvent-integral weight. -/
noncomputable def kmWeight (a b : ℝ) : ℝ :=
  if a = b then 1 / a else (Real.log a - Real.log b) / (a - b)

/-- The Kubo–Mori Fisher metric in the eigenbasis (the closed form):
`K_ρ(A) = ∑_{i,j} |A_ij|² · L(p_i, p_j)`, with `p` the eigenvalues of `ρ` and `A` the
observable in ρ's eigenbasis. Here `‖·‖²` is the squared complex modulus. -/
noncomputable def kuboMori {n : ℕ} (p : Fin n → ℝ) (A : Fin n → Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j) * kmWeight (p i) (p j)

/-- The classical Fisher information `∑_i a_i / p_i` (the diagonal / pinched contribution).
Here `a_i` plays the role of `|A_ii|²`. -/
noncomputable def classicalFisher {n : ℕ} (p : Fin n → ℝ) (a : Fin n → ℝ) : ℝ :=
  ∑ i, a i / p i

/-- The pinching / completely-dephasing channel output: zero out the off-diagonal entries of
`A` (project onto ρ's eigenbasis). This is a CPTP map. -/
def diagPart {n : ℕ} (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun i j => if i = j then A i j else 0

/-! ### Positivity of the weight -/

/-- The Kubo–Mori weight is nonnegative for positive eigenvalues. On the diagonal it is `1/a > 0`;
off the diagonal `(log a - log b)/(a - b) > 0` because `log` is strictly monotone (the numerator
and denominator have the same sign). This is what allows dropping the off-diagonal terms in the
pinching argument. -/
theorem kmWeight_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ kmWeight a b := by
  unfold kmWeight
  split_ifs with h
  · positivity
  · -- a ≠ b: numerator and denominator have matching signs, so the quotient is nonneg.
    rcases lt_or_gt_of_ne h with hlt | hgt
    · -- a < b : log a < log b (num < 0), a - b < 0 (den < 0)
      have hnum : Real.log a - Real.log b < 0 := by
        have := Real.log_lt_log ha hlt
        linarith
      have hden : a - b < 0 := by linarith
      exact le_of_lt (div_pos_of_neg_of_neg hnum hden)
    · -- a > b : log a > log b (num > 0), a - b > 0 (den > 0)
      have hnum : 0 < Real.log a - Real.log b := by
        have := Real.log_lt_log hb hgt
        linarith
      have hden : 0 < a - b := by linarith
      exact le_of_lt (div_pos hnum hden)

/-- The Kubo–Mori weight is symmetric: `L(a,b) = L(b,a)`. -/
theorem kmWeight_symm (a b : ℝ) : kmWeight a b = kmWeight b a := by
  unfold kmWeight
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    rw [← neg_sub (Real.log a), ← neg_sub a b, div_neg_eq_neg_div, neg_div', neg_neg]

/-! ### Pinching (completely-dephasing) monotonicity (HEADLINE) -/

/-- Pinching recovers the classical Fisher information: applying the completely-dephasing channel
(keeping only diagonal entries) collapses the KM metric to `∑_i |A_ii|²/p_i`. This is the
quantum → classical data-processing bridge. -/
theorem kuboMori_diagPart_eq {n : ℕ} (p : Fin n → ℝ) (A : Fin n → Fin n → ℂ) :
    kuboMori p (diagPart A) = ∑ i, Complex.normSq (A i i) / p i := by
  unfold kuboMori diagPart
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- inner sum over j: only j = i survives
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    simp [kmWeight, div_eq_mul_inv]
  · intro j _ hj
    rw [if_neg (fun h => hj h.symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The diagonal (classical Fisher) part of the KM metric. -/
theorem kuboMori_diagPart_eq_classicalFisher {n : ℕ} (p : Fin n → ℝ) (A : Fin n → Fin n → ℂ) :
    kuboMori p (diagPart A) = classicalFisher p (fun i => Complex.normSq (A i i)) := by
  rw [kuboMori_diagPart_eq]; rfl

/-- **The headline result.** The completely-dephasing (pinching) CPTP channel does not
increase the Kubo–Mori Fisher metric:

  `K_ρ(diagPart A) ≤ K_ρ(A)`.

This is a genuine *quantum data-processing inequality*: pinching is a real CPTP channel, and it
maps the full quantum metric down to the classical Fisher information. Proof: the off-diagonal
terms `∑_{i≠j} |A_ij|² L(p_i,p_j)` are nonnegative (each factor `≥ 0`), so dropping them can only
decrease the sum. Completes the classical monotonicity into the quantum regime. -/
theorem pinching_monotone {n : ℕ} (p : Fin n → ℝ) (A : Fin n → Fin n → ℂ)
    (hp : ∀ i, 0 < p i) : kuboMori p (diagPart A) ≤ kuboMori p A := by
  rw [kuboMori_diagPart_eq]
  unfold kuboMori
  -- Rewrite RHS: split each inner sum into its diagonal (j = i) term plus the rest.
  refine Finset.sum_le_sum ?_
  intro i _
  -- want: normSq (A i i) / p i ≤ ∑ j, normSq (A i j) * kmWeight (p i) (p j)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdiag : Complex.normSq (A i i) / p i
      = Complex.normSq (A i i) * kmWeight (p i) (p i) := by
    rw [kmWeight, if_pos rfl]
    rw [div_eq_mul_inv, one_div]
  rw [hdiag]
  refine le_add_of_nonneg_right ?_
  refine Finset.sum_nonneg ?_
  intro j _
  exact mul_nonneg (Complex.normSq_nonneg _) (kmWeight_nonneg (hp i) (hp j))

/-- The classical Fisher information is a lower bound for the quantum KM metric (restatement of
`pinching_monotone` in the classical-Fisher form): `classicalFisher ≤ K_ρ(A)`. -/
theorem classicalFisher_le_kuboMori {n : ℕ} (p : Fin n → ℝ) (A : Fin n → Fin n → ℂ)
    (hp : ∀ i, 0 < p i) :
    classicalFisher p (fun i => Complex.normSq (A i i)) ≤ kuboMori p A := by
  rw [← kuboMori_diagPart_eq_classicalFisher]
  exact pinching_monotone p A hp

/-! ### Reversible (relabeling / eigenbasis-unitary) invariance -/

/-- **Reversible invariance.** Permuting the eigen-indices by any permutation `σ` while correspondingly
relabeling both indices of `A` leaves the Kubo–Mori metric invariant:

  `K_{p∘σ}(A∘(σ×σ)) = K_p(A)`.

This is the discrete / eigenbasis image of unitary invariance `K_{UρU†}(UAU†) = K_ρ(A)`: a
permutation is the reversible (unitary) relabeling of the eigenbasis, and the metric depends only
on the eigenvalues and the entries of `A` in that basis. Reversible evolution does not change the
metric. Proof: reindex both sums along the bijection `σ`. -/
theorem kuboMori_perm_invariant {n : ℕ} (p : Fin n → ℝ) (A : Fin n → Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) :
    kuboMori (fun i => p (σ i)) (fun i j => A (σ i) (σ j)) = kuboMori p A := by
  unfold kuboMori
  simp only []
  rw [← Equiv.sum_comp σ (fun i => ∑ j, Complex.normSq (A i j) * kmWeight (p i) (p j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Equiv.sum_comp σ (fun j => Complex.normSq (A (σ i) j) * kmWeight (p (σ i)) (p j))]

/-! ### Anti-vacuity witness: strict pinching decrease on a non-commuting observable -/

/-- Witness eigenvalues `ρ = diag(2/3, 1/3)`. -/
noncomputable def ρp : Fin 2 → ℝ := ![2/3, 1/3]

/-- Witness observable `A = Pauli-X = [[0,1],[1,0]]` — genuinely non-commuting with `ρ`
(pure off-diagonal). -/
noncomputable def Awit : Fin 2 → Fin 2 → ℂ := ![![0, 1], ![1, 0]]

theorem ρp_pos : ∀ i, 0 < ρp i := by
  intro i; fin_cases i <;> · unfold ρp; norm_num

/-- Pinching Pauli-X to its diagonal gives the zero matrix. -/
theorem diagPart_Awit_eq_zero : ∀ i j, diagPart Awit i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> · unfold diagPart Awit; simp

/-- Pinched value is `0`: the diagonal (classical Fisher) contribution of Pauli-X vanishes,
since its diagonal is zero. -/
theorem kuboMori_diagPart_Awit_eq_zero : kuboMori ρp (diagPart Awit) = 0 := by
  rw [kuboMori_diagPart_eq]
  have : ∀ i : Fin 2, Complex.normSq (Awit i i) / ρp i = 0 := by
    intro i; fin_cases i <;> · unfold Awit; simp
  simp [Finset.sum_congr rfl (fun i _ => this i)]

/-- The full quantum KM metric of Pauli-X on `ρ = diag(2/3,1/3)` equals `2 · L(2/3, 1/3) > 0`. -/
theorem kuboMori_Awit_eq : kuboMori ρp Awit = 2 * kmWeight (2/3) (1/3) := by
  unfold kuboMori ρp Awit
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [kmWeight_symm (1/3) (2/3)]
  norm_num [Complex.normSq]
  ring

theorem kmWeight_two_thirds_pos : 0 < kmWeight (2/3) (1/3) := by
  unfold kmWeight
  rw [if_neg (by norm_num)]
  apply div_pos
  · have : Real.log (1/3) < Real.log (2/3) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  · norm_num

/-- **Anti-vacuity: STRICT pinching decrease on a genuinely non-commuting observable.**
For `ρ = diag(2/3,1/3)` and `A = Pauli-X`, the completely-dephasing channel *strictly* decreases
the KM metric: `K_ρ(diagPart A) = 0 < 2·L(2/3,1/3) = K_ρ(A)`. This shows the pinching monotonicity
is non-trivial — a real CPTP channel strictly reduces the metric, exactly the quantum
data-processing content. -/
theorem pinching_witness_strict : kuboMori ρp (diagPart Awit) < kuboMori ρp Awit := by
  rw [kuboMori_diagPart_Awit_eq_zero, kuboMori_Awit_eq]
  have := kmWeight_two_thirds_pos
  linarith

/-- The classical Fisher information of the pinched Pauli-X witness is `0` (its diagonal vanishes),
strictly below the quantum value — the concrete quantum → classical data-processing gap. -/
theorem classicalFisher_Awit_eq_zero :
    classicalFisher ρp (fun i => Complex.normSq (Awit i i)) = 0 := by
  rw [← kuboMori_diagPart_eq_classicalFisher]
  exact kuboMori_diagPart_Awit_eq_zero

/-! ### Anti-vacuity witness: STRICT KM decrease under a genuine NON-UNITAL channel

The pinching witness above is a *unital* (doubly-stochastic) channel. A stronger test is the
data-processing inequality on a genuinely **non-unital** CPTP channel — one that moves the
maximally mixed state. The **amplitude-damping** channel `Φ_γ` is the canonical example: at
damping `γ` it maps (Schrödinger picture)

  `ρ = diag(p₀, p₁)  ↦  diag(p₀ + γ p₁, (1-γ) p₁)`   (population decays toward |0⟩),

and the tangent `X = Pauli-X` (pure off-diagonal) has its off-diagonal amplitude scaled by
`√(1-γ)`, hence `|X_01|²` scaled by `(1-γ)`. Unlike pinching, `Φ_γ` does **not** kill the
off-diagonal (`[Φ_γ ρ, Φ_γ X] ≠ 0`): it is a genuine non-pinching, non-unital channel.

We instantiate the certificate: `ρ = diag(2/3, 1/3)`, `X = Pauli-X`, `γ = 1/2`.

* Pre-channel:  `K_ρ(X)          = 2·L(2/3,1/3) = 6·log 2   ≈ 4.158883`  (`kuboMori_Awit_eq`).
* Post-channel: `Φ_½ρ = diag(5/6,1/6)`, tangent off-diagonal `|·|²` scaled by `(1-½)=½`, giving
  `K_{Φρ}(ΦX)     = ½·2·L(5/6,1/6) = L(5/6,1/6) = (3/2)·log 5 ≈ 2.414157`.

Strict decrease `K_{Φρ}(ΦX) < K_ρ(X)` reduces to the scalar log-mean inequality
`(3/2)·log 5 < 6·log 2`, i.e. `log 5 < 4·log 2 = log 16`, which holds since `5 < 16`. This is the
non-vacuity certificate: a real strict KM/canonical-energy decrease under a non-unital,
non-pinching CPTP map, upgrading the pinching-only DPI. -/

/-- Post-amplitude-damping eigenvalues at `γ = 1/2`: `Φ_½(diag(2/3,1/3)) = diag(5/6,1/6)`. -/
noncomputable def ρpost : Fin 2 → ℝ := ![5/6, 1/6]

/-- Post-amplitude-damping tangent at `γ = 1/2`: `Pauli-X` with its off-diagonal amplitude scaled
by `√(1-γ) = √(1/2)`, so that `normSq` of each off-diagonal entry is `(1-γ) = 1/2`. -/
noncomputable def Apost : Fin 2 → Fin 2 → ℂ :=
  ![![0, (Real.sqrt (1/2) : ℂ)], ![(Real.sqrt (1/2) : ℂ), 0]]

theorem ρpost_pos : ∀ i, 0 < ρpost i := by
  intro i; fin_cases i <;> · unfold ρpost; norm_num

/-- The off-diagonal entry of the post-channel tangent has `normSq = 1/2 = (1-γ)`. -/
theorem normSq_Apost_offdiag : Complex.normSq (Real.sqrt (1/2) : ℂ) = 1/2 := by
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]

/-- The post-amplitude-damping KM metric equals `(1-γ)·2·L(5/6,1/6) = L(5/6,1/6)` at `γ = 1/2`. -/
theorem kuboMori_Apost_eq : kuboMori ρpost Apost = kmWeight (5/6) (1/6) := by
  unfold kuboMori ρpost Apost
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [kmWeight_symm (1/6) (5/6)]
  rw [Complex.normSq_zero, normSq_Apost_offdiag]
  ring

/-- The post-channel tangent is genuinely non-pinching: its off-diagonal entries are nonzero, so
`Φ_γ` does not project onto the eigenbasis (`[Φρ, ΦX] ≠ 0`). -/
theorem Apost_offdiag_ne_zero : Apost 0 1 ≠ 0 := by
  show (Real.sqrt (1/2) : ℂ) ≠ 0
  have : (0:ℝ) < Real.sqrt (1/2) := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast ne_of_gt this

/-- The scalar log-mean inequality underlying the amplitude-damping witness:
`L(5/6,1/6) < 2·L(2/3,1/3)`, i.e. `(3/2)·log 5 < 6·log 2`, i.e. `log 5 < log 16`. -/
theorem kmWeight_post_lt : kmWeight (5/6) (1/6) < 2 * kmWeight (2/3) (1/3) := by
  have hnum5 : Real.log (5/6) - Real.log (1/6) = Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num),
        Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  have hnum2 : Real.log (2/3) - Real.log (1/3) = Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),
        Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  have e5 : kmWeight (5/6) (1/6) = (3/2) * Real.log 5 := by
    unfold kmWeight
    rw [if_neg (by norm_num), hnum5]
    norm_num; ring
  have e2 : 2 * kmWeight (2/3) (1/3) = 6 * Real.log 2 := by
    unfold kmWeight
    rw [if_neg (by norm_num), hnum2]
    norm_num; ring
  rw [e5, e2]
  -- (3/2)·log5 < 6·log2  ⟺  log5 < 4·log2 = log 16, since 5 < 16.
  have hlog : Real.log 5 < 4 * Real.log 2 := by
    have h16 : (4 : ℝ) * Real.log 2 = Real.log 16 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; push_cast; ring
    rw [h16]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- **Non-vacuity certificate — STRICT KM decrease under a NON-UNITAL (amplitude-damping)
channel.** For `ρ = diag(2/3,1/3)`, tangent `X = Pauli-X`, damping `γ = 1/2`:

  `K_{Φρ}(ΦX) = L(5/6,1/6) = (3/2)·log 5  ≈ 2.414157  <  6·log 2 = 2·L(2/3,1/3) = K_ρ(X) ≈ 4.158883`.

Unlike pinching (`pinching_witness_strict`), the amplitude-damping channel is **non-unital** and
**non-pinching** (`Apost_offdiag_ne_zero`: the post-channel tangent keeps a nonzero off-diagonal,
`[Φρ, ΦX] ≠ 0`). This is a genuine strict
Kubo–Mori / canonical-energy decrease under a real non-unital CPTP map, upgrading the
pinching-only quantum data-processing inequality. -/
theorem amplitudeDamping_witness_strict : kuboMori ρpost Apost < kuboMori ρp Awit := by
  rw [kuboMori_Apost_eq, kuboMori_Awit_eq]
  exact kmWeight_post_lt

end Physlib.QuantumKMMonotone
