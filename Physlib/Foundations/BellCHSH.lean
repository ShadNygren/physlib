/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
import Mathlib.Algebra.Star.CHSH
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Bell's theorem as a machine-checked no-go by contradiction (CHSH)

Bell's theorem is the archetypal *no-go by contradiction*: any **local hidden-variable**
(LHV) model of a bipartite experiment must satisfy the CHSH inequality

  `A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ 2`,

yet quantum mechanics predicts (and experiment confirms) correlations reaching the
Tsirelson value `2√2 > 2`.  Therefore **no** local hidden-variable model can reproduce
the quantum correlations — the LHV hypothesis is refuted by contradiction.

`Mathlib.Algebra.Star.CHSH` already provides the two bounds abstractly:

* `IsCHSHTuple A₀ A₁ B₀ B₁` — four self-adjoint involutions with the `Aᵢ`
  commuting with the `Bⱼ` (Boolean ±1 observables, spacelike separated).
* `CHSH_inequality_of_comm` — the **classical / LHV bound** `≤ 2`, valid in any
  *commutative* ordered `ℝ`-⋆-algebra.
* `tsirelson_inequality` — the **quantum bound** `≤ 2√2 = √2^3`, valid in any
  (possibly noncommutative) ordered `ℝ`-⋆-algebra.

This file does **not** reprove those.  Instead it supplies the two missing pieces that
turn them into Bell's no-go:

1. A concrete, *proven* quantum **violation witness**: an explicit `IsCHSHTuple` of
   `4 × 4` real matrices (the standard two-qubit Tsirelson construction, realised over ℝ)
   together with a concrete state `ψ` in which the CHSH observable takes the value
   `2√2 · ‖ψ‖²`, strictly exceeding the LHV ceiling `2 · ‖ψ‖²`.  This is a nonzero,
   fully computed violation — not a vacuous `0 ≤ 0`.

2. The **no-go theorem** `bell_no_local_hidden_variable`: the LHV premise (modelled as
   full commutativity, via `CHSH_inequality_of_comm`) forces the value `≤ 2`, which
   contradicts the witnessed value `> 2`; hence the LHV hypothesis is false.

## The construction

On two qubits (`ℂ²⊗ℂ² ≅ ℝ⁴` for our real realisation) take, with `X = !![0,1;1,0]`,
`Z = !![1,0;0,-1]`:

* `A₀ = Z ⊗ I`, `A₁ = X ⊗ I`  (Alice's two settings),
* `B₀ = I ⊗ (−Z−X)/√2`, `B₁ = I ⊗ (Z−X)/√2`  (Bob's two rotated settings).

All four are self-adjoint involutions and every `Aᵢ` commutes with every `Bⱼ`.  The CHSH
operator `S = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` satisfies `S ψ = 2√2 · ψ` on
`ψ = (−1, 1, 1, 1)`, so `⟪ψ, S ψ⟫ = 2√2 · ⟪ψ, ψ⟫ > 2 · ⟪ψ, ψ⟫`.
-/

namespace Physlib.Foundations.BellCHSH

open Matrix Real

noncomputable section

/-- The real `4 × 4` matrix algebra, our realisation of the two-qubit observable algebra. -/
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Alice's first setting `A₀ = Z ⊗ I`. -/
def A0 : M4 := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

/-- Alice's second setting `A₁ = X ⊗ I`. -/
def A1 : M4 := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

/-- `√2 · B₀`, where `B₀ = I ⊗ (−Z−X)/√2` is Bob's first setting. -/
def B0r : M4 := !![-1,-1,0,0; -1,1,0,0; 0,0,-1,-1; 0,0,-1,1]

/-- `√2 · B₁`, where `B₁ = I ⊗ (Z−X)/√2` is Bob's second setting. -/
def B1r : M4 := !![1,-1,0,0; -1,-1,0,0; 0,0,1,-1; 0,0,-1,-1]

/-- Bob's first setting `B₀ = I ⊗ (−Z−X)/√2`. -/
def B0 : M4 := (Real.sqrt 2)⁻¹ • B0r

/-- Bob's second setting `B₁ = I ⊗ (Z−X)/√2`. -/
def B1 : M4 := (Real.sqrt 2)⁻¹ • B1r

/-- A tactic to discharge a concrete entrywise identity between `4 × 4` real matrices
built from `A0, A1, B0r, B1r`. -/
macro "mat4" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_four, A0, A1, B0r, B1r,
          Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] <;> ring_nf))

/-! ### The four operators are self-adjoint involutions that cross-commute -/

theorem A0_sq : A0 ^ 2 = 1 := by mat4
theorem A1_sq : A1 ^ 2 = 1 := by mat4

theorem B0r_sq : B0r * B0r = (2 : ℝ) • (1 : M4) := by mat4
theorem B1r_sq : B1r * B1r = (2 : ℝ) • (1 : M4) := by mat4

/-- `(√2)⁻¹ * (√2)⁻¹ * 2 = 1`, the scalar fact behind `B₀² = B₁² = 1`. -/
private theorem sqrt2_inv_sq_mul_two : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = 1 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem B0_sq : B0 ^ 2 = 1 := by
  have h : B0 ^ 2 = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) • (B0r * B0r) := by
    simp [B0, pow_two, smul_smul]
  rw [h, B0r_sq, smul_smul, sqrt2_inv_sq_mul_two, one_smul]

theorem B1_sq : B1 ^ 2 = 1 := by
  have h : B1 ^ 2 = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) • (B1r * B1r) := by
    simp [B1, pow_two, smul_smul]
  rw [h, B1r_sq, smul_smul, sqrt2_inv_sq_mul_two, one_smul]

/-- Self-adjointness: for a real matrix `star = conjTranspose = transpose` and star on `ℝ` is
the identity, so `star M = M` reduces to symmetry, which we check entrywise. -/
theorem A0_sa : star A0 = A0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A0]
theorem A1_sa : star A1 = A1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A1]
theorem B0r_sa : star B0r = B0r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [B0r]
theorem B1r_sa : star B1r = B1r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [B1r]

theorem B0_sa : star B0 = B0 := by rw [B0, star_smul, B0r_sa, star_trivial]
theorem B1_sa : star B1 = B1 := by rw [B1, star_smul, B1r_sa, star_trivial]

theorem A0B0r_comm : A0 * B0r = B0r * A0 := by mat4
theorem A0B1r_comm : A0 * B1r = B1r * A0 := by mat4
theorem A1B0r_comm : A1 * B0r = B0r * A1 := by mat4
theorem A1B1r_comm : A1 * B1r = B1r * A1 := by mat4

/-- The Aᵢ commute with the Bⱼ (spacelike separation). -/
theorem A0B0_comm : A0 * B0 = B0 * A0 := by
  simp only [B0, Matrix.mul_smul, Matrix.smul_mul, A0B0r_comm]
theorem A0B1_comm : A0 * B1 = B1 * A0 := by
  simp only [B1, Matrix.mul_smul, Matrix.smul_mul, A0B1r_comm]
theorem A1B0_comm : A1 * B0 = B0 * A1 := by
  simp only [B0, Matrix.mul_smul, Matrix.smul_mul, A1B0r_comm]
theorem A1B1_comm : A1 * B1 = B1 * A1 := by
  simp only [B1, Matrix.mul_smul, Matrix.smul_mul, A1B1r_comm]

/-- **The quantum CHSH tuple.**  The concrete two-qubit construction is a genuine
`IsCHSHTuple`: four self-adjoint involutions with the `Aᵢ` commuting with the `Bⱼ`. -/
theorem isCHSHTuple_witness : IsCHSHTuple A0 A1 B0 B1 where
  A₀_inv := A0_sq
  A₁_inv := A1_sq
  B₀_inv := B0_sq
  B₁_inv := B1_sq
  A₀_sa := A0_sa
  A₁_sa := A1_sa
  B₀_sa := B0_sa
  B₁_sa := B1_sa
  A₀B₀_commutes := A0B0_comm
  A₀B₁_commutes := A0B1_comm
  A₁B₀_commutes := A1B0_comm
  A₁B₁_commutes := A1B1_comm

/-! ### The quantum violation: `S ψ = 2√2 · ψ` -/

/-- `√2 · S`, where `S = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` is the CHSH observable. -/
def Sr : M4 := A0 * B0r + A0 * B1r + A1 * B0r - A1 * B1r

/-- The CHSH observable `S = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁`. -/
def S : M4 := A0 * B0 + A0 * B1 + A1 * B0 - A1 * B1

theorem S_eq_smul_Sr : S = (Real.sqrt 2)⁻¹ • Sr := by
  simp only [S, Sr, B0, B1, Matrix.mul_smul, smul_add, smul_sub]

/-- `√2 · S` reduces to an explicit integer matrix. -/
theorem Sr_eq : Sr = !![0,-2,-2,0; -2,0,0,2; -2,0,0,2; 0,2,2,0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Sr, A0, A1, B0r, B1r, Matrix.sub_apply] <;> norm_num

/-- The state exhibiting maximal violation (the `+2√2` eigenvector of `S`). -/
def psi : Fin 4 → ℝ := ![-1, 1, 1, 1]

/-- `(√2 · S) ψ = 4 · ψ`. -/
theorem Sr_mulVec_psi : Sr.mulVec psi = (4 : ℝ) • psi := by
  rw [Sr_eq]
  funext i; fin_cases i <;>
    simp [psi, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- **The eigenvalue equation `S ψ = 2√2 · ψ`.**  The CHSH observable attains the
Tsirelson value on `ψ`. -/
theorem S_mulVec_psi : S.mulVec psi = (2 * Real.sqrt 2) • psi := by
  rw [S_eq_smul_Sr, Matrix.smul_mulVec, Sr_mulVec_psi, smul_smul]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have : (Real.sqrt 2)⁻¹ * 4 = 2 * Real.sqrt 2 := by
    rw [inv_mul_eq_div, div_eq_iff (ne_of_gt hpos)]
    nlinarith [h2]
  rw [this]

/-- The CHSH expectation `⟪ψ, S ψ⟫`. -/
def chshValue : ℝ := dotProduct psi (S.mulVec psi)

/-- The squared norm `⟪ψ, ψ⟫ = 4 ≠ 0`. -/
theorem psi_normSq : dotProduct psi psi = 4 := by
  simp [psi, dotProduct, Fin.sum_univ_four]; ring

/-- **The quantum CHSH value equals `2√2 · ‖ψ‖²`.** -/
theorem chshValue_eq : chshValue = 2 * Real.sqrt 2 * dotProduct psi psi := by
  rw [chshValue, S_mulVec_psi, dotProduct_smul, smul_eq_mul, psi_normSq]

/-- `2 < 2√2`: Tsirelson strictly beats the classical ceiling. -/
theorem two_lt_two_sqrt_two : (2 : ℝ) < 2 * Real.sqrt 2 := by
  have h : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith [h]

/-- **The quantum violation (anti-vacuity witness).**  In the state `ψ`, the CHSH
observable strictly exceeds the classical LHV ceiling `2 · ‖ψ‖²`:
`⟪ψ, S ψ⟫ = 2√2·‖ψ‖² > 2·‖ψ‖²`.  This is a concrete, nonzero violation. -/
theorem chsh_violation : 2 * dotProduct psi psi < chshValue := by
  rw [chshValue_eq]
  have hpos : (0 : ℝ) < dotProduct psi psi := by rw [psi_normSq]; norm_num
  nlinarith [two_lt_two_sqrt_two, hpos]

/-! ### Bell's no-go theorem -/

/-- **Classical / LHV bound (restatement of `CHSH_inequality_of_comm`).**  In any
*commutative* ordered `ℝ`-⋆-algebra — the algebra of a local hidden-variable model,
where all observables share definite simultaneous values — every CHSH tuple obeys
`A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ 2`. -/
theorem chsh_le_two_of_commutative {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [Algebra ℝ R] [IsOrderedModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 :=
  CHSH_inequality_of_comm A₀ A₁ B₀ B₁ T

/-- **Bell's theorem, no-go form (abstract contradiction).**  Suppose a local
hidden-variable model is a commutative ordered `ℝ`-⋆-algebra `R` carrying a CHSH tuple.
Then it *cannot* reproduce any correlation value `v` exceeding the classical ceiling `2`
(such as the quantum `2√2`): the LHV assumptions force `v ≤ 2`, contradicting `2 < v`.
Formally: there is no commutative CHSH tuple whose CHSH value strictly exceeds `2`. -/
theorem bell_no_local_hidden_variable {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [Algebra ℝ R] [IsOrderedModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) (v : R)
    (hv : v = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) (hgt : 2 < v) : False := by
  have hle : v ≤ 2 := hv.symm ▸ chsh_le_two_of_commutative A₀ A₁ B₀ B₁ T
  exact absurd (lt_of_lt_of_le hgt hle) (lt_irrefl 2)

/-- **The quantum witness is not a local hidden-variable model.**  The concrete tuple
`(A₀, A₁, B₀, B₁)` achieves a CHSH value `> 2`, so its observables cannot all commute —
Alice's two settings `A₀, A₁` genuinely fail to commute.  Equivalently: no commutative
(LHV) model reproduces these correlations.

The proof is the Bell contradiction made concrete.  If `A₀` and `A₁` commuted, the whole
witness would generate a *commutative* ⋆-subalgebra, on which `CHSH_inequality_of_comm`
bounds the value by `2`; but the value is `2√2 > 2`.  Here we exhibit the noncommutativity
directly, which is the mathematical residue of that contradiction. -/
theorem witness_not_commutative : ¬ A0 * A1 = A1 * A0 := by
  -- The two products differ (they are the ±[X,Z]⊗I commutator terms); exhibit the mismatch.
  have hp : A0 * A1 = !![0,0,1,0; 0,0,0,1; -1,0,0,0; 0,-1,0,0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A0, A1, Matrix.mul_apply, Fin.sum_univ_four]
  have hq : A1 * A0 = !![0,0,-1,0; 0,0,0,-1; 1,0,0,0; 0,1,0,0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A0, A1, Matrix.mul_apply, Fin.sum_univ_four]
  intro h
  rw [hp, hq] at h
  have h02 : (1 : ℝ) = -1 := by
    have := congrFun (congrFun h 0) 2
    simpa using this
  norm_num at h02

end

end Physlib.Foundations.BellCHSH
