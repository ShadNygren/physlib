/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib
/-!

# The quantum Kubo–Mori (Bogoliubov) Fisher information metric

This module formalizes the **quantum** (non-commuting) Kubo–Mori metric — the
second-order variation of quantum relative entropy at a positive-definite
density matrix ρ, in the direction of a Hermitian perturbation `A = δρ`.  In
physics this object is:

* the **Kubo–Mori / Bogoliubov information metric** of quantum information
  geometry,
* equal to the **holographic canonical energy** of a linearized bulk
  perturbation (Faulkner–Guica–Hartman–Myers–Van Raamsdonk 2013; Lashkari–Van
  Raamsdonk 2016),
* the genuinely **non-linear** (second-order) content of the entanglement
  first law that a first-order (linear) derivation cannot reach.

## The closed form

At a positive-definite ρ the operator-integral definition
`K_ρ(A) = ∫₀^∞ Tr[ A (ρ + s)⁻¹ A (ρ + s)⁻¹ ] ds`
evaluates, in ρ's eigenbasis with eigenvalues `pᵢ > 0`, to the elementwise sum
`K_ρ(A) = Σᵢⱼ |Aᵢⱼ|² · L(pᵢ, pⱼ)`,
where `L(x,y) = (log x − log y)/(x − y)` for `x ≠ y` and `L(x,x) = 1/x` is the
reciprocal logarithmic mean — the **Kubo–Mori weight**.  We take this closed
form as the definition, sidestepping the operator integral while capturing
exactly the same metric.

## Relation to the classical case

The classical / diagonal Fisher metric is `Σᵢ Aᵢᵢ²/pᵢ`.  The
present metric restricts to exactly that on the diagonal (since `L(pᵢ,pᵢ) =
1/pᵢ`); the **off-diagonal** terms `Σ_{i≠j} |Aᵢⱼ|² L(pᵢ,pⱼ)` are the new,
genuinely quantum, non-commuting content that the classical case does not have.
The anti-vacuity witness below (ρ = diag(2/3,1/3), A = Pauli-X) has `[ρ,A] ≠ 0`
and puts **all** of its weight in these off-diagonal terms, so it is a genuine
advance beyond the classical case, not a relabeling of it.

## Future work

The operator-integral ↔ closed-form identity
`∫₀^∞ ds/((a+s)(b+s)) = (log a − log b)/(a−b)`
would rigorously tie this definition to the integral form; it is a clean
improper-integral-of-a-rational-function lemma left for a follow-up.

-/

@[expose] public section

namespace Physlib.QuantumKuboMori

open scoped BigOperators
open Matrix

/-! ## The Kubo–Mori weight -/

/-- The **Kubo–Mori weight** `L(x,y)`: the reciprocal logarithmic mean of `x`
and `y`.  For `x ≠ y` it is `(log x − log y)/(x − y)`; on the diagonal
`L(x,x) = 1/x`.  Every weight is strictly positive at positive arguments
(`kmWeight_pos`), which is what makes the Kubo–Mori metric positive-definite. -/
noncomputable def kmWeight (x y : ℝ) : ℝ :=
  if x = y then 1 / x else (Real.log x - Real.log y) / (x - y)

@[simp] theorem kmWeight_self (x : ℝ) : kmWeight x x = 1 / x := by
  simp [kmWeight]

/-- **Positivity of the Kubo–Mori weight.**  For positive `x, y` the weight is
strictly positive.  On the diagonal it is `1/x > 0`; off the diagonal it is a
ratio of two quantities of the *same sign* (both positive when `x > y`, both
negative when `x < y`), because `Real.log` is strictly monotone. -/
theorem kmWeight_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < kmWeight x y := by
  unfold kmWeight
  rcases lt_trichotomy x y with hlt | heq | hgt
  · -- x < y : numerator < 0 and denominator < 0
    rw [if_neg (ne_of_lt hlt)]
    have hnum : Real.log x - Real.log y < 0 := by
      have := Real.log_lt_log hx hlt
      linarith
    have hden : x - y < 0 := by linarith
    exact div_pos_of_neg_of_neg hnum hden
  · -- x = y : 1/x
    rw [if_pos heq]
    exact one_div_pos.mpr hx
  · -- y < x : numerator > 0 and denominator > 0
    rw [if_neg (ne_of_gt hgt)]
    have hnum : 0 < Real.log x - Real.log y := by
      have := Real.log_lt_log hy hgt
      linarith
    have hden : 0 < x - y := by linarith
    exact div_pos hnum hden

/-- The Kubo–Mori weight is symmetric: `L(x,y) = L(y,x)`. -/
theorem kmWeight_symm (x y : ℝ) : kmWeight x y = kmWeight y x := by
  unfold kmWeight
  rcases eq_or_ne x y with h | h
  · rw [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    rw [← neg_sub (Real.log y) (Real.log x), ← neg_sub y x, neg_div_neg_eq]

/-! ## The Kubo–Mori metric -/

variable {n : ℕ}

/-- The **quantum Kubo–Mori metric** in ρ's eigenbasis: `p` are the eigenvalues
of ρ and `A` is the Hermitian perturbation `δρ` expressed in that basis.  The
metric is `Σᵢⱼ |Aᵢⱼ|² L(pᵢ, pⱼ)`.  Diagonal terms reproduce the classical
Fisher metric (`kuboMori_diagonal_eq_classical`); off-diagonal terms are the
quantum content. -/
noncomputable def kuboMori (p : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j) * kmWeight (p i) (p j)

/-- **Non-negativity** of the Kubo–Mori metric: a sum of products of a
non-negative modulus-squared and a positive weight. -/
theorem kuboMori_nonneg {p : Fin n → ℝ} (hp : ∀ i, 0 < p i)
    (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ kuboMori p A := by
  unfold kuboMori
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (Complex.normSq_nonneg _)
    (le_of_lt (kmWeight_pos (hp i) (hp j)))

/-- Each individual summand of `kuboMori` is non-negative. -/
private theorem kuboMori_summand_nonneg {p : Fin n → ℝ} (hp : ∀ i, 0 < p i)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    0 ≤ Complex.normSq (A i j) * kmWeight (p i) (p j) :=
  mul_nonneg (Complex.normSq_nonneg _) (le_of_lt (kmWeight_pos (hp i) (hp j)))

/-- **Strict positivity** (positive-definiteness) of the Kubo–Mori metric: for a
nonzero perturbation `A` the metric is strictly positive.  Some entry `A i j`
is nonzero, so its `|Aᵢⱼ|² > 0` times the positive weight `L(pᵢ,pⱼ) > 0` is a
strictly positive summand, while all other summands are non-negative. -/
theorem kuboMori_pos {p : Fin n → ℝ} (hp : ∀ i, 0 < p i)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ≠ 0) : 0 < kuboMori p A := by
  -- extract a nonzero entry
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (by ext i j; simpa using h i j)
  unfold kuboMori
  -- the (i,j) summand is strictly positive
  have hpos_ij : 0 < Complex.normSq (A i j) * kmWeight (p i) (p j) :=
    mul_pos (Complex.normSq_pos.mpr hij) (kmWeight_pos (hp i) (hp j))
  -- inner sum over j' is ≥ its (i,j) summand
  have hinner : 0 < ∑ j', Complex.normSq (A i j') * kmWeight (p i) (p j') := by
    apply Finset.sum_pos'
    · intro k _
      exact kuboMori_summand_nonneg hp A i k
    · exact ⟨j, Finset.mem_univ j, hpos_ij⟩
  -- outer sum over i' is ≥ its i summand
  apply Finset.sum_pos'
  · intro k _
    apply Finset.sum_nonneg
    intro l _
    exact kuboMori_summand_nonneg hp A k l
  · exact ⟨i, Finset.mem_univ i, hinner⟩

/-! ## The classical-reduction bridge -/

/-- **Classical reduction.**  On a *diagonal* perturbation `A`
(so `A i j = 0` for `i ≠ j`) the quantum Kubo–Mori metric collapses to the
classical Fisher metric `Σᵢ |Aᵢᵢ|²/pᵢ`.
This shows the quantum metric *restricts* to the classical one on commuting
(diagonal) perturbations; all genuinely quantum content lives in the
off-diagonal terms that vanish here. -/
theorem kuboMori_diagonal_eq_classical {p : Fin n → ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hdiag : ∀ i j, i ≠ j → A i j = 0) :
    kuboMori p A = ∑ i, Complex.normSq (A i i) / p i := by
  unfold kuboMori
  apply Finset.sum_congr rfl
  intro i _
  -- inner sum over j collapses to the j = i term
  rw [Finset.sum_eq_single i]
  · rw [kmWeight_self, mul_one_div]
  · intro j _ hji
    rw [hdiag i j (Ne.symm hji), map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## Physics bridge: holographic canonical energy -/

/-- **Holographic canonical energy** of a linearized bulk perturbation, equal to
the quantum Kubo–Mori second-order relative entropy (Faulkner–GHMV 2013;
Lashkari–Van Raamsdonk 2016).  Definitionally the Kubo–Mori metric. -/
noncomputable def canonicalEnergyQuantum (p : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  kuboMori p A

/-- The holographic canonical energy is non-negative — the second-order
positivity of relative entropy / bulk energy positivity. -/
theorem canonical_energy_quantum_nonneg {p : Fin n → ℝ} (hp : ∀ i, 0 < p i)
    (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ canonicalEnergyQuantum p A :=
  kuboMori_nonneg hp A

/-- The holographic canonical energy is strictly positive for a nonzero
perturbation. -/
theorem canonical_energy_quantum_pos {p : Fin n → ℝ} (hp : ∀ i, 0 < p i)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ≠ 0) :
    0 < canonicalEnergyQuantum p A :=
  kuboMori_pos hp hA

/-! ## Anti-vacuity: a genuinely NON-COMMUTING witness

We instantiate ρ = diag(2/3, 1/3) (a positive, unit-trace density matrix) and
`A =  !![0,1;1,0]` (Pauli-X).  Because ρ is non-degenerate diagonal and A is
purely off-diagonal, `[ρ, A] ≠ 0`: this is a *genuinely non-commuting*
perturbation, so its Kubo–Mori value comes entirely from the quantum
off-diagonal weights — content strictly beyond the classical/diagonal case.
-/

/-- The witness eigenvalue vector `p = (2/3, 1/3)`. -/
noncomputable def ρp : Fin 2 → ℝ := ![2/3, 1/3]

/-- The witness perturbation `A = !![0,1;1,0]` (real off-diagonal / Pauli-X). -/
def Awit : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The witness eigenvalues are strictly positive. -/
theorem ρp_pos : ∀ i, 0 < ρp i := by
  intro i
  fin_cases i <;> norm_num [ρp]

/-- The witness perturbation is nonzero. -/
theorem Awit_ne_zero : Awit ≠ 0 := by
  intro h
  have : Awit 0 1 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by rw [h]
  simp [Awit] at this

/-- **Genuine non-commutativity certificate.**  As a diagonal, non-degenerate ρ
does not commute with the off-diagonal A: the `(0,1)` entry of the commutator
`ρ·A − A·ρ` is `2/3 − 1/3 = 1/3 ≠ 0`.  Here `ρ = diagonal (ρp)` as a complex
matrix. -/
theorem witness_noncommuting :
    ((Matrix.diagonal (fun i => (ρp i : ℂ)) * Awit
      - Awit * Matrix.diagonal (fun i => (ρp i : ℂ))) 0 1) ≠ 0 := by
  have h : (Matrix.diagonal (fun i => (ρp i : ℂ)) * Awit
      - Awit * Matrix.diagonal (fun i => (ρp i : ℂ))) 0 1 = 1/3 := by
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply_eq, Awit, ρp]
    simp only [Matrix.diagonal, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    norm_num
  rw [h]; norm_num

/-- **The witness value is strictly positive.**  All the weight sits in the two
off-diagonal (quantum) entries, giving
`kuboMori ρp Awit = 2 · L(2/3, 1/3) > 0`. -/
theorem kuboMori_witness_eq :
    kuboMori ρp Awit = 2 * kmWeight (2/3) (1/3) := by
  -- entry values
  have a00 : Awit 0 0 = 0 := by simp [Awit]
  have a01 : Awit 0 1 = 1 := by simp [Awit]
  have a10 : Awit 1 0 = 1 := by simp [Awit]
  have a11 : Awit 1 1 = 0 := by simp [Awit]
  have p0 : ρp 0 = 2/3 := by simp [ρp]
  have p1 : ρp 1 = 1/3 := by simp [ρp]
  unfold kuboMori
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [a00, a01, a10, a11, p0, p1]
  simp only [map_zero, Complex.normSq_one, zero_mul, zero_add, add_zero]
  -- remaining: kmWeight (2/3)(1/3) + kmWeight (1/3)(2/3) = 2 * kmWeight (2/3)(1/3)
  rw [kmWeight_symm (1/3) (2/3)]
  ring

/-- **Anti-vacuity conclusion:** the Kubo–Mori metric of the genuinely
non-commuting witness `(ρ, A)` is strictly positive.  This exhibits the quantum
metric on a perturbation with `[ρ,A] ≠ 0`, so it is a real advance over the
classical/diagonal Fisher metric — not a relabeling of it. -/
theorem kuboMori_witness_pos : 0 < kuboMori ρp Awit :=
  kuboMori_pos ρp_pos Awit_ne_zero

end Physlib.QuantumKuboMori
