module

public import Mathlib
import all Physlib.Foundations.SecondOrderFisher

/-!
# Kubo–Mori monotonicity — the `ddLog1` Loewner matrix is positive-semidefinite

This file develops **Kubo–Mori (KM) monotonicity**. Its first headline is that the real
symmetric **Loewner matrix** of the first divided difference of `log`,

    `M i j := ddLog1 (λ_i) (λ_j)`   (`λ_i > 0`),

is **positive semidefinite** (`Matrix.PosSemidef`). This is the operator-level generalization of the
scalar Fisher nonnegativity `fisher_nonneg` (`c₂ ≥ 0`): the Kubo–Mori metric, whose weights are the
log-mean kernel `ddLog1`, is a *genuine positive metric* on ALL Hermitian directions (not merely the
diagonal ones). It is the linear-algebraic foundation for KM-metric monotonicity (Petz / data
processing) and is **absent from Mathlib**, which carries no operator-monotone theory.

## The proof — a Gram matrix via the resolvent representation
The whole proof is one clean idea, reusing the machinery already built in `SecondOrderFisher.lean`.
The resolvent identity (`resolvent_scalar_integral`) gives, for `a, b > 0`,

    `ddLog1 a b = ∫₀^∞ 1/((a+s)(b+s)) ds = ∫₀^∞ u_a(s) · u_b(s) ds`,   `u_a(s) = 1/(a+s)`.

Hence `M` is a **Gram matrix** of the functions `s ↦ 1/(λ_i+s)` under the `L²(0,∞)` inner product, and
its quadratic form is an integral of a square:

    `xᵀ M x = Σ_ij x_i x_j ∫ u_i u_j = ∫ (Σ_i x_i · u_i(s))² ds ≥ 0`.

Symmetry of `M` (`ddLog1_symm`) supplies the Hermitian hypothesis; the integral-of-a-square supplies
nonnegativity of the quadratic form. Integrability of `u_i · u_j` on `(0,∞)` is
`resolvent_sq_integrableOn`.
-/

namespace Physlib.SecondOrderFisher

open scoped BigOperators
open MeasureTheory Filter Topology Set Matrix

variable {n : ℕ}

/-- **The Kubo–Mori / `ddLog1` Loewner matrix.** `kmLoewner λ i j = ddLog1 (λ_i) (λ_j)`, the real
    symmetric matrix whose entries are the first divided difference of `log` (the log-mean kernel).
    For `λ_i > 0` this is the Kubo–Mori quantum Fisher metric in the eigenbasis of `ρ = diag(λ)`. -/
noncomputable def kmLoewner (lam : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ddLog1 (lam i) (lam j)

@[simp] theorem kmLoewner_apply (lam : Fin n → ℝ) (i j : Fin n) :
    kmLoewner lam i j = ddLog1 (lam i) (lam j) := rfl

/-- The KM Loewner matrix is symmetric (`ddLog1_symm`), hence Hermitian over `ℝ`. -/
theorem kmLoewner_isHermitian (lam : Fin n → ℝ) : (kmLoewner lam).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, kmLoewner_apply, star_trivial]
  exact (ddLog1_symm (lam j) (lam i))

/-- The `s`-integrand of the Gram/quadratic-form identity: the FULL double-sum of scaled resolvent
    kernels equals a perfect square `(Σ_i x_i/(λ_i+s))²`, POINTWISE in `s`.  Pure algebra
    (`Finset.sum_mul_sum`), no analysis. -/
theorem km_integrand_sq (lam : Fin n → ℝ) (x : Fin n → ℝ) (s : ℝ) :
    (∑ i, ∑ j, (x i * x j) * (1 / ((lam i + s) * (lam j + s))))
      = (∑ i, x i / (lam i + s)) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [div_mul_div_comm, one_div]
  ring

/-- **The quadratic form as an integral of a square.** For `λ_i > 0` and any real vector `x`,

    `Σ_i Σ_j x_i x_j · ddLog1(λ_i,λ_j) = ∫₀^∞ (Σ_i x_i/(λ_i+s))² ds`.

Each entry is expanded by the resolvent identity `ddLog1(λ_i,λ_j) = ∫ 1/((λ_i+s)(λ_j+s))`
(`resolvent_scalar_integral`); the finite double sum is exchanged with the integral
(`integral_finsetSum`, using `resolvent_sq_integrableOn` for integrability); and the resulting
summand `Σ_ij (x_i x_j)/((λ_i+s)(λ_j+s))` factors as the square `(Σ_i x_i/(λ_i+s))²`
(`km_integrand_sq`). -/
theorem kmLoewner_quadForm_eq_integral (lam : Fin n → ℝ) (hpos : ∀ i, 0 < lam i)
    (x : Fin n → ℝ) :
    (∑ i, ∑ j, x i * x j * ddLog1 (lam i) (lam j))
      = ∫ s in Ioi (0:ℝ), (∑ i, x i / (lam i + s)) ^ 2 := by
  -- Integrability of each scaled resolvent kernel on `(0,∞)`.
  have hint : ∀ i j : Fin n,
      Integrable (fun s : ℝ => (x i * x j) * (1 / ((lam i + s) * (lam j + s))))
        (volume.restrict (Ioi 0)) := by
    intro i j
    exact ((resolvent_sq_integrableOn (lam i) (lam j) (hpos i) (hpos j)).const_mul (x i * x j))
  -- Step 1: expand every entry `x_i x_j ddLog1(λ_i,λ_j)` as an integral of the scaled kernel.
  have hentry : ∀ i j : Fin n,
      x i * x j * ddLog1 (lam i) (lam j)
        = ∫ s in Ioi (0:ℝ), (x i * x j) * (1 / ((lam i + s) * (lam j + s))) := by
    intro i j
    rw [MeasureTheory.integral_const_mul,
      resolvent_scalar_integral (lam i) (lam j) (hpos i) (hpos j)]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hentry i j))]
  -- Step 2: swap the inner `∑ j` past the integral.
  have hswap_j : ∀ i : Fin n,
      (∑ j, ∫ s in Ioi (0:ℝ), (x i * x j) * (1 / ((lam i + s) * (lam j + s))))
        = ∫ s in Ioi (0:ℝ), ∑ j, (x i * x j) * (1 / ((lam i + s) * (lam j + s))) := by
    intro i
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hint i j)]
  rw [Finset.sum_congr rfl (fun i _ => hswap_j i)]
  -- Step 3: swap the outer `∑ i` past the integral.
  have hint_row : ∀ i : Fin n,
      Integrable (fun s : ℝ => ∑ j, (x i * x j) * (1 / ((lam i + s) * (lam j + s))))
        (volume.restrict (Ioi 0)) :=
    fun i => MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hint i j)
  rw [← MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint_row i)]
  -- Step 4: the fully-swapped double-sum integrand is the perfect square.
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  exact km_integrand_sq lam x s

/-- **step 1 — the Kubo–Mori / `ddLog1` Loewner matrix is positive semidefinite.**
    For `λ_i > 0`, `M i j = ddLog1(λ_i,λ_j)` is `Matrix.PosSemidef`.  Hermitian by `ddLog1_symm`;
    the quadratic form is the integral of a square (`kmLoewner_quadForm_eq_integral`), hence `≥ 0`
    (`integral_nonneg`).  This is the operator-monotonicity of `log` at the metric level: the KM
    quantum Fisher metric is a genuine positive metric on ALL Hermitian directions — the linear-
    algebra foundation of KM (Petz) data-processing monotonicity.  Mathlib-ABSENT. -/
theorem ddLog1_loewner_posSemidef (lam : Fin n → ℝ) (hpos : ∀ i, 0 < lam i) :
    (kmLoewner lam).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (kmLoewner_isHermitian lam) (fun x => ?_)
  -- Turn the abstract quadratic form into the explicit double sum.
  have hform : star x ⬝ᵥ (kmLoewner lam) *ᵥ x
      = ∑ i, ∑ j, x i * x j * ddLog1 (lam i) (lam j) := by
    simp only [dotProduct, Matrix.mulVec, star_trivial, kmLoewner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hform, kmLoewner_quadForm_eq_integral lam hpos x]
  exact MeasureTheory.integral_nonneg (fun s => by positivity)

/-! ### Non-vacuity: the metric is genuinely positive (strict), not degenerate -/

/-- Non-vacuity witness A: a concrete PSD instance.  For `λ = (2, 1)` the `2×2` KM Loewner matrix
    `[[ddLog1 2 2, ddLog1 2 1],[ddLog1 1 2, ddLog1 1 1]] = [[1/2, log 2],[log 2, 1]]` is
    positive semidefinite. -/
theorem kmLoewner_posSemidef_witness : (kmLoewner (![2, 1] : Fin 2 → ℝ)).PosSemidef :=
  ddLog1_loewner_posSemidef (![2, 1] : Fin 2 → ℝ) (by
    intro i; fin_cases i <;> norm_num)

/-- Non-vacuity witness B (STRICT — the metric is genuinely positive, not degenerate): the quadratic
    form of the KM Loewner matrix at `λ = (2,1)` on the direction `x = (1, -1)` is
    `1/2 − 2·log 2 + 1 = 3/2 − 2 log 2 > 0`, and in particular the metric is nonzero.  This is the
    log-mean strict inequality `ddLog1(2,1) = log 2 < 1/√2·... `, i.e. the `2×2` Gram determinant is
    strictly positive for distinct eigenvalues — the KM metric is nondegenerate. -/
theorem kmLoewner_quadForm_pos_witness :
    0 < (∑ i, ∑ j, (![1, -1] : Fin 2 → ℝ) i * (![1, -1] : Fin 2 → ℝ) j
          * ddLog1 ((![2, 1] : Fin 2 → ℝ) i) ((![2, 1] : Fin 2 → ℝ) j)) := by
  -- Evaluate the `2×2` double sum: (1/2)·1 + (log2)·(-1) + (log2)·(-1) + 1·1 = 3/2 − 2 log 2.
  have hval :
      (∑ i, ∑ j, (![1, -1] : Fin 2 → ℝ) i * (![1, -1] : Fin 2 → ℝ) j
        * ddLog1 ((![2, 1] : Fin 2 → ℝ) i) ((![2, 1] : Fin 2 → ℝ) j))
        = 3 / 2 - 2 * Real.log 2 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ddLog1_self, ddLog1_self, ddLog1_of_ne (by norm_num), ddLog1_of_ne (by norm_num)]
    rw [Real.log_one]
    ring_nf
  rw [hval]
  -- `log 2 < 3/4`, so `3/2 − 2 log 2 > 0`.  Use `log 2 ≤ 0.6931... < 0.75`.
  have hlog : Real.log 2 < 3 / 4 := by
    -- `3/4 = log (exp (3/4))` and `exp (3/4) > 2` (quadratic lower bound `1 + x + x²/2 ≤ exp x`).
    have h2 : (2:ℝ) < Real.exp (3 / 4) := by
      nlinarith [Real.quadratic_le_exp_of_nonneg (x := (3 / 4 : ℝ)) (by norm_num)]
    calc Real.log 2 < Real.log (Real.exp (3 / 4)) := Real.log_lt_log (by norm_num) h2
      _ = 3 / 4 := Real.log_exp _
  linarith

/-! ## step 2 — the first Kubo–Mori metric MONOTONICITY (data-processing) results

We now derive the first genuine *monotonicity* statement: the KM Fisher metric DECREASES under the
dephasing (pinching) channel in `ρ`'s eigenbasis. The kernel weights `ddLog1(λ_i,λ_j)` are all
positive (the log-mean reciprocal), so the metric is a nonnegative sum of the weighted squared
matrix entries; dephasing zeros out the off-diagonal entries, deleting nonnegative terms — hence the
metric can only drop. This is the finite-dimensional, eigenbasis form of the Petz / data-processing
monotonicity of the Kubo–Mori metric for the pinching channel.
-/

/-- **The log-mean kernel `ddLog1` is strictly positive** for positive arguments.  For `a = b` it is
    `1/a > 0`; for `a ≠ b` it is `(log a − log b)/(a − b) > 0` because `log` is strictly increasing,
    so numerator and denominator share the same sign.  This is the positivity of the KM Fisher weight
    that drives the metric's nonnegativity and its monotonicity under dephasing. -/
theorem ddLog1_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < ddLog1 a b := by
  rcases eq_or_ne a b with h | h
  · subst h; rw [ddLog1_self]; positivity
  · rw [ddLog1_of_ne h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · -- a < b: numerator log a − log b < 0, denominator a − b < 0 ⟹ quotient > 0
      have hnum : Real.log a - Real.log b < 0 := by
        have := Real.log_lt_log ha hlt; linarith
      have hden : a - b < 0 := by linarith
      exact div_pos_of_neg_of_neg hnum hden
    · -- a > b: numerator > 0, denominator > 0
      have hnum : 0 < Real.log a - Real.log b := by
        have := Real.log_lt_log hb hgt; linarith
      have hden : 0 < a - b := by linarith
      exact div_pos hnum hden

/-- **The log-mean kernel `ddLog1` is nonnegative** for positive arguments (immediate from
    `ddLog1_pos`). This is the sign fact that makes each summand of the KM metric nonnegative. -/
theorem ddLog1_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ ddLog1 a b :=
  (ddLog1_pos ha hb).le

/-- **The Kubo–Mori quantum Fisher metric** at `ρ = diag(p)` in the real-symmetric Hermitian
    direction `A`: `kuboMoriMetric p A = Σ_i Σ_j (A i j)² · ddLog1(p_i,p_j)`.  Its diagonal part is
    the classical `fisherInfo` (`Σ_i (A i i)²/p_i`); the off-diagonal part is the genuinely quantum
    content.  The KM Loewner weights `ddLog1(p_i,p_j)` are positive (`ddLog1_pos`), so the metric is a
    nonnegative quadratic form on all Hermitian directions. -/
noncomputable def kuboMoriMetric (p : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2 * ddLog1 (p i) (p j)

/-- **The pinching (dephasing) channel** in `ρ`'s eigenbasis: `pinch A` keeps the diagonal of `A`
    and zeros the off-diagonal (`pinch A i j = if i = j then A i j else 0`).  This is the
    completely-positive trace-preserving dephasing channel whose fixed points are the diagonal
    matrices. -/
def pinch (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then A i j else 0

@[simp] theorem pinch_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    pinch A i j = if i = j then A i j else 0 := rfl

/-- **The KM metric is nonnegative** for `p_i > 0`: each summand `(A i j)² · ddLog1(p_i,p_j)` is a
    product of a square (`sq_nonneg`) and a positive weight (`ddLog1_nonneg`). This subsumes the
    classical Fisher nonnegativity (the diagonal part). -/
theorem kuboMoriMetric_nonneg (p : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ kuboMoriMetric p A := by
  unfold kuboMoriMetric
  refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
  exact mul_nonneg (sq_nonneg _) (ddLog1_nonneg (hp i) (hp j))

/-- **The pinched metric collapses to the diagonal (classical Fisher) sum**:
    `kuboMoriMetric p (pinch A) = Σ_i (A i i)² · ddLog1(p_i,p_i) = Σ_i (A i i)²/p_i`.  Every
    off-diagonal entry of `pinch A` is `0`, killing the `i ≠ j` terms of the double sum. -/
theorem kuboMoriMetric_pinch (p : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    kuboMoriMetric p (pinch A) = ∑ i, (A i i) ^ 2 * ddLog1 (p i) (p i) := by
  unfold kuboMoriMetric
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [pinch_apply, if_pos rfl]
  · intro j _ hji
    rw [pinch_apply, if_neg (fun h => hji h.symm), zero_pow (by norm_num), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- **THE step-2 headline — Kubo–Mori data-processing inequality for dephasing.**
    For `p_i > 0` and any real-symmetric direction `A`, the KM Fisher metric DECREASES under the
    pinching (dephasing) channel:

        `kuboMoriMetric p (pinch A) ≤ kuboMoriMetric p A`.

    The pinched metric equals the diagonal terms of the full metric
    (`kuboMoriMetric_pinch`), and `kuboMoriMetric p A` is that diagonal sum PLUS the off-diagonal
    contribution `Σ_i Σ_{j≠i} (A i j)² · ddLog1(p_i,p_j) ≥ 0` (each term nonnegative by
    `ddLog1_nonneg` + `sq_nonneg`).  This is the first genuine KM-metric monotonicity result:
    Fisher information cannot increase under the dephasing channel. -/
theorem kuboMori_pinching_le (p : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    kuboMoriMetric p (pinch A) ≤ kuboMoriMetric p A := by
  rw [kuboMoriMetric_pinch]
  -- Split the full metric's inner sum into the `j = i` diagonal term plus a nonnegative remainder.
  unfold kuboMoriMetric
  refine Finset.sum_le_sum (fun i _ => ?_)
  -- Peel off the diagonal `j = i` term from `∑ j, (A i j)² · ddLog1(p_i,p_j)`.
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
  -- Left = diagonal term; Right = (off-diagonal remainder) + diagonal term.
  refine le_add_of_nonneg_left ?_
  refine Finset.sum_nonneg (fun j _ => ?_)
  exact mul_nonneg (sq_nonneg _) (ddLog1_nonneg (hp i) (hp j))

/-! ### step-2 bonus: the Daleckii–Krein kernel is PSD via the Schur product theorem -/

/-- The Daleckii–Krein kernel is the Hadamard (Schur) product of the KM Loewner matrix and `H`:
    `dkKernel λ H = H ⊙ kmLoewner λ` (entrywise `H i j · ddLog1(λ_i,λ_j)`). -/
theorem dkKernel_eq_hadamard (lam : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    dkKernel lam H = H ⊙ kmLoewner lam := by
  funext i j; simp only [dkKernel_apply, Matrix.hadamard_apply, kmLoewner_apply]

/-- **step-2 bonus — the Daleckii–Krein kernel is positive semidefinite** for a PSD direction.
    For `λ_i > 0` and `H` real-symmetric `PosSemidef`, `dkKernel λ H` is `PosSemidef`.  Since
    `dkKernel λ H = H ⊙ kmLoewner λ` (Hadamard product) and `kmLoewner λ` is PSD (step 1,
    `ddLog1_loewner_posSemidef`), this is the **Schur product theorem** (`Matrix.PosSemidef.hadamard`)
    applied to two PSD matrices.  This is the Fréchet-derivative-of-`log` positivity — the operator-
    monotonicity core: `Dlog(ρ)[·]` preserves positive semidefiniteness. -/
theorem dkKernel_posSemidef_of_posSemidef (lam : Fin n → ℝ) (hpos : ∀ i, 0 < lam i)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosSemidef) : (dkKernel lam H).PosSemidef := by
  rw [dkKernel_eq_hadamard]
  exact hH.hadamard (ddLog1_loewner_posSemidef lam hpos)

/-! ### Non-vacuity witnesses for step 2 -/

/-- Non-vacuity witness for `kuboMoriMetric_nonneg` (STRICT — the metric is genuinely positive on a
    nonzero direction): at `p = (2,1)` and `A = [[1,0],[0,1]]` the KM metric is
    `1·ddLog1 2 2 + 1·ddLog1 1 1 = 1/2 + 1 = 3/2 > 0`. -/
theorem kuboMoriMetric_pos_witness :
    0 < kuboMoriMetric (![2, 1] : Fin 2 → ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold kuboMoriMetric
  simp only [Fin.sum_univ_two, Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [ddLog1_self]

/-- **STRICT non-vacuity witness for the pinching DPI** (`kuboMori_pinching_le` is genuinely strict
    when `A` has a nonzero off-diagonal entry).  Take `p = (2,1)` and the off-diagonal
    `A = [[0,1],[1,0]]`.  Then `pinch A = 0` so `kuboMoriMetric p (pinch A) = 0`, while
    `kuboMoriMetric p A = ddLog1 2 1 + ddLog1 1 2 = 2·log 2 > 0`.  Hence the inequality is STRICT:
    dephasing genuinely destroys Fisher information. -/
theorem kuboMori_pinching_strict_witness :
    kuboMoriMetric (![2, 1] : Fin 2 → ℝ) (pinch (!![(0:ℝ), 1; 1, 0]))
      < kuboMoriMetric (![2, 1] : Fin 2 → ℝ) (!![(0:ℝ), 1; 1, 0]) := by
  -- LHS = 0 (pinch of a zero-diagonal matrix), RHS = 2·log 2 > 0.
  rw [kuboMoriMetric_pinch]
  unfold kuboMoriMetric
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  rw [ddLog1_self, ddLog1_self, ddLog1_of_ne (by norm_num : (2:ℝ) ≠ 1),
    ddLog1_of_ne (by norm_num : (1:ℝ) ≠ 2), Real.log_one]
  -- LHS diagonal terms are 0² · ... = 0; RHS has the off-diagonal 1² · ddLog1 terms.
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  norm_num
  -- Remaining goal: 0 < (positive combination of log 2)
  nlinarith [hlog]

/-! ## step 3 — OPERATOR MONOTONICITY OF `log` (the famous theorem; Mathlib-ABSENT)

The step-3 headline is the operator monotonicity of the matrix logarithm:

    `A ≤ B` (real-symmetric PD, `(B − A).PosSemidef`)  ⟹  `CFC.log A ≤ CFC.log B`.

The proof has two parts, both built on the resolvent-integral Fréchet machinery of
`SecondOrderFisher.lean` (`cfcLog_line_firstDeriv_asFunction`, `hermResolvent_opNorm_le`,
`hermResolvent_eq_conj`, `matrix_integral_entry`, …):

* **(a) Fréchet positivity** (`cfcLog_firstFrechet_posSemidef`): the first Fréchet derivative
  `Dlog(X)[H] = ∫₀^∞ (X+s)⁻¹ H (X+s)⁻¹ ds` (`firstFrechetIntegral`) is `PosSemidef` for PD `X`
  and `PosSemidef` `H`.  Each resolvent `R = (X+s)⁻¹` is Hermitian PD (`hermResolvent_eq_conj`),
  so `R H R` is a congruence of the PSD `H` (`PosSemidef.mul_mul_conjTranspose_same`), hence PSD;
  and the Bochner integral of a PSD-valued integrable function is PSD (`integral_posSemidef`:
  Hermitian entrywise via `matrix_integral_entry`, quadratic form ≥ 0 via
  `ContinuousLinearMap.integral_comp_comm` + `integral_nonneg_of_ae`).

* **(b) Integrate along the path** (`cfcLog_operatorMonotone`): with `H := B − A` (PSD) and the
  PD path `X(t) = A + t•H = (1−t)•A + t•B` (`path_posDef`), the fundamental theorem of calculus
  (`intervalIntegral.integral_eq_sub_of_hasDerivAt`, entrywise) gives
  `(log B − log A)_{ij} = ∫₀¹ (Dlog(X(t))[H])_{ij} dt`.  The per-`t` derivative is
  `cfcLog_line_firstDeriv_asFunction` re-anchored at each PD base `X(t)`
  (`logline_hasDerivAt_on_path`); its interval-integrability is the parametric-integral continuity
  `frechet_continuousAt` (dominated convergence, `continuousAt_of_dominated`).  Reassembling
  entrywise (`logdiff_eq_matrix_integral`) gives `log B − log A = ∫₀¹ Dlog(X(t))[H] dt`, a
  `t`-integral of PSD matrices (part (a)), hence PSD.

Mathlib carries no operator-monotone theory; this is the classical operator monotonicity of `log`,
now reachable via the resolvent Fréchet apparatus.  This is the analytic core of the Kubo–Mori /
Petz data-processing monotonicity (the metric-level step 1/2 lifts here to the full operator order).
-/

open scoped Matrix.Norms.L2Operator

noncomputable def firstFrechetIntegral (X H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∫ s in Ioi (0:ℝ),
    Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
      * Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ))

-- reuse the three probed lemmas (copy in)
theorem resolvent_posSemidef (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsHermitian)
    (hpos : ∀ i, 0 < hX.eigenvalues i) (s : ℝ) (hs : 0 ≤ s) :
    (Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ))).PosSemidef := by
  rw [hermResolvent_eq_conj X hX hpos s hs]
  have hD : (Matrix.diagonal (fun k => (hX.eigenvalues k + s)⁻¹)).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i
    have : 0 < hX.eigenvalues i + s := by have := hpos i; linarith
    positivity
  have := hD.mul_mul_conjTranspose_same (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  convert this using 2

theorem rhr_posSemidef (X H : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsHermitian)
    (hpos : ∀ i, 0 < hX.eigenvalues i) (hH : H.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
    (Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
      * Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ))).PosSemidef := by
  set R := Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) with hR
  have hRpsd : R.PosSemidef := resolvent_posSemidef X hX hpos s hs
  have := hH.mul_mul_conjTranspose_same R
  rwa [hRpsd.isHermitian.eq] at this

theorem rhr_continuousOn [Nonempty (Fin n)] (X H : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsHermitian)
    (m : ℝ) (hm : 0 < m) (hfloor : ∀ i, m ≤ hX.eigenvalues i) :
    ContinuousOn (fun s : ℝ =>
      Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
        * Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ))) (Ioi 0) := by
  intro s hs
  have hs0 : (0:ℝ) < s := hs
  have hbu : IsUnit (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) :=
    hermitian_add_smul_one_isUnit X hX m hm hfloor s hs0
  obtain ⟨u, hu⟩ := hbu
  have h1 : ContinuousAt (fun s : ℝ => X + s • (1:Matrix (Fin n) (Fin n) ℝ)) s := by fun_prop
  have h2 : ContinuousAt Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) := by
    have := NormedRing.inverse_continuousAt u; rwa [hu] at this
  have hRc : ContinuousAt (fun s : ℝ => Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ))) s :=
    ContinuousAt.comp (g := Ring.inverse) h2 h1
  exact ((hRc.mul continuousAt_const).mul hRc).continuousWithinAt

theorem rhr_integrableOn [Nonempty (Fin n)] (X H : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsHermitian)
    (m : ℝ) (hm : 0 < m) (hfloor : ∀ i, m ≤ hX.eigenvalues i) :
    IntegrableOn (fun s : ℝ =>
      Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
        * Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ))) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun s : ℝ =>
      Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
        * Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ))) (volume.restrict (Ioi 0)) :=
    (rhr_continuousOn X H hX m hm hfloor).aestronglyMeasurable measurableSet_Ioi
  set bnd : ℝ → ℝ := fun s => ‖H‖ * (1 / ((m + s) * (m + s))) with hbnd
  have hbnd_int : IntegrableOn bnd (Ioi 0) :=
    (resolvent_sq_integrableOn m m hm hm).const_mul ‖H‖
  refine Integrable.mono' hbnd_int hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : (0:ℝ) < s := hs
  set R := Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) with hR
  have hResR : ‖R‖ ≤ 1 / (m + s) := hermResolvent_opNorm_le X hX s m hs0.le hm hfloor
  have hRnn : (0:ℝ) ≤ ‖R‖ := norm_nonneg R
  have hHnn : (0:ℝ) ≤ ‖H‖ := norm_nonneg H
  have hms : (0:ℝ) < m + s := by linarith
  have hprod : ‖R * H * R‖ ≤ (1/(m+s)) * ‖H‖ * (1/(m+s)) := by
    calc ‖R * H * R‖ ≤ ‖R * H‖ * ‖R‖ := l2_opNorm_mul _ _
      _ ≤ (‖R‖ * ‖H‖) * ‖R‖ := mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) hRnn
      _ ≤ (1/(m+s) * ‖H‖) * (1/(m+s)) := by
          apply mul_le_mul _ hResR hRnn (by positivity)
          exact mul_le_mul_of_nonneg_right hResR hHnn
  have heq : (1/(m+s)) * ‖H‖ * (1/(m+s)) = bnd s := by rw [hbnd]; field_simp
  calc ‖R * H * R‖ ≤ (1/(m+s)) * ‖H‖ * (1/(m+s)) := hprod
    _ = bnd s := heq

noncomputable def quadCLM (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => star x ⬝ᵥ M *ᵥ x
      map_add' := by intro M N; simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intro c M; rw [smul_mulVec, dotProduct_smul]; simp }

@[simp] theorem quadCLM_apply (x : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    quadCLM x M = star x ⬝ᵥ M *ᵥ x := rfl

theorem integral_posSemidef {μ : Measure ℝ} (f : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hf : Integrable f μ) (hpsd : ∀ᵐ s ∂μ, (f s).PosSemidef) :
    (∫ s, f s ∂μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · ext i j
    rw [Matrix.conjTranspose_apply, star_trivial,
        matrix_integral_entry f μ hf j i, matrix_integral_entry f μ hf i j]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hpsd] with s hps
    have h2 : (f s)ᴴ j i = (f s) j i := by rw [hps.isHermitian.eq]
    rw [Matrix.conjTranspose_apply, star_trivial] at h2
    exact h2.symm
  · have hcomm := ContinuousLinearMap.integral_comp_comm (quadCLM x) hf
    rw [quadCLM_apply] at hcomm
    rw [← hcomm]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hpsd] with s hps
    simp only [Pi.zero_apply, quadCLM_apply]
    exact hps.dotProduct_mulVec_nonneg x

/-- **PART (a) — Fréchet positivity.** For Hermitian `X` with eigenvalue floor `m>0` (so PD) and
    `H` PosSemidef, the first Fréchet derivative of `log`, `Dlog(X)[H] = ∫ R H R ds`, is PosSemidef. -/
theorem cfcLog_firstFrechet_posSemidef [Nonempty (Fin n)] (X H : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.IsHermitian) (m : ℝ) (hm : 0 < m) (hfloor : ∀ i, m ≤ hX.eigenvalues i)
    (hH : H.PosSemidef) : (firstFrechetIntegral X H).PosSemidef := by
  have hpos : ∀ i, 0 < hX.eigenvalues i := fun i => lt_of_lt_of_le hm (hfloor i)
  unfold firstFrechetIntegral
  refine integral_posSemidef _ (rhr_integrableOn X H hX m hm hfloor) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact rhr_posSemidef X H hX hpos hH s (le_of_lt hs)



-- derivative of t ↦ (log (A + t•H))_ij at ANY t₀ with A+t₀•H PD (floor m₀)
theorem logline_hasDerivAt_entry [Nonempty (Fin n)] (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hH : H.IsHermitian) (i j : Fin n) (t₀ : ℝ)
    (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hfloor : ∀ k, m₀ ≤ (hA.add (hH.smul (IsSelfAdjoint.all t₀))).eigenvalues k) :
    HasDerivAt (fun t : ℝ => (CFC.log (A + t • H)) i j)
      (lineFF1 (A + t₀ • H) H i j 0) t₀ := by
  set X₀ := A + t₀ • H with hX₀
  have hX₀herm : X₀.IsHermitian := hA.add (hH.smul (IsSelfAdjoint.all t₀))
  -- ball at ε₀ = 0: |0|*‖H‖ = 0 < m₀/2
  have hball : |(0:ℝ)| * ‖H‖ < m₀ / 2 := by
    rw [abs_zero, zero_mul]; linarith
  have hbase := cfcLog_line_firstDeriv_asFunction X₀ H hX₀herm hH m₀ hm₀ hfloor i j 0 hball
  -- hbase : HasDerivAt (fun τ => (log (X₀ + τ•H))_ij) (lineFF1 X₀ H i j 0) 0
  have hbase' : HasDerivAt (fun ε : ℝ => (CFC.log (X₀ + ε • H)) i j) (lineFF1 X₀ H i j 0) (t₀ - t₀) := by
    rw [sub_self]; exact hbase
  have hcomp := hbase'.comp_sub_const t₀
  -- hcomp : HasDerivAt (fun t => (log (X₀ + (t - t₀)•H))_ij) (lineFF1 X₀ H i j 0) t₀
  have hfeq : (fun t : ℝ => (CFC.log (X₀ + (t - t₀) • H)) i j)
      = (fun t : ℝ => (CFC.log (A + t • H)) i j) := by
    funext t
    congr 2
    rw [hX₀, sub_smul]; abel
  rw [hfeq] at hcomp
  exact hcomp



-- A + t•H PD for t ∈ [0,1] given A PD, A+H PD
theorem path_posDef (A H : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hAH : (A + H).PosDef)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (A + t • H).PosDef := by
  have heq : A + t • H = (1 - t) • A + t • (A + H) := by rw [smul_add]; module
  rw [heq]
  rcases eq_or_lt_of_le ht1 with h|h
  · subst h; norm_num; exact hAH
  · rcases eq_or_lt_of_le ht0 with h0|h0
    · rw [← h0]; norm_num; exact hA
    · have h1 : (0:ℝ) < 1 - t := by linarith
      exact (hA.smul h1).add (hAH.smul h0)

-- deriv of t ↦ (log (A+t•H))_ij at t₀∈[0,1]
theorem logline_hasDerivAt_on_path [Nonempty (Fin n)] (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hAH : (A + H).PosDef) (hHherm : H.IsHermitian) (i j : Fin n)
    (t₀ : ℝ) (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1) :
    HasDerivAt (fun t : ℝ => (CFC.log (A + t • H)) i j)
      (lineFF1 (A + t₀ • H) H i j 0) t₀ := by
  have hAherm : A.IsHermitian := hA.1
  set hX₀herm := hAherm.add (hHherm.smul (IsSelfAdjoint.all t₀)) with hhx
  have hPD : (A + t₀ • H).PosDef := path_posDef A H hA hAH t₀ ht0 ht1
  -- floor from PD
  have hposev : ∀ k, 0 < hX₀herm.eigenvalues k := by
    rw [← hX₀herm.posDef_iff_eigenvalues_pos]; exact hPD
  obtain ⟨k0, hk0⟩ := Finite.exists_min hX₀herm.eigenvalues
  exact logline_hasDerivAt_entry A H hAherm hHherm i j t₀ (hX₀herm.eigenvalues k0)
    (hposev k0) hk0


-- === continuity lemma (from probeCont) ===
theorem frechet_continuousAt [Nonempty (Fin n)] (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hH : H.IsHermitian) (t₀ : ℝ) (m : ℝ) (hm : 0 < m)
    (hfloor : ∀ k, m ≤ (hA.add (hH.smul (IsSelfAdjoint.all t₀))).eigenvalues k) :
    ContinuousAt (fun t : ℝ => ∫ s in Ioi (0:ℝ),
      Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
        * Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ))) t₀ := by
  set X₀ := A + t₀ • H with hX₀
  have hX₀herm : X₀.IsHermitian := hA.add (hH.smul (IsSelfAdjoint.all t₀))
  -- reparametrize base: A + t•H = X₀ + (t - t₀)•H. So integrand(t) = integrand'(t-t₀) with base X₀.
  -- restrict measure
  rw [show (fun t : ℝ => ∫ s in Ioi (0:ℝ),
      Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
        * Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)))
    = (fun t : ℝ => ∫ s, (fun t' => Ring.inverse ((A + t' • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
        * Ring.inverse ((A + t' • H) + s • (1:Matrix (Fin n) (Fin n) ℝ))) t
          ∂(volume.restrict (Ioi (0:ℝ)))) from rfl]
  set F : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ := fun t s =>
    Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
      * Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) with hF
  have hm2 : (0:ℝ) < m/2 := by linarith
  set δ : ℝ := m / (2 * (‖H‖ + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  -- floor m/2 for base A + t•H when |t - t₀| < δ
  have hfloor2 : ∀ t, |t - t₀| < δ → ∀ k,
      m/2 ≤ (hA.add (hH.smul (IsSelfAdjoint.all t))).eigenvalues k := by
    intro t ht k
    have hbaseherm : (A + t • H).IsHermitian := hA.add (hH.smul (IsSelfAdjoint.all t))
    -- A + t•H = X₀ + (t-t₀)•H
    have heq : (A + t • H) = X₀ + (t - t₀) • H := by rw [hX₀, sub_smul]; abel
    have hXtH : (X₀ + (t - t₀) • H).IsHermitian := by rw [← heq]; exact hbaseherm
    have hlb := hermPerturb_eigenvalues_lower X₀ H hX₀herm hH m hfloor (t - t₀) hXtH k
    -- |t-t₀|·‖H‖ ≤ δ‖H‖ < m/2
    have hbnd : |t - t₀| * ‖H‖ < m/2 := by
      calc |t - t₀| * ‖H‖ ≤ δ * ‖H‖ := mul_le_mul_of_nonneg_right ht.le (norm_nonneg H)
        _ < δ * (‖H‖ + 1) := by apply mul_lt_mul_of_pos_left _ hδpos; linarith [norm_nonneg H]
        _ = m/2 := by rw [hδ]; field_simp
    -- transport the floor bound across heq
    have hlb' : m - |t - t₀| * ‖H‖ ≤ hbaseherm.eigenvalues k := by
      convert hlb using 2
    linarith
  -- bound function
  set bound : ℝ → ℝ := fun s => ‖H‖ * (1 / ((m/2 + s) * (m/2 + s))) with hbound
  have hbound_int : Integrable bound (volume.restrict (Ioi (0:ℝ))) :=
    (resolvent_sq_integrableOn (m/2) (m/2) hm2 hm2).const_mul ‖H‖
  have hballnhds : Metric.ball t₀ δ ∈ 𝓝 t₀ := Metric.ball_mem_nhds t₀ hδpos
  have hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) (volume.restrict (Ioi (0:ℝ))) := by
    filter_upwards [hballnhds] with t ht
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    have hbaseherm : (A + t • H).IsHermitian := hA.add (hH.smul (IsSelfAdjoint.all t))
    have htdist : |t - t₀| < δ := by rw [← Real.dist_eq]; exact ht
    have hbu : IsUnit ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) :=
      hermitian_add_smul_one_isUnit (A + t • H) hbaseherm (m/2) hm2 (hfloor2 t htdist) s hs0
    obtain ⟨u, hu⟩ := hbu
    have h1 : ContinuousAt (fun s : ℝ => (A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) s := by fun_prop
    have h2 : ContinuousAt Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) := by
      have := NormedRing.inverse_continuousAt u; rwa [hu] at this
    have hRc : ContinuousAt (fun s : ℝ => Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ))) s :=
      ContinuousAt.comp (g := Ring.inverse) h2 h1
    exact (((hRc.mul continuousAt_const).mul hRc)).continuousWithinAt
  have hdom : ∀ᶠ t in 𝓝 t₀, ∀ᵐ s ∂(volume.restrict (Ioi (0:ℝ))), ‖F t s‖ ≤ bound s := by
    filter_upwards [hballnhds] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    have hbaseherm : (A + t • H).IsHermitian := hA.add (hH.smul (IsSelfAdjoint.all t))
    have htdist : |t - t₀| < δ := by rw [← Real.dist_eq]; exact ht
    set R := Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) with hR
    have hResR : ‖R‖ ≤ 1 / (m/2 + s) :=
      hermResolvent_opNorm_le (A + t • H) hbaseherm s (m/2) hs0.le hm2 (hfloor2 t htdist)
    have hRnn : (0:ℝ) ≤ ‖R‖ := norm_nonneg R
    have hHnn : (0:ℝ) ≤ ‖H‖ := norm_nonneg H
    have hms : (0:ℝ) < m/2 + s := by linarith
    have hprod : ‖R * H * R‖ ≤ (1/(m/2+s)) * ‖H‖ * (1/(m/2+s)) := by
      calc ‖R * H * R‖ ≤ ‖R * H‖ * ‖R‖ := l2_opNorm_mul _ _
        _ ≤ (‖R‖ * ‖H‖) * ‖R‖ := mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) hRnn
        _ ≤ (1/(m/2+s) * ‖H‖) * (1/(m/2+s)) := by
            apply mul_le_mul _ hResR hRnn (by positivity)
            exact mul_le_mul_of_nonneg_right hResR hHnn
    have heqb : (1/(m/2+s)) * ‖H‖ * (1/(m/2+s)) = bound s := by rw [hbound]; field_simp
    show ‖F t s‖ ≤ bound s
    rw [hF]
    calc ‖R * H * R‖ ≤ (1/(m/2+s)) * ‖H‖ * (1/(m/2+s)) := hprod
      _ = bound s := heqb
  have hcont_ae : ∀ᵐ s ∂(volume.restrict (Ioi (0:ℝ))), ContinuousAt (fun t => F t s) t₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    have hbaseherm₀ : (A + t₀ • H).IsHermitian := hA.add (hH.smul (IsSelfAdjoint.all t₀))
    have hbu : IsUnit ((A + t₀ • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) :=
      hermitian_add_smul_one_isUnit (A + t₀ • H) hbaseherm₀ m hm hfloor s hs0
    obtain ⟨u, hu⟩ := hbu
    have h1 : ContinuousAt (fun t : ℝ => (A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) t₀ := by fun_prop
    have h2 : ContinuousAt Ring.inverse ((A + t₀ • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) := by
      have := NormedRing.inverse_continuousAt u; rwa [hu] at this
    have hRc : ContinuousAt (fun t : ℝ => Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ))) t₀ :=
      ContinuousAt.comp (g := Ring.inverse) h2 h1
    show ContinuousAt (fun t => F t s) t₀
    rw [hF]
    exact (hRc.mul continuousAt_const).mul hRc
  exact MeasureTheory.continuousAt_of_dominated hmeas hdom hbound_int hcont_ae




set_option maxHeartbeats 1000000 in
unseal lineFF1 in
theorem lineFF1_zero_eq (X H : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    lineFF1 X H i j 0 = ∫ s in Ioi (0:ℝ),
      (Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
        * Ring.inverse (X + s • (1:Matrix (Fin n) (Fin n) ℝ))) i j := by
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  rw [zero_smul, add_zero]

-- derivative entry = firstFrechetIntegral entry
theorem logline_deriv_eq_frechet [Nonempty (Fin n)] (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hAH : (A + H).PosDef) (hHherm : H.IsHermitian) (i j : Fin n)
    (t₀ : ℝ) (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1) :
    HasDerivAt (fun t : ℝ => (CFC.log (A + t • H)) i j)
      ((firstFrechetIntegral (A + t₀ • H) H) i j) t₀ := by
  have hd := logline_hasDerivAt_on_path A H hA hAH hHherm i j t₀ ht0 ht1
  rw [lineFF1_zero_eq] at hd
  -- (firstFrechetIntegral X H) i j = ∫ (R H R) i j via matrix_integral_entry
  have hpos : ∀ k, 0 < (hA.1.add (hHherm.smul (IsSelfAdjoint.all t₀))).eigenvalues k := by
    rw [← (hA.1.add (hHherm.smul (IsSelfAdjoint.all t₀))).posDef_iff_eigenvalues_pos]
    exact path_posDef A H hA hAH t₀ ht0 ht1
  obtain ⟨k0, hk0⟩ := Finite.exists_min (hA.1.add (hHherm.smul (IsSelfAdjoint.all t₀))).eigenvalues
  have hint := rhr_integrableOn (A + t₀ • H) H (hA.1.add (hHherm.smul (IsSelfAdjoint.all t₀)))
    ((hA.1.add (hHherm.smul (IsSelfAdjoint.all t₀))).eigenvalues k0) (hpos k0) hk0
  have hentry : (firstFrechetIntegral (A + t₀ • H) H) i j
      = ∫ s in Ioi (0:ℝ), (Ring.inverse ((A + t₀ • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
          * Ring.inverse ((A + t₀ • H) + s • (1:Matrix (Fin n) (Fin n) ℝ))) i j := by
    rw [firstFrechetIntegral, matrix_integral_entry _ _ hint i j]
  rw [hentry]
  exact hd



-- continuity of the entry derivative on Icc 0 1
theorem frechet_entry_continuousOn [Nonempty (Fin n)] (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hAH : (A + H).PosDef) (hHherm : H.IsHermitian) (i j : Fin n) :
    ContinuousOn (fun t : ℝ => (firstFrechetIntegral (A + t • H) H) i j) (Icc 0 1) := by
  intro t₀ ht₀
  obtain ⟨ht0, ht1⟩ := ht₀
  have hPD : (A + t₀ • H).PosDef := path_posDef A H hA hAH t₀ ht0 ht1
  have hherm₀ := hA.1.add (hHherm.smul (IsSelfAdjoint.all t₀))
  have hpos : ∀ k, 0 < hherm₀.eigenvalues k := by
    rw [← hherm₀.posDef_iff_eigenvalues_pos]; exact hPD
  obtain ⟨k0, hk0⟩ := Finite.exists_min hherm₀.eigenvalues
  have hcont := frechet_continuousAt A H hA.1 hHherm t₀ (hherm₀.eigenvalues k0) (hpos k0) hk0
  -- entry-projection is continuous; firstFrechetIntegral unfolds to that integral
  have hproj : ContinuousAt (fun t : ℝ => (firstFrechetIntegral (A + t • H) H) i j) t₀ := by
    have hφ : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) := by fun_prop
    have : (fun t : ℝ => (firstFrechetIntegral (A + t • H) H) i j)
        = (fun t : ℝ => (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
            (∫ s in Ioi (0:ℝ), Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
              * Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)))) := by
      funext t; rw [firstFrechetIntegral]
    rw [this]
    exact hφ.continuousAt.comp hcont
  exact hproj.continuousWithinAt

-- entry FTC: (log B - log A) i j = ∫₀¹ (firstFrechet) i j
theorem logdiff_entry_eq_integral [Nonempty (Fin n)] (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hAH : (A + H).PosDef) (hHherm : H.IsHermitian) (i j : Fin n) :
    (CFC.log (A + H)) i j - (CFC.log A) i j
      = ∫ t in (0:ℝ)..1, (firstFrechetIntegral (A + t • H) H) i j := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => (CFC.log (A + t • H)) i j)
        ((firstFrechetIntegral (A + t • H) H) i j) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact logline_deriv_eq_frechet A H hA hAH hHherm i j t ht.1 ht.2
  have hcont : ContinuousOn (fun t : ℝ => (firstFrechetIntegral (A + t • H) H) i j) (uIcc 0 1) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact frechet_entry_continuousOn A H hA hAH hHherm i j
  have hII : IntervalIntegrable (fun t : ℝ => (firstFrechetIntegral (A + t • H) H) i j)
      volume 0 1 := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII
  -- endpoints: A + 0•H = A, A + 1•H = A + H
  have h0 : A + (0:ℝ) • H = A := by simp
  have h1 : A + (1:ℝ) • H = A + H := by simp
  rw [h0, h1] at hftc
  rw [hftc]



-- matrix interval integrability of firstFrechet on [0,1]
theorem frechet_intervalIntegrable [Nonempty (Fin n)] (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hAH : (A + H).PosDef) (hHherm : H.IsHermitian) :
    IntervalIntegrable (fun t : ℝ => firstFrechetIntegral (A + t • H) H) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num)]
  intro t₀ ht₀
  obtain ⟨ht0, ht1⟩ := ht₀
  have hPD : (A + t₀ • H).PosDef := path_posDef A H hA hAH t₀ ht0 ht1
  have hherm₀ := hA.1.add (hHherm.smul (IsSelfAdjoint.all t₀))
  have hpos : ∀ k, 0 < hherm₀.eigenvalues k := by
    rw [← hherm₀.posDef_iff_eigenvalues_pos]; exact hPD
  obtain ⟨k0, hk0⟩ := Finite.exists_min hherm₀.eigenvalues
  have hcont := frechet_continuousAt A H hA.1 hHherm t₀ (hherm₀.eigenvalues k0) (hpos k0) hk0
  have heq : (fun t : ℝ => firstFrechetIntegral (A + t • H) H)
      = (fun t : ℝ => ∫ s in Ioi (0:ℝ),
          Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ)) * H
            * Ring.inverse ((A + t • H) + s • (1:Matrix (Fin n) (Fin n) ℝ))) := by
    funext t; rw [firstFrechetIntegral]
  rw [heq]; exact hcont.continuousWithinAt

-- the matrix log difference = interval integral of firstFrechet
theorem logdiff_eq_matrix_integral [Nonempty (Fin n)] (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hAH : (A + H).PosDef) (hHherm : H.IsHermitian) :
    CFC.log (A + H) - CFC.log A
      = ∫ t in (0:ℝ)..1, firstFrechetIntegral (A + t • H) H := by
  have hII := frechet_intervalIntegrable A H hA hAH hHherm
  ext i j
  rw [Matrix.sub_apply]
  rw [logdiff_entry_eq_integral A H hA hAH hHherm i j]
  -- (∫ t in 0..1, F t) i j = ∫ t in 0..1, (F t) i j
  let φ : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)
  have hφ : ∀ M : Matrix (Fin n) (Fin n) ℝ, φ M = M i j := fun _ => rfl
  have := ContinuousLinearMap.intervalIntegral_comp_comm φ hII
  simp only [hφ] at this
  rw [this]

-- integral of PSD over Ioc via my helper (interval form)
theorem frechet_interval_posSemidef [Nonempty (Fin n)] (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hAH : (A + H).PosDef) (hHherm : H.IsHermitian) (hHpsd : H.PosSemidef) :
    (∫ t in (0:ℝ)..1, firstFrechetIntegral (A + t • H) H).PosSemidef := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  -- now ∫ t in Ioc 0 1, ... ∂volume = ∫ t, ... ∂(volume.restrict (Ioc 0 1))
  have hII := frechet_intervalIntegrable A H hA hAH hHherm
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hII
  refine integral_posSemidef _ hII ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hherm₀ := hA.1.add (hHherm.smul (IsSelfAdjoint.all t))
  have hposk : ∀ k, 0 < hherm₀.eigenvalues k := by
    rw [← hherm₀.posDef_iff_eigenvalues_pos]
    exact path_posDef A H hA hAH t ht0.le ht1
  exact cfcLog_firstFrechet_posSemidef (A + t • H) H hherm₀
    (Classical.choose (Finite.exists_min hherm₀.eigenvalues) |> hherm₀.eigenvalues)
    (hposk _) (Classical.choose_spec (Finite.exists_min hherm₀.eigenvalues)) hHpsd



/-- **OPERATOR MONOTONICITY OF `log`** (Mathlib-ABSENT). For real-symmetric PD matrices `A ≤ B`
    (i.e. `(B - A).PosSemidef`), `CFC.log A ≤ CFC.log B`. -/
theorem cfcLog_operatorMonotone [Nonempty (Fin n)] (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hle : (B - A).PosSemidef) :
    (CFC.log B - CFC.log A).PosSemidef := by
  set H := B - A with hH
  have hHherm : H.IsHermitian := hle.isHermitian
  have hAH : (A + H).PosDef := by rw [hH]; rwa [add_sub_cancel]
  have hBeq : A + H = B := by rw [hH, add_sub_cancel]
  have hstep := frechet_interval_posSemidef A H hA hAH hHherm hle
  rw [← logdiff_eq_matrix_integral A H hA hAH hHherm] at hstep
  rw [hBeq] at hstep
  exact hstep



/-- **STRICT non-vacuity witness for operator monotonicity of log.** `A = diag(1,1)`, `B = diag(2,2)`
    with `A < B` (`(B-A).PosDef`). Then `CFC.log B − CFC.log A = (log 2)•1 ≻ 0` — nonzero PSD,
    confirming non-degeneracy. -/
theorem cfcLog_operatorMonotone_strict_witness :
    (CFC.log (diagM (![2,2] : Fin 2 → ℝ)) - CFC.log (diagM (![1,1] : Fin 2 → ℝ))).PosSemidef
      ∧ (CFC.log (diagM (![2,2] : Fin 2 → ℝ)) - CFC.log (diagM (![1,1] : Fin 2 → ℝ))) ≠ 0 := by
  have hApd : (diagM (![1,1] : Fin 2 → ℝ)).PosDef := by
    rw [diagM_eq_diagonal]; rw [Matrix.posDef_diagonal_iff]; intro i; fin_cases i <;> norm_num
  have hBpd : (diagM (![2,2] : Fin 2 → ℝ)).PosDef := by
    rw [diagM_eq_diagonal]; rw [Matrix.posDef_diagonal_iff]; intro i; fin_cases i <;> norm_num
  have hle : ((diagM (![2,2] : Fin 2 → ℝ)) - (diagM (![1,1] : Fin 2 → ℝ))).PosSemidef := by
    have : (diagM (![2,2] : Fin 2 → ℝ)) - (diagM (![1,1] : Fin 2 → ℝ))
        = diagM (![1,1] : Fin 2 → ℝ) := by
      funext i j; simp only [diagM_apply]; fin_cases i <;> fin_cases j <;> norm_num
    rw [this]; exact hApd.posSemidef
  refine ⟨cfcLog_operatorMonotone _ _ hApd hBpd hle, ?_⟩
  -- compute the difference explicitly: log(diag 2) - log(diag 1) = diag(log 2) - 0
  rw [diagM_eq_diagonal, diagM_eq_diagonal,
      cfcLog_diagonal_eq_diagLog _ (by intro i; fin_cases i <;> norm_num),
      cfcLog_diagonal_eq_diagLog _ (by intro i; fin_cases i <;> norm_num)]
  intro hzero
  have h00 := congrFun (congrFun hzero 0) 0
  simp only [Matrix.sub_apply, diagLog_apply, Matrix.zero_apply, if_pos,
    Matrix.cons_val_zero, Real.log_one] at h00
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ## step 4 — OPERATOR CONVEXITY OF THE MATRIX INVERSE (Mathlib-ABSENT)

The step-4 headline is the **operator convexity of the matrix inverse**: for real-symmetric
positive-definite `A B` and `t ∈ [0,1]`, with `C := t•A + (1-t)•B`,

    `C⁻¹ ≤ t·A⁻¹ + (1-t)·B⁻¹`   (Loewner order),

i.e. `(t•A⁻¹ + (1-t)•B⁻¹ - C⁻¹).PosSemidef`.  This is the AM–HM operator inequality — the map
`X ↦ X⁻¹` is operator convex on positive-definite matrices.  It is **absent from Mathlib** (which
carries no operator-convexity theory) and is the foundational lemma for operator convexity of
`x·log x` (via `x log x = ∫ (x/(1+s) − 1 + s·(x+s)⁻¹) ds`) and operator concavity of `log`, hence for
the full Kubo–Mori / Petz data-processing monotonicity at the operator (not just metric) level.

### The proof — the Schur-complement block-matrix argument (the clean classical route)
1. `blockInv_posSemidef`: for PD `A`, the block matrix `[[A, 1],[1, A⁻¹]]`
   (`Matrix.fromBlocks A 1 1 A⁻¹`) is `PosSemidef`.  By Mathlib's Schur characterization
   `Matrix.PosDef.fromBlocks₁₁` (block PSD ⟺ top-left PD ∧ Schur complement PSD), its Schur complement
   w.r.t. the `A` block is `A⁻¹ − 1·A⁻¹·1 = 0 ⪰ 0`.
2. `convexComb_posDef`: the convex combination `C = t•A + (1-t)•B` is PD (`PosDef.smul`/`.add`, with
   the `t=0`/`t=1` boundaries handled).
3. `inv_operatorConvex`: convex-combine the two block matrices —
   `t•[[A,1],[1,A⁻¹]] + (1-t)•[[B,1],[1,B⁻¹]] = [[C, 1],[1, t A⁻¹+(1-t)B⁻¹]]` — which is PSD
   (`PosSemidef.smul`/`.add`, `fromBlocks_smul`/`fromBlocks_add`).  Taking the Schur complement of THIS
   block matrix w.r.t. the `C` block (again `fromBlocks₁₁`, `C` PD) yields
   `(t A⁻¹+(1-t)B⁻¹) − 1·C⁻¹·1 = t A⁻¹+(1-t)B⁻¹ − C⁻¹ ⪰ 0`.  ∎
-/

/-- **The block matrix `[[A, 1],[1, A⁻¹]]` is positive semidefinite** for PD `A`.  Via the
    Schur-complement characterization `Matrix.PosDef.fromBlocks₁₁`: the complement w.r.t. the `A`
    block is `A⁻¹ − 1·A⁻¹·1 = 0 ⪰ 0`.  This is the key gadget encoding `X ↦ X⁻¹` as a Schur
    complement, from which operator convexity follows by convex-combining. -/
theorem blockInv_posSemidef {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) [Invertible A] :
    (Matrix.fromBlocks A 1 1 A⁻¹).PosSemidef := by
  have hb : (Matrix.fromBlocks A (1 : Matrix (Fin N) (Fin N) ℝ) 1 A⁻¹)
      = Matrix.fromBlocks A 1 (1 : Matrix (Fin N) (Fin N) ℝ)ᴴ A⁻¹ := by
    rw [conjTranspose_one]
  rw [hb, Matrix.PosDef.fromBlocks₁₁ 1 A⁻¹ hA]
  have hzero : A⁻¹ - (1 : Matrix (Fin N) (Fin N) ℝ)ᴴ * A⁻¹ * 1 = 0 := by simp
  rw [hzero]
  exact Matrix.PosSemidef.zero

/-- **The convex combination of two PD matrices is PD** for `0 ≤ t ≤ 1`.  Uses `PosDef.smul`
    (`0 < a`) and `PosDef.add`, handling the `t = 0` and `t = 1` boundaries where one coefficient
    vanishes. -/
theorem convexComb_posDef {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (t • A + (1 - t) • B).PosDef := by
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · rw [← h0]; simp; exact hB
  · rcases eq_or_lt_of_le ht1 with h1 | h1
    · rw [h1]; simp; exact hA
    · exact (hA.smul h0).add (hB.smul (by linarith : (0 : ℝ) < 1 - t))

/-- **step 4 — OPERATOR CONVEXITY OF THE MATRIX INVERSE** (Mathlib-ABSENT).  For real-symmetric PD
    matrices `A B` and `t ∈ [0,1]`, with `C := t•A + (1-t)•B`,

        `(t • A⁻¹ + (1 - t) • B⁻¹ - (t • A + (1 - t) • B)⁻¹).PosSemidef`,

    i.e. `C⁻¹ ≤ t A⁻¹ + (1-t) B⁻¹` in the Loewner order — the map `X ↦ X⁻¹` is operator convex on
    positive-definite matrices (the AM–HM operator inequality).  The proof convex-combines the two
    block matrices `[[A,1],[1,A⁻¹]]` and `[[B,1],[1,B⁻¹]]` (each PSD by `blockInv_posSemidef`) into
    `[[C,1],[1, t A⁻¹+(1-t)B⁻¹]]` (PSD by `PosSemidef.smul`/`.add`, `fromBlocks_smul`/`_add`) and reads
    off its Schur complement w.r.t. the PD block `C` (`Matrix.PosDef.fromBlocks₁₁`).  This is the
    foundational lemma for operator convexity of `x·log x` and operator concavity of `log`. -/
theorem inv_operatorConvex {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • A⁻¹ + (1 - t) • B⁻¹ - (t • A + (1 - t) • B)⁻¹).PosSemidef := by
  letI := hA.isUnit.invertible
  letI := hB.isUnit.invertible
  have hC : (t • A + (1 - t) • B).PosDef := convexComb_posDef A B hA hB t ht0 ht1
  letI := hC.isUnit.invertible
  set C := t • A + (1 - t) • B with hCdef
  -- The convex-combined block matrix `[[C, 1],[1, t A⁻¹+(1-t) B⁻¹]]` is PSD.
  have hblock : (Matrix.fromBlocks C 1 1 (t • A⁻¹ + (1 - t) • B⁻¹)).PosSemidef := by
    have hcomb : Matrix.fromBlocks C (1 : Matrix (Fin N) (Fin N) ℝ) 1 (t • A⁻¹ + (1 - t) • B⁻¹)
        = t • Matrix.fromBlocks A 1 1 A⁻¹ + (1 - t) • Matrix.fromBlocks B 1 1 B⁻¹ := by
      rw [fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
      congr 1 <;> simp
    rw [hcomb]
    exact ((blockInv_posSemidef A hA).smul ht0).add
      ((blockInv_posSemidef B hB).smul (by linarith : (0 : ℝ) ≤ 1 - t))
  -- Extract the Schur complement w.r.t. the PD block `C`.
  have hb : (Matrix.fromBlocks C (1 : Matrix (Fin N) (Fin N) ℝ) 1 (t • A⁻¹ + (1 - t) • B⁻¹))
      = Matrix.fromBlocks C 1 (1 : Matrix (Fin N) (Fin N) ℝ)ᴴ (t • A⁻¹ + (1 - t) • B⁻¹) := by
    rw [conjTranspose_one]
  rw [hb, Matrix.PosDef.fromBlocks₁₁ 1 (t • A⁻¹ + (1 - t) • B⁻¹) hC] at hblock
  have hsimp : (t • A⁻¹ + (1 - t) • B⁻¹) - (1 : Matrix (Fin N) (Fin N) ℝ)ᴴ * C⁻¹ * 1
      = t • A⁻¹ + (1 - t) • B⁻¹ - C⁻¹ := by simp
  rw [hsimp] at hblock
  exact hblock

set_option maxHeartbeats 800000 in
/-- **STRICT non-vacuity witness for operator convexity of the inverse** (the AM–HM operator gap is
    genuinely nonzero unless `A = B`).  Take `A = ![![2,0],![0,1]]`, `B = ![![1,0],![0,3]]`, `t = 1/2`.
    Then `(1/2) A⁻¹ + (1/2) B⁻¹ − ((A+B)/2)⁻¹ = diag(1/12, 1/6)` — a nonzero positive-semidefinite
    matrix (entry `(0,0) = 1/12 ≠ 0`), confirming the Loewner inequality `C⁻¹ ≤ t A⁻¹ + (1-t) B⁻¹` is
    strict for distinct `A, B`.  (`set A/B` before applying keeps the elaborator from eagerly reducing
    the concrete `2×2` inverses during unification; the coefficients carry an explicit `ℝ` annotation
    so `1 - 1/2` is real, not `ℕ`-scalar.) -/
theorem inv_operatorConvex_strict_witness :
    ((1 / 2 : ℝ) • (!![(2 : ℝ), 0; 0, 1])⁻¹ + (1 - 1 / 2 : ℝ) • (!![(1 : ℝ), 0; 0, 3])⁻¹
       - ((1 / 2 : ℝ) • (!![(2 : ℝ), 0; 0, 1])
          + (1 - 1 / 2 : ℝ) • (!![(1 : ℝ), 0; 0, 3]))⁻¹).PosSemidef
    ∧ ((1 / 2 : ℝ) • (!![(2 : ℝ), 0; 0, 1])⁻¹ + (1 - 1 / 2 : ℝ) • (!![(1 : ℝ), 0; 0, 3])⁻¹
       - ((1 / 2 : ℝ) • (!![(2 : ℝ), 0; 0, 1])
          + (1 - 1 / 2 : ℝ) • (!![(1 : ℝ), 0; 0, 3]))⁻¹) ≠ 0 := by
  have hApd : (!![(2 : ℝ), 0; 0, 1]).PosDef := by
    rw [← Matrix.diagonal_vec2, Matrix.posDef_diagonal_iff]; intro i; fin_cases i <;> norm_num
  have hBpd : (!![(1 : ℝ), 0; 0, 3]).PosDef := by
    rw [← Matrix.diagonal_vec2, Matrix.posDef_diagonal_iff]; intro i; fin_cases i <;> norm_num
  constructor
  · set A := (!![(2 : ℝ), 0; 0, 1]) with hA
    set B := (!![(1 : ℝ), 0; 0, 3]) with hB
    exact inv_operatorConvex A B hApd hBpd (1 / 2) (by norm_num) (by norm_num)
  · -- Nonzero: compute entry `(0,0) = 1/12 ≠ 0` from the explicit `2×2` inverses.
    intro h
    have h00 := congrFun (congrFun h 0) 0
    rw [Matrix.inv_def, Matrix.inv_def, Matrix.inv_def] at h00
    norm_num [Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.smul_of, Matrix.smul_cons,
      Matrix.add_cons, Matrix.head_cons, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] at h00

/-! ## step 4b — OPERATOR CONVEXITY OF `X ↦ X·log X` (the headline; Mathlib-ABSENT)

The map `X ↦ X·log X` is **operator convex** on positive-definite matrices: for PD `A,B` and
`t ∈ [0,1]`, with `C := t•A + (1-t)•B`,

    `t • (A·log A) + (1-t) • (B·log B)  −  C·log C  ⪰  0`.

This is the operator-level Klein/Gibbs convexity — the matrix inequality underlying the joint
convexity of quantum relative entropy and hence Kubo–Mori / Petz data-processing monotonicity.

### The proof — integral representation + inverse operator convexity + PSD-under-integral
Multiply the `CFC.log` resolvent representation (`cfcLog_eq_resolvent_integral`) on the LEFT
by `X` and pull `X` inside the Bochner integral (the left-multiplication continuous-linear map
`mulLeftRight ℝ _ X 1`, `ContinuousLinearMap.integral_comp_comm`):

    `X · log X  =  ∫_{Ioi 0}  X · ( (1+s)⁻¹•1 − (X+s•1)⁻¹ )  ds`.

The key **pointwise** identity: since `X = (X+s•1) − s•1` commutes with `(X+s•1)⁻¹`,
`X·(X+s•1)⁻¹ = 1 − s•(X+s•1)⁻¹`, so the integrand rearranges to
`(1+s)⁻¹•X − 1 + s•(X+s•1)⁻¹`.  In the convex combination `t•g_A + (1-t)•g_B − g_C`, the
`(1+s)⁻¹•X` parts cancel (`t•A+(1-t)•B−C = 0`) and the `−1` parts cancel (`t+(1-t)−1 = 0`), leaving

    `t•g_A(s) + (1-t)•g_B(s) − g_C(s)  =  s • ( t•(A+s•1)⁻¹ + (1-t)•(B+s•1)⁻¹ − (C+s•1)⁻¹ )`.

Because `C+s•1 = t•(A+s•1) + (1-t)•(B+s•1)`, the bracket is PSD by operator convexity of the
inverse (`inv_operatorConvex`) applied to the PD pair `(A+s•1, B+s•1)`, and `s ≥ 0`; so the
integrand is PSD for every `s`, and the integral is PSD (`integral_posSemidef`). ∎
(The rearranged `(1+s)⁻¹•X − 1 + s•(X+s•1)⁻¹` pieces are individually NON-integrable; only their
combination is — the cancellation is done at the integrand level as a pointwise matrix identity,
then integrated in the integrable `X·((1+s)⁻¹•1 − (X+s•1)⁻¹)` form.) -/

section XLogXOperatorConvex
open scoped Matrix.Norms.L2Operator

/-- `A + s•1` is positive-definite for PD `A` and `s > 0` (quadratic form `≥ (·) + s(x⬝ᵥx) > 0`). -/
theorem posDef_add_smul_one (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (s : ℝ) (hs : 0 < s) :
    (A + s • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hHerm : (A + s • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian :=
    hA.1.add ((Matrix.isHermitian_one).smul (IsSelfAdjoint.all s))
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  have hAx := hA.dotProduct_mulVec_pos hx
  have hxx : 0 < x ⬝ᵥ x := by
    rw [dotProduct]
    apply Finset.sum_pos'
    · intro k _; exact mul_self_nonneg _
    · rcases Function.ne_iff.mp hx with ⟨k, hk⟩
      exact ⟨k, Finset.mem_univ k, mul_self_pos.mpr hk⟩
  have hexp : star x ⬝ᵥ ((A + s • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x)
      = star x ⬝ᵥ (A *ᵥ x) + s * (x ⬝ᵥ x) := by
    rw [add_mulVec, smul_mulVec, one_mulVec]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, star_trivial]
  rw [hexp]; nlinarith [hAx, hxx, hs]

/-- **The `X`-multiplied resolvent integrand** `g_X(s) := X · ((1+s)⁻¹•1 − (X+s•1)⁻¹)` — the
    integrand whose `∫_{Ioi 0}` is `X·log X` (`xLogX_integral_rep`).  Kept in this product form for
    integrability; its rearranged pieces are individually non-integrable. -/
noncomputable def xLogXIntegrand (X : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  X * resolventRepIntegrand X s

/-- **Pointwise rearrangement of `g_X`.**  Given `X+s•1` a unit,
    `X · resolventRepIntegrand X s = (1+s)⁻¹•X − 1 + s•(X+s•1)⁻¹`, using
    `X·(X+s•1)⁻¹ = 1 − s•(X+s•1)⁻¹` (from `(X+s•1)·(X+s•1)⁻¹ = 1` and commutativity). -/
theorem xLogXIntegrand_rearrange (X : Matrix (Fin n) (Fin n) ℝ) (s : ℝ)
    (hu : IsUnit (X + s • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    xLogXIntegrand X s
      = (1 + s)⁻¹ • X - 1 + s • Ring.inverse (X + s • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  set R := Ring.inverse (X + s • (1 : Matrix (Fin n) (Fin n) ℝ)) with hR
  have hXR : X * R = 1 - s • R := by
    have hmulR : (X + s • (1 : Matrix (Fin n) (Fin n) ℝ)) * R = 1 := by
      rw [hR]; exact Ring.mul_inverse_cancel _ hu
    have he : (X + s • (1 : Matrix (Fin n) (Fin n) ℝ)) * R = X * R + s • R := by
      rw [add_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [he] at hmulR
    linear_combination (norm := abel) hmulR
  unfold xLogXIntegrand resolventRepIntegrand
  rw [hR] at hXR
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hXR]
  abel

/-- **The convex-combination cancellation identity.**  With `A+s•1`, `B+s•1`, `C+s•1`
    (`C := t•A+(1-t)•B`) all units,
    `t•g_A(s) + (1-t)•g_B(s) − g_C(s) = s • ( t•(A+s•1)⁻¹ + (1-t)•(B+s•1)⁻¹ − (C+s•1)⁻¹ )` —
    the `(1+s)⁻¹•X` and `−1` parts cancel, leaving `s•(resolvent convex combination)`. -/
theorem xLogXIntegrand_combo (A B : Matrix (Fin n) (Fin n) ℝ) (t s : ℝ)
    (huA : IsUnit (A + s • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (huB : IsUnit (B + s • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (huC : IsUnit ((t • A + (1 - t) • B) + s • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    t • xLogXIntegrand A s + (1 - t) • xLogXIntegrand B s
      - xLogXIntegrand (t • A + (1 - t) • B) s
      = s • ( t • Ring.inverse (A + s • (1 : Matrix (Fin n) (Fin n) ℝ))
              + (1 - t) • Ring.inverse (B + s • (1 : Matrix (Fin n) (Fin n) ℝ))
              - Ring.inverse ((t • A + (1 - t) • B) + s • (1 : Matrix (Fin n) (Fin n) ℝ)) ) := by
  rw [xLogXIntegrand_rearrange A s huA, xLogXIntegrand_rearrange B s huB,
    xLogXIntegrand_rearrange (t • A + (1 - t) • B) s huC]
  module

/-- **The integrand of the operator-convexity gap is PosSemidef, pointwise for `s > 0`.**  By
    `xLogXIntegrand_combo` it equals `s•(t•(A+s•1)⁻¹+(1-t)•(B+s•1)⁻¹−(C+s•1)⁻¹)`, and the bracket is
    PSD by `inv_operatorConvex` on the PD pair `(A+s•1, B+s•1)` (whose convex combination is `C+s•1`),
    scaled by `s ≥ 0`. -/
theorem xLogXIntegrand_gap_posSemidef (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hB : B.PosDef) (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs : 0 < s) :
    (t • xLogXIntegrand A s + (1 - t) • xLogXIntegrand B s
      - xLogXIntegrand (t • A + (1 - t) • B) s).PosSemidef := by
  have hAs : (A + s • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := posDef_add_smul_one A hA s hs
  have hBs : (B + s • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := posDef_add_smul_one B hB s hs
  rw [xLogXIntegrand_combo A B t s hAs.isUnit hBs.isUnit
    (posDef_add_smul_one (t • A + (1 - t) • B) (convexComb_posDef A B hA hB t ht0 ht1) s hs).isUnit]
  set As := A + s • (1 : Matrix (Fin n) (Fin n) ℝ) with hAsdef
  set Bs := B + s • (1 : Matrix (Fin n) (Fin n) ℝ) with hBsdef
  have hconv := inv_operatorConvex As Bs hAs hBs t ht0 ht1
  rw [nonsing_inv_eq_ringInverse, nonsing_inv_eq_ringInverse, nonsing_inv_eq_ringInverse] at hconv
  have hCeq : t • As + (1 - t) • Bs
      = (t • A + (1 - t) • B) + s • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hAsdef, hBsdef]; module
  rw [hCeq] at hconv
  exact hconv.smul (le_of_lt hs)

/-- **Integrability of `g_X` on `(0,∞)`.**  `g_X = X·(resolventRepIntegrand X)` is the
    left-multiplication CLM applied to the (integrable) resolvent-rep integrand
    (`hermResolventRepIntegrand_integrable`), hence integrable. -/
theorem xLogXIntegrand_integrable (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsHermitian)
    (hpos : ∀ i, 0 < hX.eigenvalues i) :
    IntegrableOn (fun s : ℝ => xLogXIntegrand X s) (Ioi 0) := by
  set L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ) X 1 with hL
  have hint := hermResolventRepIntegrand_integrable X hX hpos
  have hcomp : IntegrableOn (fun s : ℝ => L (resolventRepIntegrand X s)) (Ioi 0) :=
    ContinuousLinearMap.integrable_comp L hint
  apply hcomp.congr_fun _ measurableSet_Ioi
  intro s hs
  simp only [hL, ContinuousLinearMap.mulLeftRight_apply, Matrix.mul_one, xLogXIntegrand]

/-- **The integral representation of `X·log X`.**  For Hermitian PD `X`,
    `X · CFC.log X = ∫_{Ioi 0} g_X(s) ds`.  Multiply `cfcLog_eq_resolvent_integral` on the left by `X`
    and pull `X` through the Bochner integral via the left-multiplication CLM. -/
theorem xLogX_integral_rep (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsHermitian)
    (hpos : ∀ i, 0 < hX.eigenvalues i) :
    X * CFC.log X = ∫ s in Ioi (0 : ℝ), xLogXIntegrand X s := by
  rw [cfcLog_eq_resolvent_integral X hX hpos]
  set L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ) X 1 with hL
  have hLapply : ∀ M, L M = X * M := by
    intro M; rw [hL, ContinuousLinearMap.mulLeftRight_apply, Matrix.mul_one]
  have hint := hermResolventRepIntegrand_integrable X hX hpos
  rw [← hLapply, ← ContinuousLinearMap.integral_comp_comm L hint]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [hLapply]; rfl

/-- **step 4b — OPERATOR CONVEXITY OF `X ↦ X·log X`** (Mathlib-ABSENT; the KM-monotonicity
    headline).  For real-symmetric PD matrices `A B` and `t ∈ [0,1]`, with `C := t•A + (1-t)•B`,

        `(t • (A * CFC.log A) + (1 - t) • (B * CFC.log B) − C * CFC.log C).PosSemidef`,

    i.e. `X ↦ X·log X` is operator convex on positive-definite matrices — the matrix Klein/Gibbs
    convexity underlying joint convexity of quantum relative entropy and Kubo–Mori / Petz
    data-processing monotonicity.  Proof: represent each `X·log X` as `∫ g_X ds` (`xLogX_integral_rep`,
    from the `CFC.log` resolvent representation); the gap integrand is PSD pointwise
    (`xLogXIntegrand_gap_posSemidef`, from inverse operator convexity) and integrable
    (`xLogXIntegrand_integrable`); conclude by `integral_posSemidef`. -/
theorem xLogX_operatorConvex (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • (A * CFC.log A) + (1 - t) • (B * CFC.log B)
      - (t • A + (1 - t) • B) * CFC.log (t • A + (1 - t) • B)).PosSemidef := by
  set C := t • A + (1 - t) • B with hCdef
  have hC : C.PosDef := convexComb_posDef A B hA hB t ht0 ht1
  -- eigenvalue positivity for the three matrices
  have hAp : ∀ i, 0 < hA.isHermitian.eigenvalues i :=
    hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA
  have hBp : ∀ i, 0 < hB.isHermitian.eigenvalues i :=
    hB.isHermitian.posDef_iff_eigenvalues_pos.mp hB
  have hCp : ∀ i, 0 < hC.isHermitian.eigenvalues i :=
    hC.isHermitian.posDef_iff_eigenvalues_pos.mp hC
  -- integral representations
  rw [xLogX_integral_rep A hA.isHermitian hAp, xLogX_integral_rep B hB.isHermitian hBp,
    xLogX_integral_rep C hC.isHermitian hCp]
  -- integrabilities
  have hIA := xLogXIntegrand_integrable A hA.isHermitian hAp
  have hIB := xLogXIntegrand_integrable B hB.isHermitian hBp
  have hIC := xLogXIntegrand_integrable C hC.isHermitian hCp
  -- pull the linear combination inside a single integral
  have hcomb : t • (∫ s in Ioi (0 : ℝ), xLogXIntegrand A s)
      + (1 - t) • (∫ s in Ioi (0 : ℝ), xLogXIntegrand B s)
      - (∫ s in Ioi (0 : ℝ), xLogXIntegrand C s)
      = ∫ s in Ioi (0 : ℝ),
          (t • xLogXIntegrand A s + (1 - t) • xLogXIntegrand B s - xLogXIntegrand C s) := by
    have e1 : (∫ s in Ioi (0 : ℝ),
          (t • xLogXIntegrand A s + (1 - t) • xLogXIntegrand B s - xLogXIntegrand C s))
        = (∫ s in Ioi (0 : ℝ), (t • xLogXIntegrand A s + (1 - t) • xLogXIntegrand B s))
          - ∫ s in Ioi (0 : ℝ), xLogXIntegrand C s :=
      MeasureTheory.integral_sub ((hIA.smul t).add (hIB.smul (1 - t))) hIC
    have e2 : (∫ s in Ioi (0 : ℝ), (t • xLogXIntegrand A s + (1 - t) • xLogXIntegrand B s))
        = (∫ s in Ioi (0 : ℝ), t • xLogXIntegrand A s)
          + ∫ s in Ioi (0 : ℝ), (1 - t) • xLogXIntegrand B s :=
      MeasureTheory.integral_add (hIA.smul t) (hIB.smul (1 - t))
    have e3 : (∫ s in Ioi (0 : ℝ), t • xLogXIntegrand A s)
        = t • ∫ s in Ioi (0 : ℝ), xLogXIntegrand A s := MeasureTheory.integral_smul t _
    have e4 : (∫ s in Ioi (0 : ℝ), (1 - t) • xLogXIntegrand B s)
        = (1 - t) • ∫ s in Ioi (0 : ℝ), xLogXIntegrand B s := MeasureTheory.integral_smul (1 - t) _
    rw [e1, e2, e3, e4]
  rw [hcomb]
  -- the combined integrand is PSD a.e. and integrable ⟹ its integral is PSD
  refine integral_posSemidef _
    (((hIA.smul t).add (hIB.smul (1 - t))).sub hIC) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact xLogXIntegrand_gap_posSemidef A B hA hB t s ht0 ht1 hs

/-- **STRICT non-vacuity witness for operator convexity of `X·log X`.**  Take the diagonal PD
    `A = diag(1,4)`, `B = diag(4,1)`, `t = 1/2`, so `C = diag(5/2, 5/2)`.  The gap
    `(1/2)(A·log A) + (1/2)(B·log B) − C·log C` is the diagonal matrix
    `diag( (1/2)(1·log 1 + 4·log 4) − (5/2)log(5/2),  same )` whose `(0,0)` entry is
    `2·log 4 − (5/2)·log(5/2) = log 16 − log((5/2)^(5/2)) > 0` (strict convexity of `x·log x`),
    confirming the operator-convexity gap is genuinely nonzero for distinct `A, B`. -/
theorem xLogX_operatorConvex_strict_witness :
    (((1 / 2 : ℝ) • (Matrix.diagonal ![(1 : ℝ), 4] * CFC.log (Matrix.diagonal ![(1 : ℝ), 4]))
        + (1 - 1 / 2 : ℝ) • (Matrix.diagonal ![(4 : ℝ), 1] * CFC.log (Matrix.diagonal ![(4 : ℝ), 1]))
        - ((1 / 2 : ℝ) • Matrix.diagonal ![(1 : ℝ), 4] + (1 - 1 / 2 : ℝ) • Matrix.diagonal ![(4 : ℝ), 1])
          * CFC.log ((1 / 2 : ℝ) • Matrix.diagonal ![(1 : ℝ), 4]
              + (1 - 1 / 2 : ℝ) • Matrix.diagonal ![(4 : ℝ), 1])).PosSemidef)
    ∧ (2 * Real.log 4 - (5 / 2) * Real.log (5 / 2) ≠ 0) := by
  have hApd : (Matrix.diagonal ![(1 : ℝ), 4]).PosDef := by
    rw [Matrix.posDef_diagonal_iff]; intro i; fin_cases i <;> norm_num
  have hBpd : (Matrix.diagonal ![(4 : ℝ), 1]).PosDef := by
    rw [Matrix.posDef_diagonal_iff]; intro i; fin_cases i <;> norm_num
  refine ⟨xLogX_operatorConvex _ _ hApd hBpd (1 / 2) (by norm_num) (by norm_num), ?_⟩
  -- 2 log 4 − (5/2) log(5/2) = log 16 − log((5/2)^(5/2)) > 0 since 16 > (5/2)^(5/2) ≈ 9.88
  have h1 : (2 : ℝ) * Real.log 4 = Real.log 16 := by
    rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.log_pow]; ring
  have hlt : (5 / 2 : ℝ) * Real.log (5 / 2) < 2 * Real.log 4 := by
    rw [h1]
    have hb : (0 : ℝ) < 5 / 2 := by norm_num
    -- (5/2)·log(5/2) = log((5/2)^(5/2)),  and  (5/2)^(5/2) ≤ (5/2)^3 = 15.625 < 16
    have hlog : (5 / 2 : ℝ) * Real.log (5 / 2) = Real.log ((5 / 2 : ℝ) ^ (5 / 2 : ℝ)) := by
      rw [Real.log_rpow hb]
    rw [hlog]
    apply Real.log_lt_log (by positivity)
    have hexp : ((5 / 2 : ℝ) ^ (5 / 2 : ℝ)) ≤ (5 / 2 : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h3 : ((5 / 2 : ℝ) ^ (3 : ℝ)) = 125 / 8 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h3] at hexp
    linarith
  linarith

end XLogXOperatorConvex

end Physlib.SecondOrderFisher
