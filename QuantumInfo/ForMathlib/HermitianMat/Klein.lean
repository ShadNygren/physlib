/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.CFC

/-! # Klein's inequality (tangent form)

Klein's inequality bounds `Tr[f(X)]` by the tangent-line expansion of `f` around a second
matrix `Y`, with **no commutativity** assumed between `X` and `Y`: if the scalar function `f`
lies below its tangents with slope function `g` on `[0,∞) × (0,∞)`, then

`Tr[f(X)] ≤ Tr[f(Y)] + ⟪Y.cfc g, X − Y⟫`.

The proof is by double spectral decomposition: writing `X = Σᵢ xᵢ Pᵢ` and `Y = Σⱼ yⱼ Qⱼ`,
all three traces expand into `Σᵢⱼ wᵢⱼ * (scalar tangent gap)` where the transition weights
`wᵢⱼ = Tr[Pᵢ Qⱼ] = ‖⟨uᵢ, vⱼ⟩‖²` form a doubly stochastic matrix, so the scalar inequality
transfers term by term (`sum_tangent_le`).

The specialization to `f = Real.negMulLog` (in `QuantumInfo.Entropy.Relative`) gives an
elementary proof that the quantum relative entropy is nonnegative.
-/

@[expose] public section

noncomputable section

namespace HermitianMat

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]

open scoped ComplexOrder InnerProductSpace RealInnerProductSpace

/-- Row sums of the squared-norm entries of a unitary matrix are 1. -/
private lemma unitary_row_sum_sq_norm {W : Matrix d d 𝕜}
    (hW : W ∈ Matrix.unitaryGroup d 𝕜) (i : d) :
    ∑ j, ‖W i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hW) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.star_apply, RCLike.star_def, RCLike.mul_conj] at h
  exact_mod_cast h

/-- Column sums of the squared-norm entries of a unitary matrix are 1. -/
private lemma unitary_col_sum_sq_norm {W : Matrix d d 𝕜}
    (hW : W ∈ Matrix.unitaryGroup d 𝕜) (j : d) :
    ∑ i, ‖W i j‖ ^ 2 = 1 := by
  simpa using unitary_row_sum_sq_norm (Unitary.star_mem hW) j

/-- Trace of the product of two (possibly non-commuting) rank-one spectral projectors
`U Eᵢᵢ Uᴴ` and `V Eⱼⱼ Vᴴ` is the transition weight `‖(Uᴴ V) i j‖²`. -/
private lemma trace_proj_mul_proj (U V : Matrix d d 𝕜) (i j : d) :
    (U * Matrix.single i i 1 * U.conjTranspose *
      (V * Matrix.single j j 1 * V.conjTranspose)).trace
      = ((‖(U.conjTranspose * V) i j‖ ^ 2 : ℝ) : 𝕜) := by
  have h1 : U * Matrix.single i i (1 : 𝕜) * U.conjTranspose *
      (V * Matrix.single j j (1 : 𝕜) * V.conjTranspose)
      = U * (Matrix.single i i (1 : 𝕜) * (U.conjTranspose * V) *
          Matrix.single j j (1 : 𝕜)) * V.conjTranspose := by
    simp only [Matrix.mul_assoc]
  have h2 : V.conjTranspose * U = (U.conjTranspose * V).conjTranspose := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [h1, Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.trace_mul_cycle,
    Matrix.trace_mul_comm, Matrix.trace_single_mul, h2, Matrix.conjTranspose_apply,
    smul_eq_mul, RCLike.star_def, RCLike.mul_conj]
  push_cast
  ring

/-- Double spectral expansion of the Hilbert–Schmidt inner product: `⟪A.cfc f, B.cfc g⟫`
is the double sum over both spectra of `f(xᵢ) g(yⱼ)` weighted by the squared-norm
transition weights `‖(Uᴴ V) i j‖²` between the two eigenbases. -/
lemma inner_cfc_cfc (A B : HermitianMat d 𝕜) (f g : ℝ → ℝ) :
    ⟪A.cfc f, B.cfc g⟫_ℝ = ∑ i, ∑ j,
      f (A.H.eigenvalues i) * g (B.H.eigenvalues j) *
        ‖(A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val) i j‖ ^ 2 := by
  rw [inner_eq_re_trace, A.cfc_toMat_eq_sum_smul_proj f, B.cfc_toMat_eq_sum_smul_proj g,
    Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Matrix.trace_sum,
    Matrix.trace_smul, map_sum, trace_proj_mul_proj, RCLike.smul_re, RCLike.ofReal_re]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq d] in
/-- Scalar core of Klein's inequality: a pointwise tangent-line bound transfers through
a doubly stochastic weight matrix to the corresponding weighted sums. -/
private lemma sum_tangent_le (f g : ℝ → ℝ) (x y : d → ℝ) (w : d → d → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 < y j)
    (htan : ∀ a, 0 ≤ a → ∀ b, 0 < b → f a ≤ f b + g b * (a - b)) :
    ∑ i, f (x i) ≤ ∑ j, f (y j) +
      ((∑ i, ∑ j, x i * g (y j) * w i j) - ∑ j, y j * g (y j)) := by
  have h1 : ∑ i, f (x i) = ∑ i, ∑ j, f (x i) * w i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hrow i, mul_one]
  have h2 : ∑ j, f (y j) = ∑ i, ∑ j, f (y j) * w i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, hcol j, mul_one]
  have h3 : ∑ j, y j * g (y j) = ∑ i, ∑ j, y j * g (y j) * w i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, hcol j, mul_one]
  have hmain : ∑ i, ∑ j, f (x i) * w i j ≤
      ∑ i, ∑ j, (f (y j) + g (y j) * (x i - y j)) * w i j :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (htan _ (hx i) _ (hy j)) (hw i j)
  have hexp : ∑ i, ∑ j, (f (y j) + g (y j) * (x i - y j)) * w i j
      = (∑ i, ∑ j, f (y j) * w i j) +
        ((∑ i, ∑ j, x i * g (y j) * w i j) - ∑ i, ∑ j, y j * g (y j) * w i j) := by
    simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith [h1, h2, h3, hmain, hexp]

/-- **Klein's inequality**, tangent form: if the scalar function `f` lies below its
tangent lines with slope function `g`, i.e. `f x ≤ f y + g y * (x - y)` for `x ≥ 0` and
`y > 0` (as holds for any differentiable concave `f` with `g = f'`), then for any positive
semidefinite `X` and positive definite `Y`,

`Tr[f(X)] ≤ Tr[f(Y)] + ⟪Y.cfc g, X − Y⟫`,

with no commutativity assumed between `X` and `Y`. -/
theorem klein_of_tangent (f g : ℝ → ℝ) (X Y : HermitianMat d 𝕜)
    (hX : 0 ≤ X) (hY : Y.mat.PosDef)
    (htan : ∀ x, 0 ≤ x → ∀ y, 0 < y → f x ≤ f y + g y * (x - y)) :
    (X.cfc f).trace ≤ (Y.cfc f).trace + ⟪Y.cfc g, X - Y⟫_ℝ := by
  have hI1 : ⟪Y.cfc g, X⟫_ℝ = ∑ i, ∑ j,
      X.H.eigenvalues i * g (Y.H.eigenvalues j) *
        ‖(X.H.eigenvectorUnitary.val.conjTranspose * Y.H.eigenvectorUnitary.val) i j‖ ^ 2 := by
    rw [inner_comm]
    conv_lhs => rw [← X.cfc_id]
    rw [inner_cfc_cfc]
    simp only [id_eq]
  have hI2 : ⟪Y.cfc g, Y⟫_ℝ = ∑ j, Y.H.eigenvalues j * g (Y.H.eigenvalues j) := by
    rw [inner_comm, inner_eq_re_trace, trace_mul_cfc]
    simp
  have hW : X.H.eigenvectorUnitary.val.conjTranspose * Y.H.eigenvectorUnitary.val ∈
      Matrix.unitaryGroup d 𝕜 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact mul_mem (Unitary.star_mem X.H.eigenvectorUnitary.2) Y.H.eigenvectorUnitary.2
  have hkey := sum_tangent_le f g X.H.eigenvalues Y.H.eigenvalues
    (fun i j => ‖(X.H.eigenvectorUnitary.val.conjTranspose *
      Y.H.eigenvectorUnitary.val) i j‖ ^ 2)
    (fun i j => by positivity) (unitary_row_sum_sq_norm hW) (unitary_col_sum_sq_norm hW)
    (X.eigenvalues_nonneg hX) hY.eigenvalues_pos htan
  rw [HermitianMat.inner_sub_left, trace_cfc_eq, trace_cfc_eq, hI1, hI2]
  exact hkey

/-- **Klein's inequality**, convex form: if the scalar function `f` lies *above* its
tangent lines with slope function `g` (as holds for any differentiable convex `f` with
`g = f'`), the trace inequality of `klein_of_tangent` reverses:

`Tr[f(Y)] + ⟪Y.cfc g, X − Y⟫ ≤ Tr[f(X)]`. -/
lemma klein_of_tangent_convex (f g : ℝ → ℝ) (X Y : HermitianMat d 𝕜)
    (hX : 0 ≤ X) (hY : Y.mat.PosDef)
    (htan : ∀ x, 0 ≤ x → ∀ y, 0 < y → f y + g y * (x - y) ≤ f x) :
    (Y.cfc f).trace + ⟪Y.cfc g, X - Y⟫_ℝ ≤ (X.cfc f).trace := by
  have h := klein_of_tangent (fun t => -f t) (fun t => -g t) X Y hX hY
    fun x hx y hy => by
      have := htan x hx y hy
      show -f x ≤ -f y + -g y * (x - y)
      linarith
  simp only [cfc_neg_apply, trace_neg, HermitianMat.inner_neg_left] at h
  linarith

end HermitianMat
