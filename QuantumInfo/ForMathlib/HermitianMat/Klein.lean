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

/-- The change-of-basis matrix `Uᴴ V` between the eigenbases of two Hermitian matrices
is unitary. -/
private lemma transition_mem_unitaryGroup (A B : HermitianMat d 𝕜) :
    A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val ∈
      Matrix.unitaryGroup d 𝕜 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact mul_mem (Unitary.star_mem A.H.eigenvectorUnitary.2) B.H.eigenvectorUnitary.2

/-- Expansion of `⟪B.cfc g, A⟫` over both spectra: `inner_cfc_cfc` with `f = id`. -/
private lemma inner_cfc_left_expand (A B : HermitianMat d 𝕜) (g : ℝ → ℝ) :
    ⟪B.cfc g, A⟫_ℝ = ∑ i, ∑ j,
      A.H.eigenvalues i * g (B.H.eigenvalues j) *
        ‖(A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val) i j‖ ^ 2 := by
  rw [inner_comm]
  conv_lhs => rw [← A.cfc_id]
  rw [inner_cfc_cfc]
  simp only [id_eq]

/-- Expansion of `⟪B.cfc g, B⟫` as a single sum over the spectrum of `B`. -/
private lemma inner_cfc_self_expand (B : HermitianMat d 𝕜) (g : ℝ → ℝ) :
    ⟪B.cfc g, B⟫_ℝ = ∑ j, B.H.eigenvalues j * g (B.H.eigenvalues j) := by
  rw [inner_comm, inner_eq_re_trace, trace_mul_cfc]
  simp

omit [DecidableEq d] in
/-- Renormalization along a doubly stochastic weight matrix: a sum `∑ i, c i` spreads over
the rows of the weights as `∑ i, ∑ j, c i * w i j`. -/
private lemma sum_eq_sum_sum_mul_weights (c : d → ℝ) {w : d → d → ℝ}
    (hrow : ∀ i, ∑ j, w i j = 1) :
    ∑ i, c i = ∑ i, ∑ j, c i * w i j :=
  Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, hrow i, mul_one]

omit [DecidableEq d] in
/-- Scalar core of Klein's inequality: a pointwise tangent-line bound transfers through
a doubly stochastic weight matrix to the corresponding weighted sums. -/
private lemma sum_tangent_le (f g : ℝ → ℝ) (x y : d → ℝ) (w : d → d → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 < y j)
    (htan : ∀ a, 0 ≤ a → ∀ b, 0 < b → f a ≤ f b + g b * (a - b)) :
    ∑ i, f (x i) ≤ ∑ j, f (y j) +
      ((∑ i, ∑ j, x i * g (y j) * w i j) - ∑ j, y j * g (y j)) := by
  have h1 := sum_eq_sum_sum_mul_weights (f <| x ·) hrow
  have h2 : ∑ j, f (y j) = ∑ i, ∑ j, f (y j) * w i j := by
    rw [Finset.sum_comm]
    exact sum_eq_sum_sum_mul_weights (f <| y ·) hcol
  have h3 : ∑ j, y j * g (y j) = ∑ i, ∑ j, y j * g (y j) * w i j := by
    rw [Finset.sum_comm]
    exact sum_eq_sum_sum_mul_weights (fun j => y j * g (y j)) hcol
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
  have hW := transition_mem_unitaryGroup X Y
  have hkey := sum_tangent_le f g X.H.eigenvalues Y.H.eigenvalues
    (fun i j => ‖(X.H.eigenvectorUnitary.val.conjTranspose *
      Y.H.eigenvectorUnitary.val) i j‖ ^ 2)
    (fun i j => by positivity) (unitary_row_sum_sq_norm hW) (unitary_col_sum_sq_norm hW)
    (X.eigenvalues_nonneg hX) hY.eigenvalues_pos htan
  rw [HermitianMat.inner_sub_left, trace_cfc_eq, trace_cfc_eq,
    inner_cfc_left_expand, inner_cfc_self_expand]
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

/-! ## The equality condition

When the tangent-line bound is *strict* away from the base point (as for a strictly concave
`f`), Klein's inequality saturates exactly when `X = Y`: a vanishing sum of nonpositive
weighted tangent gaps vanishes termwise, strictness forces the eigenvalues to agree wherever
a transition weight is nonzero, and unitarity of the weight matrix then makes the diagonal
of eigenvalues intertwine the change of basis, collapsing the two spectral decompositions
onto each other. -/

omit [DecidableEq d] in
/-- A vanishing double sum of nonpositive terms vanishes termwise. -/
private lemma eq_zero_of_sum_sum_nonpos {t : d → d → ℝ} (h : ∀ i j, t i j ≤ 0)
    (hsum : ∑ i, ∑ j, t i j = 0) (i j : d) : t i j = 0 := by
  rw [← Finset.sum_product'] at hsum
  exact (Finset.sum_eq_zero_iff_of_nonpos fun p _ => h p.1 p.2).mp hsum (i, j) (by simp)

omit [DecidableEq d] in
/-- Scalar core of the equality condition: if the tangent-line bound is strict away from the
base point, saturation of the weighted-sum inequality of `sum_tangent_le` forces the spectra
to agree wherever the transition weight is nonzero. -/
private lemma sum_tangent_eq (f g : ℝ → ℝ) (x y : d → ℝ) (w : d → d → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 < y j)
    (hstrict : ∀ a, 0 ≤ a → ∀ b, 0 < b → a ≠ b → f a < f b + g b * (a - b))
    (hsum : ∑ i, f (x i) = ∑ j, f (y j) +
      ((∑ i, ∑ j, x i * g (y j) * w i j) - ∑ j, y j * g (y j)))
    (i j : d) (hwij : w i j ≠ 0) : x i = y j := by
  -- spread the single sums over the doubly stochastic weights, as in `sum_tangent_le`
  have h1 := sum_eq_sum_sum_mul_weights (f <| x ·) hrow
  have h2 : ∑ j, f (y j) = ∑ i, ∑ j, f (y j) * w i j := by
    rw [Finset.sum_comm]
    exact sum_eq_sum_sum_mul_weights (f <| y ·) hcol
  have h3 : ∑ j, y j * g (y j) = ∑ i, ∑ j, y j * g (y j) * w i j := by
    rw [Finset.sum_comm]
    exact sum_eq_sum_sum_mul_weights (fun j => y j * g (y j)) hcol
  -- the total weighted tangent gap vanishes
  have hkey : ∑ i, ∑ j, w i j * (f (x i) - (f (y j) + g (y j) * (x i - y j))) = 0 := by
    have hexp : ∀ i j, w i j * (f (x i) - (f (y j) + g (y j) * (x i - y j)))
        = f (x i) * w i j - f (y j) * w i j -
          (x i * g (y j) * w i j - y j * g (y j) * w i j) := fun i j => by ring
    simp only [hexp, Finset.sum_sub_distrib]
    rw [← h1, ← h2, ← h3]
    linarith [hsum]
  -- each weighted gap is nonpositive: zero at the base point, negative elsewhere
  have hterm : ∀ i j, w i j * (f (x i) - (f (y j) + g (y j) * (x i - y j))) ≤ 0 := by
    intro i j
    rcases eq_or_ne (x i) (y j) with he | hne
    · rw [he]
      simp
    · exact mul_nonpos_of_nonneg_of_nonpos (hw i j)
        (by linarith [hstrict _ (hx i) _ (hy j) hne])
  -- so each vanishes; strictness then leaves only `x i = y j` on nonzero weights
  by_contra hne
  have h0 := eq_zero_of_sum_sum_nonpos hterm hkey i j
  have hlt : f (x i) - (f (y j) + g (y j) * (x i - y j)) < 0 := by
    linarith [hstrict _ (hx i) _ (hy j) hne]
  exact absurd h0 (ne_of_lt (mul_neg_of_pos_of_neg ((hw i j).lt_of_ne' hwij) hlt))

/-- If a diagonal matrix intertwines the change-of-basis `Uᴴ V` between two unitaries, the
two unitary conjugations agree: `U D₁ Uᴴ = V D₂ Vᴴ`. -/
private lemma conj_diag_congr {U V D₁ D₂ : Matrix d d 𝕜}
    (hU : U ∈ Matrix.unitaryGroup d 𝕜) (hV : V ∈ Matrix.unitaryGroup d 𝕜)
    (h : D₁ * (U.conjTranspose * V) = (U.conjTranspose * V) * D₂) :
    U * D₁ * U.conjTranspose = V * D₂ * V.conjTranspose := by
  have hUU : U * U.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hU
  have hVV : V * V.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hV
  have h2 := congrArg (fun M => U * M * V.conjTranspose) h
  simp only [← Matrix.mul_assoc] at h2
  -- h2 : U * D₁ * Uᴴ * V * Vᴴ = U * Uᴴ * V * D₂ * Vᴴ
  rwa [Matrix.mul_assoc (U * D₁ * U.conjTranspose) V V.conjTranspose, hVV, mul_one,
    hUU, one_mul] at h2

/-- Two Hermitian matrices are equal as soon as their eigenvalues agree across every pair of
eigenbasis directions with nonzero transition amplitude: the diagonal of eigenvalues then
intertwines the change of basis, so the two spectral decompositions coincide. -/
private lemma eq_of_eigenvalues_eq_on_transition (X Y : HermitianMat d 𝕜)
    (h : ∀ i j, (X.H.eigenvectorUnitary.val.conjTranspose * Y.H.eigenvectorUnitary.val) i j ≠ 0 →
      X.H.eigenvalues i = Y.H.eigenvalues j) : X = Y := by
  have hDW : Matrix.diagonal (RCLike.ofReal ∘ X.H.eigenvalues) *
      (X.H.eigenvectorUnitary.val.conjTranspose * Y.H.eigenvectorUnitary.val) =
      (X.H.eigenvectorUnitary.val.conjTranspose * Y.H.eigenvectorUnitary.val) *
        Matrix.diagonal (RCLike.ofReal ∘ Y.H.eigenvalues) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rcases eq_or_ne ((X.H.eigenvectorUnitary.val.conjTranspose *
        Y.H.eigenvectorUnitary.val) i j) 0 with hw | hw
    · rw [hw, mul_zero, zero_mul]
    · rw [Function.comp_apply, Function.comp_apply, h i j hw, mul_comm]
  have hXspec : X.mat = X.H.eigenvectorUnitary.val *
      Matrix.diagonal (RCLike.ofReal ∘ X.H.eigenvalues) *
        X.H.eigenvectorUnitary.val.conjTranspose := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      using X.H.spectral_theorem
  have hYspec : Y.mat = Y.H.eigenvectorUnitary.val *
      Matrix.diagonal (RCLike.ofReal ∘ Y.H.eigenvalues) *
        Y.H.eigenvectorUnitary.val.conjTranspose := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      using Y.H.spectral_theorem
  apply HermitianMat.ext
  rw [hXspec, hYspec]
  exact conj_diag_congr X.H.eigenvectorUnitary.2 Y.H.eigenvectorUnitary.2 hDW

/-- **Equality condition in Klein's inequality**: when the tangent-line bound with slope
function `g` is *strict* away from the base point (as holds for a strictly concave
differentiable `f`, e.g. `Real.negMulLog` via `Real.negMulLog_lt_tangent`), the inequality
`klein_of_tangent` saturates exactly when `X = Y`. -/
lemma klein_of_tangent_eq_iff (f g : ℝ → ℝ) (X Y : HermitianMat d 𝕜)
    (hX : 0 ≤ X) (hY : Y.mat.PosDef)
    (hstrict : ∀ x, 0 ≤ x → ∀ y, 0 < y → x ≠ y → f x < f y + g y * (x - y)) :
    (X.cfc f).trace = (Y.cfc f).trace + ⟪Y.cfc g, X - Y⟫_ℝ ↔ X = Y := by
  constructor
  · intro heq
    rw [HermitianMat.inner_sub_left, trace_cfc_eq, trace_cfc_eq,
      inner_cfc_left_expand, inner_cfc_self_expand] at heq
    have hW := transition_mem_unitaryGroup X Y
    refine eq_of_eigenvalues_eq_on_transition X Y fun i j hne =>
      sum_tangent_eq f g X.H.eigenvalues Y.H.eigenvalues
        (fun i j => ‖(X.H.eigenvectorUnitary.val.conjTranspose *
          Y.H.eigenvectorUnitary.val) i j‖ ^ 2)
        (fun i j => by positivity) (unitary_row_sum_sq_norm hW) (unitary_col_sum_sq_norm hW)
        (X.eigenvalues_nonneg hX) hY.eigenvalues_pos hstrict heq i j (by simpa using hne)
  · rintro rfl
    simp

end HermitianMat
