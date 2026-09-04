/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

noncomputable section
open NNReal

namespace Real

theorem negMulLog_strictMonoOn : StrictMonoOn Real.negMulLog (Set.Icc 0 (exp (-1))) := by
  apply strictMonoOn_of_deriv_pos
  · exact convex_Icc 0 (exp (-1))
  · exact continuous_negMulLog.continuousOn
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    linarith only [log_exp (-1), log_lt_log hx.left hx.right, deriv_negMulLog hx.left.ne']

theorem negMulLog_strictAntiOn : StrictAntiOn Real.negMulLog (Set.Ici (exp (-1))) := by
  apply strictAntiOn_of_deriv_neg
  · exact convex_Ici (exp (-1))
  · exact continuous_negMulLog.continuousOn
  · intro x hx
    rw [interior_Ici' Set.nonempty_Iio, Set.mem_Ioi] at hx
    have hx' : x ≠ 0 := by grind [exp_nonneg]
    linarith [log_exp (-1), log_lt_log (exp_pos (-1)) hx, deriv_negMulLog hx']

/-- Tangent-line bound for `Real.negMulLog`: being concave on `[0, ∞)`, it lies below
each of its tangent lines at base points `y > 0`, whose slope is
`deriv negMulLog y = -(log y + 1)`. Valid for all `x ≥ 0`, including `x = 0`. -/
lemma negMulLog_le_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    negMulLog x ≤ negMulLog y + -(log y + 1) * (x - y) := by
  rcases hx.eq_or_lt with h0 | hx'
  · rw [← h0]
    simp only [negMulLog_def]
    nlinarith [hy]
  · -- for `x > 0`, this rearranges the classic bound `log (y/x) ≤ y/x - 1`
    have hlog : log (y / x) ≤ y / x - 1 := log_le_sub_one_of_pos (div_pos hy hx')
    rw [log_div hy.ne' hx'.ne'] at hlog
    have h4 : x * (y / x - 1) = y - x := by
      rw [mul_sub, mul_one, mul_comm, div_mul_cancel₀ _ hx'.ne']
    have h2 : x * (log y - log x) ≤ y - x := by
      have h3 := mul_le_mul_of_nonneg_left hlog hx'.le
      rwa [h4] at h3
    simp only [negMulLog_def]
    nlinarith [h2]

/-- Strict tangent-line bound for `Real.negMulLog`: being *strictly* concave on `[0, ∞)`,
it lies strictly below its tangent lines at base points `y > 0` except at the base point
itself. Strictness comes from `Real.log_lt_sub_one_of_pos`. -/
lemma negMulLog_lt_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≠ y) :
    negMulLog x < negMulLog y + -(log y + 1) * (x - y) := by
  rcases hx.eq_or_lt with h0 | hx'
  · rw [← h0]
    simp only [negMulLog_def]
    nlinarith [hy]
  · -- for `x > 0`, this rearranges the classic strict bound `log (y/x) < y/x - 1`
    have hne : y / x ≠ 1 := fun hc => hxy (by rw [(div_eq_iff hx'.ne').mp hc, one_mul])
    have hlog : log (y / x) < y / x - 1 := log_lt_sub_one_of_pos (div_pos hy hx') hne
    rw [log_div hy.ne' hx'.ne'] at hlog
    have h4 : x * (y / x - 1) = y - x := by
      rw [mul_sub, mul_one, mul_comm, div_mul_cancel₀ _ hx'.ne']
    have h2 : x * (log y - log x) < y - x := by
      have h3 := mul_lt_mul_of_pos_left hlog hx'
      rwa [h4] at h3
    simp only [negMulLog_def]
    nlinarith [h2]

theorem negMulLog_le_rexp_neg_one {x : ℝ} (hx : 0 ≤ x) : negMulLog x ≤ exp (-1) := by
  by_cases hp : x < exp (-1)
  · grw [negMulLog_strictMonoOn.monotoneOn (by grind) (by grind) hp.le]
    simp [negMulLog]
  by_cases hp' : Real.exp (-1) < x
  · grw [negMulLog_strictAntiOn.antitoneOn (by grind) (by grind) hp'.le]
    simp [negMulLog]
  · simp [show x = exp (-1) by order, negMulLog]

end Real
