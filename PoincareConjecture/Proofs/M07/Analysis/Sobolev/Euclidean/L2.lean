import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Poincare.Analysis.Sobolev

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}

theorem norm_toLp_sq_eq_integral (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, pow_two]

theorem eLpNorm_toReal_sq_eq_integral (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← Lp.norm_toLp f hf]
  exact norm_toLp_sq_eq_integral hf

theorem eLpNorm_two_le_sqrt_of_integral_sq_le (hf : MemLp f 2 μ)
    {C : ℝ} (hC : ∫ x, f x ^ 2 ∂μ ≤ C) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
  have hC0 : 0 ≤ C := (integral_nonneg fun x => sq_nonneg (f x)).trans hC
  have hb : (eLpNorm f 2 μ).toReal ≤ Real.sqrt C := by
    apply (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg C)).mp
    rw [eLpNorm_toReal_sq_eq_integral hf, Real.sq_sqrt hC0]
    exact hC
  simpa only [ENNReal.ofReal_toReal hf.eLpNorm_lt_top.ne] using
    ENNReal.ofReal_le_ofReal hb

end Poincare.Analysis.Sobolev
