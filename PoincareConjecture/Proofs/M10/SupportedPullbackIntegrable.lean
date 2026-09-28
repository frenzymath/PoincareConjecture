import PoincareConjecture.Proofs.M10.SupportedChartTest
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture.M10

variable {M E : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

theorem integrable_supported_pullback (e : OpenPartialHomeomorph M E)
    {ψ ρ : E → ℝ} {H : M → ℝ} {A : ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ e.target)
    (hρ : ContinuousOn ρ e.target) (hH : Measurable H)
    (hbound : ∀ᵐ y ∂μ, y ∈ tsupport ψ → |ρ y * H (e.symm y)| ≤ A) :
    Integrable (fun y ↦ ψ y * (ρ y * H (e.symm y))) μ := by
  let a := fun y ↦ ψ y * (ρ y * H (e.symm y))
  have hzero (y : E) (hy : y ∉ e.target) : a y = 0 := by
    have hnot : y ∉ tsupport ψ := fun h ↦ hy (hs h)
    simp only [a, image_eq_zero_of_notMem_tsupport hnot, zero_mul]
  have hm : AEStronglyMeasurable a (μ.restrict e.target) :=
    (hψ.measurable.aemeasurable.mul
      ((hρ.aemeasurable e.open_target.measurableSet).mul
        (hH.comp_aemeasurable (e.symm.continuousOn.aemeasurable
          e.open_target.measurableSet)))).aestronglyMeasurable
  have hmfull : AEStronglyMeasurable a μ := by
    have h := (aestronglyMeasurable_indicator_iff e.open_target.measurableSet).mpr hm
    have he : e.target.indicator a = a := by
      funext y
      by_cases hy : y ∈ e.target
      · exact indicator_of_mem hy a
      · simp only [indicator_of_notMem hy, hzero y hy]
    rwa [he] at h
  apply ((hψ.integrable_of_hasCompactSupport hc).abs.mul_const A).mono' hmfull
  filter_upwards [hbound] with y hy
  change ‖a y‖ ≤ |ψ y| * A
  by_cases hys : y ∈ tsupport ψ
  · simp only [a, Real.norm_eq_abs, abs_mul]
    simpa only [abs_mul] using mul_le_mul_of_nonneg_left (hy hys) (abs_nonneg (ψ y))
  · simp only [a, image_eq_zero_of_notMem_tsupport hys, zero_mul, norm_zero, abs_zero, le_refl]

end PoincareConjecture.M10
