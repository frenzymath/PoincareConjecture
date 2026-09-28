import PoincareConjecture.Proofs.M34.Mathlib.CutoffIntegralComparison
import Mathlib.MeasureTheory.Integral.Bochner.Set










set_option autoImplicit false

open Set MeasureTheory

namespace MeasureTheory



theorem exists_integral_cutoff_sq_le_setIntegral
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {U : Set X} (hU : IsOpen U) {φ : X → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : X → ℝ, ContinuousOn ρ U →
      (∀ x ∈ tsupport φ, 0 ≤ ρ x) →
      (∫ x, φ x ^ 2 * ρ x ∂μ) ≤ B * ∫ x in tsupport φ, ρ x ∂μ := by
  obtain ⟨b, hb⟩ := hφc.exists_bound_of_continuousOn (hφ.pow 2).continuousOn
  let B := max b 0
  refine ⟨B, le_max_right _ _, ?_⟩
  intro ρ hρ hρ0
  have hB (x) (hx : x ∈ tsupport φ) : φ x ^ 2 ≤ B :=
    (le_abs_self _).trans ((hb x hx).trans (le_max_left _ _))
  have hwc : HasCompactSupport (fun x => φ x ^ 2) :=
    hφc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hwU : tsupport (fun x => φ x ^ 2) ⊆ U := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := φ) (g := φ)).trans hφU
  have hi : Integrable (fun x => φ x ^ 2 * ρ x) μ :=
    integrable_cutoff_mul hU (hφ.pow 2).continuousOn hwc hwU hρ
  have hρi : IntegrableOn ρ (tsupport φ) μ :=
    ContinuousOn.integrableOn_compact' hφc (isClosed_tsupport φ).measurableSet
      (hρ.mono hφU)
  have hpoint (x) : φ x ^ 2 * ρ x ≤ B * (tsupport φ).indicator ρ x := by
    by_cases hx : x ∈ tsupport φ
    · rw [indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right (hB x hx) (hρ0 x hx)
    · simp [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  have hbnd := integral_mono hi
    ((hρi.integrable_indicator (isClosed_tsupport φ).measurableSet).const_mul B) hpoint
  simpa only [integral_const_mul, integral_indicator (isClosed_tsupport φ).measurableSet] using hbnd

end MeasureTheory
