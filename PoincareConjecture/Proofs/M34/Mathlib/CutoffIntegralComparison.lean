import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support












set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace MeasureTheory

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  {U : Set X} {w f : X → ℝ}




theorem integrable_cutoff_mul (hU : IsOpen U) (hw : ContinuousOn w U)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) (hf : ContinuousOn f U) :
    Integrable (fun x => w x * f x) μ := by
  have hc : Continuous (fun x => w x * f x) :=
    (hw.mul hf).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_left.trans hwU)
  exact hc.integrable_of_hasCompactSupport (hwc.mul_right (f' := f))




theorem integral_cutoff_mul_finsetSum_le {I : Type*} (s : Finset I)
    (hU : IsOpen U) (hw : ContinuousOn w U) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ U) (hw0 : ∀ x ∈ tsupport w, 0 ≤ w x)
    {q : I → X → ℝ} {g : X → ℝ}
    (hq : ∀ i ∈ s, ContinuousOn (q i) U) (hg : ContinuousOn g U)
    (hpoint : ∀ x ∈ tsupport w, (∑ i ∈ s, q i x) ≤ g x) :
    (∑ i ∈ s, ∫ x, w x * q i x ∂μ) ≤ ∫ x, w x * g x ∂μ := by
  have hqi (i : I) (hi : i ∈ s) : Integrable (fun x => w x * q i x) μ :=
    integrable_cutoff_mul hU hw hwc hwU (hq i hi)
  rw [← integral_finsetSum _ hqi]
  apply integral_mono (integrable_finsetSum _ hqi)
    (integrable_cutoff_mul hU hw hwc hwU hg)
  intro x
  by_cases hx : x ∈ tsupport w
  · simpa only [Finset.mul_sum] using
      mul_le_mul_of_nonneg_left (hpoint x hx) (hw0 x hx)
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, Finset.sum_const_zero, le_refl]

end MeasureTheory
