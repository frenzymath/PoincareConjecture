import PoincareConjecture.Proofs.M34.Mathlib.CutoffIntegralComparison










set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace MeasureTheory



theorem integral_cutoff_sq_finsetSum
    {X I : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] (s : Finset I)
    {U : Set X} (hU : IsOpen U) {φ : X → ℝ}
    (hφ : ContinuousOn φ U) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    {f : I → X → ℝ} (hf : ∀ i ∈ s, ContinuousOn (f i) U) :
    (∫ x, φ x ^ 2 * (∑ i ∈ s, f i x ^ 2) ∂μ) =
      ∑ i ∈ s, ∫ x, (φ x * f i x) ^ 2 ∂μ := by
  have hwc : HasCompactSupport (fun x => φ x ^ 2) :=
    hφc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hwU : tsupport (fun x => φ x ^ 2) ⊆ U := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := φ) (g := φ)).trans hφU
  have hi (i : I) (hi : i ∈ s) : Integrable (fun x => φ x ^ 2 * f i x ^ 2) μ :=
    integrable_cutoff_mul hU (hφ.pow 2) hwc hwU ((hf i hi).pow 2)
  simpa only [Finset.mul_sum, mul_pow] using integral_finsetSum s hi

end MeasureTheory
