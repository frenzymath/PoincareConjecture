import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace MeasureTheory

theorem setIntegral_le_finsetSum_of_cover
    {X I : Type*} [MeasurableSpace X] {μ : Measure X} (s : Finset I)
    {K : Set X} {Q : I → Set X} {f : X → ℝ}
    (hK : MeasurableSet K) (hQ : ∀ i ∈ s, MeasurableSet (Q i))
    (hfK : IntegrableOn f K μ) (hfQ : ∀ i ∈ s, IntegrableOn f (Q i) μ)
    (hf0 : ∀ x, 0 ≤ f x) (hcover : K ⊆ ⋃ i ∈ s, Q i) :
    (∫ x in K, f x ∂μ) ≤ ∑ i ∈ s, ∫ x in Q i, f x ∂μ := by
  classical
  have hi (i : I) (hi : i ∈ s) : Integrable ((Q i).indicator f) μ :=
    (hfQ i hi).integrable_indicator (hQ i hi)
  have h0 (i : I) (x : X) : 0 ≤ (Q i).indicator f x := by
    by_cases hx : x ∈ Q i <;> simp [hx, hf0 x]
  calc
    (∫ x in K, f x ∂μ) = ∫ x, K.indicator f x ∂μ := (integral_indicator hK).symm
    _ ≤ ∫ x, ∑ i ∈ s, (Q i).indicator f x ∂μ := by
      apply integral_mono (hfK.integrable_indicator hK) (integrable_finsetSum _ hi)
      intro x
      by_cases hx : x ∈ K
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
        obtain ⟨his, hxi⟩ := mem_iUnion.mp hxi
        rw [indicator_of_mem hx]
        calc
          f x = (Q i).indicator f x := (indicator_of_mem hxi f).symm
          _ ≤ ∑ j ∈ s, (Q j).indicator f x := Finset.single_le_sum (fun j _ => h0 j x) his
      · rw [indicator_of_notMem hx]
        exact Finset.sum_nonneg (fun i _ => h0 i x)
    _ = ∑ i ∈ s, ∫ x, (Q i).indicator f x ∂μ := integral_finsetSum s hi
    _ = ∑ i ∈ s, ∫ x in Q i, f x ∂μ :=
      Finset.sum_congr rfl (fun i hi => integral_indicator (hQ i hi))

theorem setIntegral_le_cutoff_sq_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {Q : Set X} (hQ : MeasurableSet Q) {φ f : X → ℝ}
    (hi : Integrable (fun x => φ x ^ 2 * f x) μ)
    (hf0 : ∀ x, 0 ≤ f x) (hφ : ∀ x ∈ Q, φ x = 1) :
    (∫ x in Q, f x ∂μ) ≤ ∫ x, φ x ^ 2 * f x ∂μ := by
  calc
    (∫ x in Q, f x ∂μ) = ∫ x in Q, φ x ^ 2 * f x ∂μ := by
      apply setIntegral_congr_fun hQ
      intro x hx
      change f x = φ x ^ 2 * f x
      rw [hφ x hx, one_pow, one_mul]
    _ ≤ ∫ x, φ x ^ 2 * f x ∂μ :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (fun x =>
        mul_nonneg (sq_nonneg _) (hf0 x)))

end MeasureTheory
