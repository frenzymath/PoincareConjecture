import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.FiniteCover
open Set MeasureTheory
open scoped BigOperators
namespace Poincare.CurvatureIntegral
theorem integral_le_card_mul_weighted_bound_of_finset_cover
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {E W : Set X} (hE : MeasurableSet E) (S : Finset ι)
    (U V : ι → Set X) (hU : ∀ i ∈ S, MeasurableSet (U i))
    {R K : X → ℝ} (hR : ∀ x, 0 ≤ R x) (hK : ∀ x, 0 ≤ K x)
    (hRi : IntegrableOn R E μ)
    (hUi : ∀ i ∈ S, IntegrableOn R (U i) μ)
    (hKi : IntegrableOn K W μ)
    (hcover : E ⊆ ⋃ i ∈ S, U i)
    (hVW : ∀ i ∈ S, V i ⊆ W)
    {B a : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i ∈ S, (∫ x in U i, R x ∂μ) ≤
      B * (a + ∫ x in V i, K x ∂μ)) :
    (∫ x in E, R x ∂μ) ≤ (S.card : ℝ) * B *
      (a + ∫ x in W, K x ∂μ) := by
  classical
  calc
    _ ≤ ∑ i ∈ S, ∫ x in U i, R x ∂μ :=
      integral_le_sum_of_finset_cover hE S U hU hR hRi hUi hcover
    _ ≤ ∑ _i ∈ S, B * (a + ∫ x in W, K x ∂μ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (hbound i hi).trans
      apply mul_le_mul_of_nonneg_left _ hB
      apply add_le_add_right
      exact setIntegral_mono_set hKi (Filter.Eventually.of_forall hK)
        (Filter.Eventually.of_forall (hVW i hi))
    _ = _ := by simp [nsmul_eq_mul]; ring
end Poincare.CurvatureIntegral
