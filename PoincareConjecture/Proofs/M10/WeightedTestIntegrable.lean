import PoincareConjecture.Proofs.M10.EuclideanGreen








set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem continuous_trace_fderiv {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {V : E → E} (hV : ContDiff ℝ 1 V) :
    Continuous (fun x ↦ LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap) := by
  simp_rw [LinearMap.trace_eq_sum_inner _ b]
  exact continuous_finsetSum _ (fun i _ ↦
    continuous_const.inner ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem tsupport_trace_fderiv_subset (V : E → E) :
    tsupport (fun x ↦ LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap) ⊆ tsupport V := by
  apply closure_minimal _ (isClosed_tsupport V)
  intro x hx
  by_contra hnot
  apply hx
  simp only [fderiv_of_notMem_tsupport ℝ hnot, ContinuousLinearMap.toLinearMap_zero, map_zero]



theorem integrable_mul_trace_weighted_test {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {U : Set E} (hU : IsOpen U)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ u ψ : E → ℝ}
    (hB : ContDiffOn ℝ 1 B U) (hρ : ContDiffOn ℝ 1 ρ U)
    (hi : ∀ x ∈ U, (B x).IsInvertible) (hu : ContinuousOn u U)
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    Integrable (fun x ↦ LinearMap.trace ℝ E
      (fderiv ℝ (weightedMetricDual B ρ ψ) x).toLinearMap) μ ∧
    Integrable (fun x ↦ u x * LinearMap.trace ℝ E
      (fderiv ℝ (weightedMetricDual B ρ ψ) x).toLinearMap) μ := by
  have hV := weightedMetricDual_contDiff_of_tsupport_subset hU hB hρ hψ.contDiffOn hi hs
  have hcont := continuous_trace_fderiv b hV
  have hsup := (tsupport_trace_fderiv_subset (weightedMetricDual B ρ ψ)).trans
    (tsupport_weightedMetricDual_subset B ρ ψ)
  refine ⟨hcont.integrable_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) hsup), ?_⟩
  exact integrable_of_continuousOn_of_tsupport_subset hU hc hs
    (hu.mul hcont.continuousOn) (tsupport_mul_subset_right.trans hsup)

end PoincareConjecture.M10
