import PoincareConjecture.Proofs.M10.LocalDivergenceIntegration
import PoincareConjecture.Proofs.M10.WeightedMetricDual

set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem inverse_bilinear_pairing_symm (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hi : B.IsInvertible) (hs : ∀ v w, B v w = B w v) (d e : E →L[ℝ] ℝ) :
    d (B.inverse e) = e (B.inverse d) := by
  have hd := congrArg (fun a : E →L[ℝ] ℝ ↦ a (B.inverse e)) (hi.self_apply_inverse d)
  have he := congrArg (fun a : E →L[ℝ] ℝ ↦ a (B.inverse d)) (hi.self_apply_inverse e)
  exact hd.symm.trans ((hs _ _).trans he)

theorem integral_weighted_green {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ u ψ : E → ℝ}
    (hB : ContDiffOn ℝ 1 B U) (hρ : ContDiffOn ℝ 1 ρ U)
    (hi : ∀ x ∈ U, (B x).IsInvertible) (hBs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hu : ContDiffOn ℝ 2 u U) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    Integrable (fun x ↦ u x * LinearMap.trace ℝ E
      (fderiv ℝ (weightedMetricDual B ρ ψ) x).toLinearMap) μ ∧
    Integrable (fun x ↦ ψ x * LinearMap.trace ℝ E
      (fderiv ℝ (weightedMetricDual B ρ u) x).toLinearMap) μ ∧
    (∫ x, u x * LinearMap.trace ℝ E
      (fderiv ℝ (weightedMetricDual B ρ ψ) x).toLinearMap ∂μ) =
    ∫ x, ψ x * LinearMap.trace ℝ E
      (fderiv ℝ (weightedMetricDual B ρ u) x).toLinearMap ∂μ := by
  have hVu : ContDiffOn ℝ 1 (weightedMetricDual B ρ u) U := by
    intro x hx
    exact (weightedMetricDual_contDiffAt (hB.contDiffAt (hU.mem_nhds hx))
      (hρ.contDiffAt (hU.mem_nhds hx)) (hu.contDiffAt (hU.mem_nhds hx))
      (hi x hx)).contDiffWithinAt
  have hVψ := weightedMetricDual_contDiff_of_tsupport_subset hU hB hρ hψ.contDiffOn hi hs
  have hleft := integral_mul_trace_fderiv_of_compact_vector (μ := μ) b hU
    (hu.of_le (by norm_num)) hVψ (weightedMetricDual_hasCompactSupport B ρ hc)
    ((tsupport_weightedMetricDual_subset B ρ ψ).trans hs)
  have hright := integral_mul_trace_fderiv_of_compact_scalar (μ := μ) b hU
    (hψ.of_le (by norm_num)) hVu hc hs
  refine ⟨hleft.1, hright.1, hleft.2.2.trans ?_⟩
  rw [hright.2.2]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    by_cases hx : x ∈ U
    · simp only [weightedMetricDual, map_smul, smul_eq_mul]
      rw [inverse_bilinear_pairing_symm (B x) (hi x hx) (hBs x hx)]
    · have hxs : x ∉ tsupport ψ := fun h ↦ hx (hs h)
      simp only [weightedMetricDual, fderiv_of_notMem_tsupport ℝ hxs, map_zero,
        smul_zero, zero_apply])

end PoincareConjecture.M10
