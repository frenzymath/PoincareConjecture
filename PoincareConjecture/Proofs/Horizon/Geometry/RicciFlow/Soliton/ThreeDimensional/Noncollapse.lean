import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

theorem metricKappaNoncollapsed_of_scalar_comparison
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (F : RicciFlow 3 M (Iio 0))
    {κ : ℝ} (hκ : 0 < κ)
    (hcomparison : ∀ t < 0, ∀ x,
      (F.connection t).curvatureTensorNorm x ≤ 9 * (F.connection t).scalarCurvature x)
    (hscalar : ∀ x, MonotoneOn (fun t => (F.connection t).scalarCurvature x) (Iio 0))
    (hnoncollapse : ∀ t < 0, ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Ioc (t - r ^ 2) t, ∀ q ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball p r))
    {t : ℝ} (ht : t < 0) :
    MetricKappaNoncollapsed (F.metric t) (F.connection t) (κ / 729) := by
  refine ⟨div_pos hκ (by norm_num), ?_⟩
  intro p r hr hbound
  have hr9 : 0 < r / 9 := by positivity
  have hsub : (F.metric t).ball p (r / 9) ⊆ (F.metric t).ball p r := by
    intro q hq
    exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (by linarith))
  have hparabolic : ∀ s ∈ Ioc (t - (r / 9) ^ 2) t,
      ∀ q ∈ (F.metric t).ball p (r / 9),
      |(F.connection s).curvatureTensorNorm q| ≤ (r / 9)⁻¹ ^ 2 := by
    intro s hs q hq
    have hs0 : s < 0 := hs.2.trans_lt ht
    have hnorm := hcomparison s hs0 q
    have htrace := (F.connection t).abs_scalarCurvature_le_curvatureTensorNorm q
    have hmono := hscalar q hs0 ht hs.2
    have hterminal := (le_abs_self _).trans (hbound q (hsub hq))
    have hnorm_nonneg : 0 ≤ (F.connection s).curvatureTensorNorm q := Real.sqrt_nonneg _
    rw [abs_of_nonneg hnorm_nonneg]
    have hscale : (r / 9)⁻¹ ^ 2 = 81 * r⁻¹ ^ 2 := by
      rw [inv_div, div_pow]
      norm_num [div_eq_mul_inv]
    rw [hscale]
    norm_num at hnorm htrace
    have htrace' := (le_abs_self _).trans htrace
    linarith
  have hvol := hnoncollapse t ht p (r / 9) hr9 hparabolic
  have hconstant : κ * (r / 9) ^ 3 = (κ / 729) * r ^ 3 := by ring
  rw [hconstant] at hvol
  exact hvol.trans (MeasureTheory.measure_mono hsub)



theorem metricKappaNoncollapsed_of_scalar_monotone
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow 3 M (Iio 0))
    {κ : ℝ} (hκ : 0 < κ)
    (hoperator : ∀ t < 0, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ x, MonotoneOn (fun t => (F.connection t).scalarCurvature x) (Iio 0))
    (hnoncollapse : ∀ t < 0, ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Ioc (t - r ^ 2) t, ∀ q ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball p r))
    {t : ℝ} (ht : t < 0) :
    MetricKappaNoncollapsed (F.metric t) (F.connection t) (κ / 729) := by
  apply metricKappaNoncollapsed_of_scalar_comparison F hκ ?_ hscalar hnoncollapse ht
  intro s hs x
  convert (F.connection s).curvatureTensorNorm_le_scalarCurvature
    (hC.tensor_calculus 3 M (F.metric s) (F.connection s)) x (hoperator s hs x)
    using 1
  norm_num

end PoincareConjecture.RicciFlow
