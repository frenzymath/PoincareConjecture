import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Twisted.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Main

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

theorem normalized_compact_uniform_scalar_upper
    (P : M27KappaAlternativePredecessors.{u})
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 0 ≤ D) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        IsCompact (univ : Set M) →
        metricDiameter (K.flow.metric 0) univ ≤ D →
        ∀ x : M, (K.flow.connection 0).scalarCurvature x ≤ L := by
  obtain ⟨L, hL, hbound⟩ := ScalarDerivatives.uniform_based_local_scalar_bound
    P.scalarDerivativeServices hkappa (D + 1) (by linarith)
  refine ⟨L, hL, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnc hnormalized hcompact hdiam x
  have hx := compact_mem_ball_of_metricDiameter_lt (K.flow.metric 0) hcompact
    (hdiam.trans_lt (by linarith : D < D + 1)) p x
  have hb := hbound
    (ScalarDerivatives.smallBasedKappaSolution K p kappa hkappa hnc hnormalized)
    (equivShrink M x)
    ((ScalarDerivatives.smallBasedKappaSolution_mem_ball K p kappa hkappa hnc hnormalized
      0 (D + 1) x).mpr hx)
  change (K.flow.shrink.connection 0).scalarCurvature (equivShrink M x) ≤ L at hb
  simpa only [K.flow.shrink_scalarCurvature, Equiv.symm_apply_apply] using hb

section VolumeComparison

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem compact_volume_le_of_metricDiameter_lt
    (P : M27KappaAlternativePredecessors.{u}) (K : AncientKappaSolution 3 M)
    (hcompact : IsCompact (univ : Set M)) (p : M)
    {r : ℝ} (hr : 0 < r) (hdiam : metricDiameter (K.flow.metric 0) univ < r) :
    calibratedMetricVolume (K.flow.metric 0) univ ≤
      ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume 3 * r ^ (3 : ℕ)) :=
  P.capServices.calibratedVolume_le_of_subset_ball le_rfl p hr
    (fun x _ => compact_mem_ball_of_metricDiameter_lt (K.flow.metric 0) hcompact hdiam p x)

end VolumeComparison

theorem normalized_compact_volume_diameter_bounds
    (P : M27KappaAlternativePredecessors.{u})
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 0 ≤ D) :
    ∃ d v V : ℝ, 0 < d ∧ 0 < v ∧ 0 < V ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        IsCompact (univ : Set M) →
        metricDiameter (K.flow.metric 0) univ ≤ D →
        d < metricDiameter (K.flow.metric 0) univ ∧
          ENNReal.ofReal v < calibratedMetricVolume (K.flow.metric 0) univ ∧
          calibratedMetricVolume (K.flow.metric 0) univ < ENNReal.ofReal V := by
  obtain ⟨L, hL, hscalar⟩ := normalized_compact_uniform_scalar_upper P hkappa hD
  let A : ℝ := max L 1
  have hAone : 1 ≤ A := le_max_right _ _
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hAone
  let r : ℝ := A⁻¹
  have hr : 0 < r := inv_pos.mpr hA
  let b : ℝ := kappa * r ^ (3 : ℕ)
  have hb : 0 < b := mul_pos hkappa (pow_pos hr 3)
  let omega : ℝ := RiemannianMetric.euclideanUnitBallVolume 3
  have homega : 0 < omega := RiemannianMetric.euclideanUnitBallVolume_pos 3
  let d : ℝ := min 1 (b / (16 * (omega + 1)))
  have hd : 0 < d := lt_min zero_lt_one (div_pos hb (by positivity))
  have hdone : d ≤ 1 := min_le_left _ _
  have hdb : d * (16 * (omega + 1)) ≤ b :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨d, b / 2, omega * (D + 1) ^ (3 : ℕ) + 1, hd, by positivity,
    by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnc hnormalized hcompact hdiam
  have hglobal (x : M) : (K.flow.connection 0).scalarCurvature x ≤ A :=
    (hscalar K p hnc hnormalized hcompact hdiam x).trans (le_max_left _ _)
  have hvolBall : ENNReal.ofReal b ≤
      calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p r) := by
    apply hnc r hr 0 le_rfl p r hr le_rfl
    intro s hs x _
    rw [abs_of_nonneg (show 0 ≤ (K.flow.connection s).curvatureTensorNorm x from
      Real.sqrt_nonneg _)]
    have hnorm := (P.past_norm_le_scalar M K s 0 hs.2 le_rfl x).trans (hglobal x)
    change (K.flow.connection s).curvatureTensorNorm x ≤ (A⁻¹)⁻¹ ^ 2
    rw [inv_inv]
    nlinarith
  have hvol : ENNReal.ofReal b ≤ calibratedMetricVolume (K.flow.metric 0) univ :=
    hvolBall.trans (MeasureTheory.measure_mono (subset_univ _))
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    have hsmall : metricDiameter (K.flow.metric 0) univ < 2 * d := by
      have hle := le_of_not_gt h
      linarith
    have hupper := compact_volume_le_of_metricDiameter_lt P K hcompact p
      (show 0 < 2 * d by positivity) hsmall
    have hreal : b ≤ omega * (2 * d) ^ (3 : ℕ) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hvol.trans hupper)
    have hcube : d ^ (3 : ℕ) ≤ d := by nlinarith [sq_nonneg d, sq_nonneg (1 - d)]
    have hmul := mul_le_mul_of_nonneg_left hcube homega.le
    nlinarith
  · exact (ENNReal.ofReal_lt_ofReal_iff hb).mpr (by linarith) |>.trans_le hvol
  · apply (compact_volume_le_of_metricDiameter_lt P K hcompact p
      (show 0 < D + 1 by linarith) (hdiam.trans_lt (by linarith : D < D + 1))).trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    change omega * (D + 1) ^ (3 : ℕ) < omega * (D + 1) ^ (3 : ℕ) + 1
    linarith

end PoincareConjecture
