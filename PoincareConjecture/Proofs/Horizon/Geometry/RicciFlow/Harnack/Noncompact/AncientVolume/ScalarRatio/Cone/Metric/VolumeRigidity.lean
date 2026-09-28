import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RiemannianVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.Flatness

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

theorem curvatureTensor_eq_zero_of_asymptoticCone_volume_ge_euclidean
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 2 ≤ n)
    (hc : MetricComplete g) (hoperator : ∀ x, D.NonnegativeCurvatureOperator x)
    (p : M) :
    letI := g.toMetricSpace
    let hsec : D.NonnegativeSectionalCurvature := fun x v w =>
      D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x (hoperator x) v w
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    ENNReal.ofReal (euclideanUnitBallVolume n) ≤ Measure.euclideanHausdorffMeasure n
      {z : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison z < 1} →
    ∀ (x : M) (u v w z : TangentSpace (𝓡 n) x), D.curvatureTensor x u v w z = 0 := by
  let := g.toMetricSpace
  let hsec : D.NonnegativeSectionalCurvature := fun x v w =>
    D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x (hoperator x) v w
  dsimp only
  intro hvolume
  have hRic := fun x v => D.ricci_nonneg_of_nonnegative_curvatureOperator x (hoperator x) v
  have hlim := g.tendsto_asymptoticVolumeRatio D (by omega) hc hRic p
  have hnonneg : 0 ≤ g.asymptoticVolumeRatio p := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    positivity
  have hupper : g.asymptoticVolumeRatio p ≤ euclideanUnitBallVolume n := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact g.ball_volume_div_pow_le_euclideanUnitBallVolume D (by omega) hc hRic p hr
  have hlower : euclideanUnitBallVolume n ≤ g.asymptoticVolumeRatio p := by
    apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
    exact hvolume.trans (g.asymptoticCone_volume_le_asymptoticVolumeRatio
      D (by omega) hc hsec p)
  have heq := le_antisymm hupper hlower
  exact g.curvatureTensor_eq_zero_of_maximal_volume_growth D hn hc hoperator p
    (heq ▸ hlim)

theorem asymptoticCone_volume_lt_euclidean_of_scalar_pos
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 2 ≤ n)
    (hc : MetricComplete g) (hoperator : ∀ x, D.NonnegativeCurvatureOperator x)
    (hnonflat : ∃ x, 0 < D.scalarCurvature x) (p : M) :
    letI := g.toMetricSpace
    let hsec : D.NonnegativeSectionalCurvature := fun x v w =>
      D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x (hoperator x) v w
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    Measure.euclideanHausdorffMeasure n
      {z : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison z < 1} <
      ENNReal.ofReal (euclideanUnitBallVolume n) := by
  let := g.toMetricSpace
  by_contra h
  have hflat := g.curvatureTensor_eq_zero_of_asymptoticCone_volume_ge_euclidean
    D hn hc hoperator p (le_of_not_gt h)
  obtain ⟨x, hx⟩ := hnonflat
  have hzero : D.scalarCurvature x = 0 := by
    simp only [LeviCivitaData.scalarCurvature, LeviCivitaData.ricci, hflat,
      Finset.sum_const_zero]
  exact hx.ne' hzero

end PoincareConjecture.RiemannianMetric
