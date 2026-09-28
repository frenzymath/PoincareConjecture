import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.VolumeComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RiemannianLink
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeRatio.Monotonicity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

theorem asymptoticCone_volume_le_normalized_ball_volume
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {L : ℝ} (hL : 0 < L) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    Measure.euclideanHausdorffMeasure n
      {z : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison z < 1} ≤
      (ENNReal.ofReal L)⁻¹ ^ n * g.volumeMeasure (g.ball p L) := by
  let := g.toMetricSpace
  let := g.nonempty_basedMinimizingRays hc p
  have h := cone_radial_ball_volume_le_source_ball
    (g.rayComparison_of_metricComplete D hc hsec p) n hL
  rw [g.toMetricSpace_ball] at h
  exact h

theorem asymptoticCone_volume_le_asymptoticVolumeRatio
    [SecondCountableTopology M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    Measure.euclideanHausdorffMeasure n
      {z : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison z < 1} ≤
      ENNReal.ofReal (g.asymptoticVolumeRatio p) := by
  let := g.toMetricSpace
  have hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v := by
    intro x v
    unfold LeviCivitaData.ricci
    exact Finset.sum_nonneg fun i _ => hsec x v _
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (g.tendsto_asymptoticVolumeRatio D hn hc hRic p)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have h := g.asymptoticCone_volume_le_normalized_ball_volume D hc hsec p hL
  have hfinite := g.ball_volume_ne_top_of_metricComplete hc p L
  have heq : ENNReal.ofReal ((g.volumeMeasure (g.ball p L)).toReal / L ^ n) =
      (ENNReal.ofReal L)⁻¹ ^ n * g.volumeMeasure (g.ball p L) := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hL n), ENNReal.ofReal_toReal hfinite,
      ENNReal.ofReal_pow hL.le, div_eq_mul_inv, ENNReal.inv_pow, mul_comm]
  simpa only [Function.comp_apply, heq] using h

end PoincareConjecture.RiemannianMetric
