import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import Mathlib.Topology.Algebra.Order.Field









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M]



theorem tendsto_ball_volume_div_pow_zero_of_compact (g : RiemannianMetric n M)
    (hn : 0 < n) (p : M) :
    Tendsto (fun r : ℝ => (g.volumeMeasure (g.ball p r)).toReal / r ^ n)
      atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero (b := 0)
    (B := (g.volumeMeasure univ).toReal)
  · exact Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  · exact Eventually.of_forall fun _ =>
      ENNReal.toReal_mono (g.volumeMeasure_lt_top_of_isCompact isCompact_univ).ne
        (measure_mono (subset_univ _))
  · exact tendsto_pow_atTop hn.ne'

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.AncientKappaSolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  [CompactSpace M]



theorem asymptotic_volume_ratio_zero_of_compact (K : AncientKappaSolution n M)
    (hcalculus : (K.flow.connection 0).CurvatureTensorCalculus) :
    AncientAsymptoticVolumeRatioZero K := by
  have hn : 0 < n := lt_of_lt_of_le (by norm_num) (K.two_le_dimension hcalculus)
  intro t ht p
  exact (K.flow.metric t).calibrated_asymptoticVolumeRatio_eq_zero_of_tendsto p
    (fun r _ => ((K.flow.metric t).volumeMeasure_ball_lt_top (K.complete t ht) p r).ne)
    ((K.flow.metric t).tendsto_ball_volume_div_pow_zero_of_compact hn p)

end PoincareConjecture.AncientKappaSolution
