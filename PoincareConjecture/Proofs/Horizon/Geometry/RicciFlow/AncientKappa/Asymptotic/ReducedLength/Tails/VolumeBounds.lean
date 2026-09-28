import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.RescaledLowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.MaximalBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

open RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem one_le_dimension (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) : 1 ≤ n := by
  have hp := P.reducedLength_pos S.reference (S.base 0) (S.scale 0) (S.scale_pos 0)
  have hb := S.base_reduced_length_bound 0
  have hn : (0 : ℝ) < n := by linarith
  have : 0 < n := by exact_mod_cast hn
  omega

theorem rescaled_ball_volume_le_euclidean (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (k : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (p : M) {r : ℝ} (hr : 0 < r) :
    calibratedMetricVolume ((S.rescaling k).flow.metric (-τ))
        (((S.rescaling k).flow.metric (-τ)).ball p r) ≤
      ENNReal.ofReal (euclideanUnitBallVolume n * r ^ n) := by
  let g := (S.rescaling k).flow.metric (-τ)
  let D := (S.rescaling k).flow.connection (-τ)
  have hc : MetricComplete g := (S.rescaling k).complete (-τ) (neg_neg_of_pos hτ)
  have hRic (x : M) (v : TangentSpace (𝓡 n) x) : 0 ≤ D.ricci x v v :=
    (D.ricci_bounds_of_nonnegative_curvatureOperator D.intrinsicCurvatureTensorCalculus x
      ((S.rescaling k).nonnegative_curvature_operator (-τ) (neg_neg_of_pos hτ) x) v).1
  have h := g.ball_volume_div_pow_le_euclideanUnitBallVolume D
    (S.one_le_dimension P) hc hRic p hr
  have hreal := (div_le_iff₀ (pow_pos hr n)).mp h
  rw [calibratedMetricVolume_eq_volumeMeasure,
    ← ENNReal.ofReal_toReal (g.ball_volume_ne_top_of_metricComplete hc p r)]
  exact ENNReal.ofReal_le_ofReal hreal

end PoincareConjecture.AncientRescalingSequence
