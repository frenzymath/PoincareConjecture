import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal
universe u
namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

private theorem comparison_factors_pos :
    0 < N.scale * Real.sqrt (1 - N.epsilon) ∧
      0 < N.scale * Real.sqrt (1 + N.epsilon) := by
  constructor
  · exact mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  · exact mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_pos]))

private theorem comparison_quadratic_bounds :
    ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
      (N.scale * Real.sqrt (1 - N.epsilon)) ^ 2 * EvolvingRoundCylinderMetric 0 z v v ≤
          roundCylinderPullback g N.coordinate_map z v v ∧
        roundCylinderPullback g N.coordinate_map z v v ≤
          (N.scale * Real.sqrt (1 + N.epsilon)) ^ 2 * EvolvingRoundCylinderMetric 0 z v v := by
  intro z hz v
  have hlo : (N.scale * Real.sqrt (1 - N.epsilon)) ^ 2 =
      (1 - N.epsilon) * N.scale ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_lt_half])]
    ring
  have hhi : (N.scale * Real.sqrt (1 + N.epsilon)) ^ 2 =
      (1 + N.epsilon) * N.scale ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos])]
    ring
  simpa only [hlo, hhi] using N.pullback_metric_bounds hz.2 v

theorem intrinsicEDist_bounds {z w : RoundCylinderSpace}
    (hz : z ∈ N.cylinderDomain) (hw : w ∈ N.cylinderDomain) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) *
        N.cylinderIntrinsicEDist z w ≤
      intrinsicEDist g N.carrier (N.coordinate_map z) (N.coordinate_map w) ∧
    intrinsicEDist g N.carrier (N.coordinate_map z) (N.coordinate_map w) ≤
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon)) *
        N.cylinderIntrinsicEDist z w := by
  exact N.intrinsicEDist_bounds_of_quadratic (N.comparison_factors_pos).1
    (N.comparison_factors_pos).2 N.comparison_quadratic_bounds hz hw

theorem volumeMeasure_image_bounds {A : Set RoundCylinderSpace}
    (hA : MeasurableSet A) (hAN : A ⊆ N.cylinderDomain) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
        roundCylinderVolumeMeasure A ≤ g.volumeMeasure (N.coordinate_map '' A) ∧
      g.volumeMeasure (N.coordinate_map '' A) ≤
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon)) ^ 3 *
          roundCylinderVolumeMeasure A := by
  exact N.volume_bounds_of_quadratic (N.comparison_factors_pos).1
    (N.comparison_factors_pos).2 N.comparison_quadratic_bounds hA hAN

end PoincareConjecture.EpsilonNeck
