import PoincareConjecture.Proofs.M10.SmoothMetric
import PoincareConjecture.Proofs.M10.MetricInverse

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem backwardMetricCoordinates_apply_symm (q₀ : M) (w : M × ℝ)
    (hw : w.1 ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q₀).baseSet) (u v : EuclideanSpace ℝ (Fin n)) :
    backwardMetricCoordinates F T q₀ w u v =
      (F.metric (T - w.2)).inner w.1
        ((trivializationAt (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n)) q₀).symmL ℝ w.1 u)
        ((trivializationAt (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n)) q₀).symmL ℝ w.1 v) := by
  have h := backwardMetricCoordinates_apply (F := F) (T := T) q₀ w hw
    ((trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q₀).symmL ℝ w.1 u)
    ((trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q₀).symmL ℝ w.1 v)
  simpa only [Bundle.Trivialization.continuousLinearMapAt_symmL _ hw] using h

theorem backwardMetricCoordinates_symm (q₀ : M) (w : M × ℝ)
    (hw : w.1 ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q₀).baseSet) (u v : EuclideanSpace ℝ (Fin n)) :
    backwardMetricCoordinates F T q₀ w u v = backwardMetricCoordinates F T q₀ w v u := by
  rw [backwardMetricCoordinates_apply_symm q₀ w hw,
    backwardMetricCoordinates_apply_symm q₀ w hw]
  exact (F.metric (T - w.2)).symm w.1 _ _

theorem backwardMetricCoordinates_pos (q₀ : M) (w : M × ℝ)
    (hw : w.1 ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q₀).baseSet) (u : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0) :
    0 < backwardMetricCoordinates F T q₀ w u u := by
  rw [backwardMetricCoordinates_apply_symm q₀ w hw]
  apply (F.metric (T - w.2)).pos w.1 _
  intro hz
  have h := congrArg ((trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) q₀).continuousLinearMapAt ℝ w.1) hz
  rw [Bundle.Trivialization.continuousLinearMapAt_symmL _ hw, map_zero] at h
  exact hu h

theorem coordinateBackwardMetric_symm (q₀ : M) (w : EuclideanSpace ℝ (Fin n) × ℝ)
    (hw : w.1 ∈ (extChartAt (𝓡 n) q₀).target) (u v : EuclideanSpace ℝ (Fin n)) :
    coordinateBackwardMetric F T q₀ w u v = coordinateBackwardMetric F T q₀ w v u := by
  apply backwardMetricCoordinates_symm q₀ ((extChartAt (𝓡 n) q₀).symm w.1, w.2)
  simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
    (extChartAt (𝓡 n) q₀).map_target hw

theorem coordinateBackwardMetric_isInvertible (q₀ : M)
    (w : EuclideanSpace ℝ (Fin n) × ℝ)
    (hw : w.1 ∈ (extChartAt (𝓡 n) q₀).target) :
    (coordinateBackwardMetric F T q₀ w).IsInvertible := by
  apply positive_bilinear_isInvertible
  intro u hu
  apply backwardMetricCoordinates_pos q₀ ((extChartAt (𝓡 n) q₀).symm w.1, w.2) _ u hu
  simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
    (extChartAt (𝓡 n) q₀).map_target hw

end PoincareConjecture.M10
