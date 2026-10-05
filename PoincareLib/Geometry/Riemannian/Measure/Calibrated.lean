import PoincareLib.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Calibrated Riemannian volume

Adapted from Mapher, `PoincareMT/Definitions/Ch06/ReducedVolume.lean`, commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Declaration bodies are retained; only the required definition closure is imported.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareMT

/-- Euclidean calibration of the diameter-power Hausdorff measure. -/
noncomputable def euclideanVolumeCalibration (n : ℕ) : ℝ≥0∞ :=
  MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) /
    MeasureTheory.Measure.hausdorffMeasure (n : ℝ)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- Riemannian volume, normalized to Euclidean Lebesgue volume. -/
noncomputable def calibratedMetricVolume [MeasurableSpace M] [BorelSpace M]
    [T3Space M] (g : RiemannianMetric n M) : MeasureTheory.Measure M :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  euclideanVolumeCalibration n • MeasureTheory.Measure.hausdorffMeasure (n : ℝ)

end PoincareMT

