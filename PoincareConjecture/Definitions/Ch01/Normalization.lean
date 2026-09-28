import PoincareConjecture.Definitions.Ch01.Curvature
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

noncomputable def euclideanUnitBallLebesgueVolume : ℝ≥0∞ :=
  MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)

noncomputable def euclideanUnitBallHausdorffVolume : ℝ≥0∞ :=
  MeasureTheory.Measure.hausdorffMeasure (3 : ℝ)
    (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)

noncomputable def euclideanHausdorffCalibration : ℝ≥0∞ :=
  euclideanUnitBallLebesgueVolume / euclideanUnitBallHausdorffVolume

noncomputable def RiemannianMetric.hausdorffVolume
    (g : RiemannianMetric 3 M) : @MeasureTheory.Measure M inferInstance :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  MeasureTheory.Measure.hausdorffMeasure (3 : ℝ)

noncomputable def normalizedMetricVolume (g : RiemannianMetric 3 M) :
    @MeasureTheory.Measure M inferInstance :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  euclideanHausdorffCalibration • g.hausdorffVolume

def normalizedMetricComplete (g : RiemannianMetric 3 M) : Prop :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  CompleteSpace M

structure NormalizedInitialMetric where
  metric : RiemannianMetric 3 M
  connection : LeviCivitaData metric
  volumeMeasure : @MeasureTheory.Measure M inferInstance
  volume_is_normalized_metric :
    volumeMeasure = normalizedMetricVolume metric
  full_curvature_bound :
    ∀ x : M, connection.curvatureTensorNorm x ≤ 1
  small_ball_lower_bound :
    ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 ≤
        volumeMeasure (metric.ball x r)
  volume_finite : volumeMeasure Set.univ < ⊤
  complete : normalizedMetricComplete metric

end PoincareConjecture
