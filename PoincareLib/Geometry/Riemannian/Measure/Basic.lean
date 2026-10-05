import PoincareLib.Geometry.Riemannian.Metric
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The measure induced by a Riemannian metric

The normalized Hausdorff measure uses the intrinsic distance of the retained
metric. Its identification with the coordinate volume density is a separate
geometric theorem.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- Normalized Hausdorff volume for the emetric induced by `g`.

`euclideanHausdorffMeasure` agrees with Lebesgue volume on Euclidean space,
which fixes the normalization needed for the one-dimensional Gaussian case.
-/
noncomputable def volumeMeasure (g : RiemannianMetric n M) : Measure M :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  Measure.euclideanHausdorffMeasure n

end PoincareMT.RiemannianMetric
