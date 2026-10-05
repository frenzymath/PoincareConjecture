import PoincareLib.Geometry.Riemannian.Surface.Regularity
import PoincareLib.Geometry.Riemannian.Measure.LocalFinite

/-!
# Integrability of curvature on compact surfaces

The intrinsic Riemannian volume is locally finite. Compactness and continuity
therefore make scalar curvature and both its nonnegative parts integrable.
These facts hold in every dimension, including nonorientable manifolds.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Scalar curvature is integrable for intrinsic volume on a compact manifold. -/
theorem integrable_scalarCurvature (D : LeviCivitaData g) :
    Integrable D.scalarCurvature g.volumeMeasure :=
  g.integrable_volumeMeasure_of_hasCompactSupport D.continuous_scalarCurvature
    (HasCompactSupport.of_compactSpace _)

/-- The positive part of scalar curvature is integrable on a compact manifold. -/
theorem integrable_scalarCurvature_posPart (D : LeviCivitaData g) :
    Integrable (fun x => max 0 (D.scalarCurvature x)) g.volumeMeasure :=
  g.integrable_volumeMeasure_of_hasCompactSupport
    (continuous_const.max D.continuous_scalarCurvature)
    (HasCompactSupport.of_compactSpace _)

/-- The negative part of scalar curvature is integrable on a compact manifold. -/
theorem integrable_scalarCurvature_negPart (D : LeviCivitaData g) :
    Integrable (fun x => max 0 (-D.scalarCurvature x)) g.volumeMeasure :=
  g.integrable_volumeMeasure_of_hasCompactSupport
    (continuous_const.max D.continuous_scalarCurvature.neg)
    (HasCompactSupport.of_compactSpace _)

end PoincareMT.LeviCivitaData
