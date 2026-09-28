import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite








set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem integrable_scalarCurvature (D : LeviCivitaData g) :
    Integrable D.scalarCurvature g.volumeMeasure :=
  g.integrable_volumeMeasure_of_hasCompactSupport D.continuous_scalarCurvature
    (HasCompactSupport.of_compactSpace _)


theorem integrable_scalarCurvature_posPart (D : LeviCivitaData g) :
    Integrable (fun x => max 0 (D.scalarCurvature x)) g.volumeMeasure :=
  g.integrable_volumeMeasure_of_hasCompactSupport
    (continuous_const.max D.continuous_scalarCurvature)
    (HasCompactSupport.of_compactSpace _)


theorem integrable_scalarCurvature_negPart (D : LeviCivitaData g) :
    Integrable (fun x => max 0 (-D.scalarCurvature x)) g.volumeMeasure :=
  g.integrable_volumeMeasure_of_hasCompactSupport
    (continuous_const.max D.continuous_scalarCurvature.neg)
    (HasCompactSupport.of_compactSpace _)

end PoincareConjecture.LeviCivitaData
