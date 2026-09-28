import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Integral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedTotalCurvature

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

theorem integral_scalarCurvature_le_eight_pi
    {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [T3Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [CompactSpace S] [ConnectedSpace S]
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ 8 * Real.pi := by
  obtain ⟨T⟩ := Topology.Surface.exists_finite_smooth_triangulation_with_retained_coordinates
    (M := S)
  exact T.integral_scalarCurvature_le_eight_pi_of_length_lt_one D T.length_lt_one

end PoincareConjecture.LeviCivitaData
