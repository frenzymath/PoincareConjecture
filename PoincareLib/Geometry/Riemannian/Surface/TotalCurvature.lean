import PoincareLib.Geometry.Riemannian.Surface.Curvature
import PoincareLib.Geometry.Riemannian.Surface.Integral
import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.RetainedTotalCurvature

/-!
# Total scalar curvature of closed surfaces

Petrunin, *An upper bound for the curvature integral*, Section 4.4,
author manuscript p. 8. The constructed coordinate triangulation, complete
metric vertex fans and Euler-characteristic bound give the intrinsic integral
estimate for every connected compact smooth surface, including nonorientable ones.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

/-- The intrinsic total scalar curvature of a connected closed surface is at most `8π`. -/
theorem integral_scalarCurvature_le_eight_pi
    {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [T3Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [CompactSpace S] [ConnectedSpace S]
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ 8 * Real.pi := by
  obtain ⟨T⟩ := Topology.Surface.exists_finite_smooth_triangulation_with_retained_coordinates
    (M := S)
  exact T.integral_scalarCurvature_le_eight_pi_of_length_lt_one D T.length_lt_one

end PoincareMT.LeviCivitaData
