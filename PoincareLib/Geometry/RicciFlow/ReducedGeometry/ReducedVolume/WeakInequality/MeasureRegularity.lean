import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.AlmostEverywhere.RegularImage
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.Lipschitz.SpacetimeLipschitz
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.Continuity.ContactBounds

/-!
# The complete reduced-length measure-regularity output

Morgan-Tian Corollary 6.67, Claims 6.68-6.69, Proposition 7.5 and
Corollary 7.6 give the one open regular spacetime image, every-slice nullity,
full-window continuity and local Lipschitz regularity, and derivative bounds.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

/-- The L-geodesic and differential theories produce all eight measure-regularity fields. -/
theorem reducedLength_measure_regularity
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (p : M) :
    Nonempty (ReducedLengthMeasureData F T τmax p) := by
  obtain ⟨G⟩ := hDifferential.exponential_geometry p
  exact ⟨{
    regularDomain := G.regularImage
    regularDomain_open := G.regular_chart.open_target
    regularDomain_time := G.regular_target_times
    regular_points := fun z hz ↦ ⟨G.regular_point z hz⟩
    slice_complement_null := fun _ hτ hmax ↦
      regularImage_slice_complement_eq_zero hL hDifferential hwindow G hτ hmax
    continuous := reducedLength_continuousOn hL hDifferential p
    locally_lipschitz := reducedLength_locallyLipschitz hL hDifferential hwindow p
    local_derivative_bounds := reducedLength_local_derivative_bounds hDifferential G }⟩

end PoincareMT.ReducedVolume
