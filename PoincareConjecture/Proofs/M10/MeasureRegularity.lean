import PoincareConjecture.Proofs.M10.RegularImage
import PoincareConjecture.Proofs.M10.SpacetimeLipschitz
import PoincareConjecture.Proofs.M10.ContactBounds









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}


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

end PoincareConjecture.M10
