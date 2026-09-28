import PoincareConjecture.Proofs.M63.Mathlib.PeriodicConcatenation
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.MinimizingGeodesicSide
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.ProfileBase











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {N : ℕ}



noncomputable def geodesicPolygonOfSides (hN : 0 < N) (vertices : Polygon M N)
    (side : ∀ j : Fin N, M63MinimizingGeodesicSide g D (m63CellLength N)
      (vertices j) (vertices (finRotate N j))) : M63GeodesicPolygon g D N := by
  let h := exists_continuous_periodic_concat hN (m63CellLength_pos hN)
    (fun j => (side j).map)
    (fun j => (side j).smooth.continuousOn.mono (side j).interval_subset)
    (fun j => (side j).finish.trans (side (finRotate N j)).start.symm)
  exact {
    vertices := vertices
    side := side
    map := h.choose
    continuous := h.choose_spec.1
    periodic := by
      simpa only [m63_count_mul_cellLength hN, curvePeriod] using h.choose_spec.2.1
    cell_agreement := h.choose_spec.2.2 }




theorem geodesicPolygon_nonempty_of_precompact_balls [T2Space M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hN : 0 < N)
    (vertices : Polygon M N) (R : Fin N → ℝ) (hR : ∀ j, 0 < R j)
    (hcompact : ∀ j, IsCompact (closure (g.ball (vertices j) (R j))))
    (hnext : ∀ j, vertices (finRotate N j) ∈ g.ball (vertices j) (R j)) :
    ∃ polygon : M63GeodesicPolygon g D N, polygon.vertices = vertices := by
  let side (j : Fin N) := Classical.choice (minimizingGeodesicSide_nonempty g D
    (m63CellLength_pos hN) (vertices j) (vertices (finRotate N j))
    (hR j) (hcompact j) (hnext j))
  exact ⟨geodesicPolygonOfSides hN vertices side, rfl⟩

end PoincareConjecture.M63
