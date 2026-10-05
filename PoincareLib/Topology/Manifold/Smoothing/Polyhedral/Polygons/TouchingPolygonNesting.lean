import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PuncturedPolygonBoundary
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegionNesting

/-!
# Nesting for polygon boundaries meeting at one point

The punctured boundary lies on one side of the other polygon.
Density then gives either inside containment or avoidance of
the first open inside. See Alexander 1924, p. 7 and M76
derivation 151.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- When two simple polygon boundaries meet only at one point,
the second punctured boundary lies entirely inside or outside
the first. See Alexander p. 7 and M76 derivation 151. -/
theorem boundary_sdiff_subset_inside_or_outside {m n : ℕ}
    (P : Polygon (ℝ × ℝ) (m + 3)) (Q : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q) (q : ℝ × ℝ)
    (hinter : P.boundary ℝ ∩ Q.boundary ℝ ⊆ {q}) :
    Q.boundary ℝ \ {q} ⊆ P.inside ∨ Q.boundary ℝ \ {q} ⊆ P.outside := by
  apply (Q.isConnected_boundary_sdiff_singleton hQ hinjQ q).isPreconnected.subset_or_subset
    (P.isOpen_inside hP hinjP) (P.isOpen_outside hP hinjP) P.disjoint_inside_outside
  rw [← P.compl_boundary_eq_inside_union_outside]
  rintro x ⟨hxQ, hxq⟩ hxP
  exact hxq (hinter ⟨hxP, hxQ⟩)

/-- Two simple polygon boundaries meeting only at one point
give either inclusion of the second inside in the first or
avoidance of the first open inside by the whole second boundary.
See Alexander p. 7 and M76 derivation 151. -/
theorem inside_subset_or_disjoint_boundary_of_singleton_inter {m n : ℕ}
    (P : Polygon (ℝ × ℝ) (m + 3)) (Q : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q) (q : ℝ × ℝ)
    (hinter : P.boundary ℝ ∩ Q.boundary ℝ ⊆ {q}) :
    Q.inside ⊆ P.inside ∨ Disjoint P.inside (Q.boundary ℝ) := by
  rcases P.boundary_sdiff_subset_inside_or_outside Q hP hinjP hQ hinjQ q hinter with hi | ho
  · have hboundary : Q.boundary ℝ ⊆ closure P.inside := by
      rw [← Q.closure_boundary_sdiff_singleton hQ hinjQ q]
      exact closure_mono hi
    exact Or.inl (P.inside_subset_inside_of_boundary_subset Q hP hinjP hQ hinjQ hboundary)
  · have hboundary : Q.boundary ℝ ⊆ closure P.outside := by
      rw [← Q.closure_boundary_sdiff_singleton hQ hinjQ q]
      exact closure_mono ho
    exact Or.inr ((P.disjoint_inside_outside.closure_right
      (P.isOpen_inside hP hinjP)).mono_right hboundary)

end Polygon
