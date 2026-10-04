import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegionNesting

/-!
# Regions of disjoint planar polygon boundaries

A connected polygon boundary avoiding another boundary lies in
one complementary region. Strict boundary nesting gives containment
of the entire closed disk in the open region. See Alexander 1924,
p. 7, Erickson pp. 2--4, 8--10 and M76 derivation 122.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- Two disjoint simple polygon boundaries are nested in one
of the other's two complementary regions. See Alexander p. 7
and M76 derivation 122. -/
theorem boundary_subset_inside_or_outside_of_disjoint {m n : ℕ}
    (P : Polygon (ℝ × ℝ) (m + 3)) (Q : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hdisj : Disjoint (P.boundary ℝ) (Q.boundary ℝ)) :
    Q.boundary ℝ ⊆ P.inside ∨ Q.boundary ℝ ⊆ P.outside := by
  apply (Q.isConnected_boundary hQ hinjQ).isPreconnected.subset_or_subset
    (P.isOpen_inside hP hinjP) (P.isOpen_outside hP hinjP) P.disjoint_inside_outside
  rw [← P.compl_boundary_eq_inside_union_outside]
  intro x hx hxb
  exact Set.disjoint_left.mp hdisj hxb hx

/-- A polygon boundary strictly inside another simple polygon
has its entire closed region there. See Alexander p. 7 and
M76 derivation 122. -/
theorem closure_inside_subset_inside_of_boundary_subset_inside {m n : ℕ}
    (P : Polygon (ℝ × ℝ) (m + 3)) (Q : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hboundary : Q.boundary ℝ ⊆ P.inside) : closure Q.inside ⊆ P.inside := by
  rw [closure_eq_self_union_frontier, Q.frontier_inside hQ hinjQ]
  exact union_subset
    (P.inside_subset_inside_of_boundary_subset Q hP hinjP hQ hinjQ
      (hboundary.trans subset_closure)) hboundary

end Polygon
