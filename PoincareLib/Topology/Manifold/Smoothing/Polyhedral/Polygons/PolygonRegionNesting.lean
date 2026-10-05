import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegions

/-!
# Nesting and intersections of polygon regions

Boundary containment in a closed inside implies containment
of insides. Disjoint open insides have closed intersection
equal to their common boundary. See Erickson, Simple Polygons,
pp. 8--9 and M76 derivation 102.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- An unbounded preconnected set avoiding the boundary lies
in the polygon's outside. Simplicity is not needed.
See M76 derivation 102. -/
theorem subset_outside_of_unbounded_preconnected {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (P : Polygon E n)
    {S : Set E} (hS : IsPreconnected S) (hsub : S ⊆ (P.boundary ℝ)ᶜ)
    (hunbounded : ¬ Bornology.IsBounded S) : S ⊆ P.outside := by
  intro q hq
  refine ⟨hsub hq, fun h => hunbounded ?_⟩
  exact h.subset (hS.subset_connectedComponentIn hq hsub)

/-- A polygon whose boundary lies in another simple polygon's
closed inside has an outside containing that polygon's outside.
See Erickson pp. 8--9 and M76 derivation 102. -/
theorem outside_subset_outside_of_boundary_subset {n m : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (Q : Polygon (ℝ × ℝ) m)
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hboundary : Q.boundary ℝ ⊆ closure P.inside) : P.outside ⊆ Q.outside := by
  apply Q.subset_outside_of_unbounded_preconnected
    (P.isConnected_outside hP hinj).isPreconnected _ (P.not_isBounded_outside hP hinj)
  intro q hq hqQ
  have hqcl := hboundary hqQ
  rw [P.closure_inside hP hinj] at hqcl
  exact hqcl hq

/-- Containment of a simple polygon's boundary in another's
closed inside implies containment of their open insides.
See Erickson pp. 8--9 and M76 derivation 102. -/
theorem inside_subset_inside_of_boundary_subset {n m : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (Q : Polygon (ℝ × ℝ) (m + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hboundary : Q.boundary ℝ ⊆ closure P.inside) : Q.inside ⊆ P.inside := by
  have hout := P.outside_subset_outside_of_boundary_subset Q hP hinjP hboundary
  have hclosed : Q.inside ⊆ closure P.inside := by
    rw [P.closure_inside hP hinjP]
    intro q hq hqP
    exact Set.disjoint_left.mp Q.disjoint_inside_outside hq (hout hqP)
  have h := interior_maximal hclosed (Q.isOpen_inside hQ hinjQ)
  rwa [P.interior_closure_inside hP hinjP] at h

/-- Disjoint polygon insides have closed intersection equal to
their boundary intersection. See Erickson pp. 8--9 and derivation 102. -/
theorem closure_inside_inter_eq_boundary_inter {n m : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (Q : Polygon (ℝ × ℝ) (m + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hdis : Disjoint P.inside Q.inside) :
    closure P.inside ∩ closure Q.inside = P.boundary ℝ ∩ Q.boundary ℝ := by
  rw [← P.frontier_inside hP hinjP, ← Q.frontier_inside hQ hinjQ]
  apply Subset.antisymm
  · intro q hq
    refine ⟨⟨hq.1, ?_⟩, ⟨hq.2, ?_⟩⟩
    · intro hi
      exact Set.disjoint_left.mp (hdis.closure_right (P.isOpen_inside hP hinjP))
        (interior_subset hi) hq.2
    · intro hi
      exact Set.disjoint_left.mp (hdis.closure_left (Q.isOpen_inside hQ hinjQ))
        hq.1 (interior_subset hi)
  · exact inter_subset_inter frontier_subset_closure frontier_subset_closure

end Polygon
