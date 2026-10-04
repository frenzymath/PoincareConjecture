import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplicialPolygon
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonReindex

/-!
# Finite frugal geometric triangulations of polygon regions

The carrier is the canonical closed inside, the original edges
remain faces, no new vertices are introduced, and every face has
a triangular coface. See Erickson, Simple Polygons, pp. 6--9
and M76 derivation 114.
-/

set_option autoImplicit false

open Set Geometry

namespace Polygon

/-- A finite pure geometric triangulation of the closed polygon
inside, retaining all original edges and using only its vertices.
This is a frugal triangulation in Erickson pp. 6--9; see derivation 114. -/
structure IsTriangulation {n : ℕ} (P : Polygon (ℝ × ℝ) n)
    (K : SimplicialComplex ℝ (ℝ × ℝ)) : Prop where
  /-- Finitely many simplices suffice. -/
  finite_faces : K.faces.Finite
  /-- The geometric carrier is the entire closed inside. -/
  space_eq : K.space = closure P.inside
  /-- No auxiliary vertices are introduced. -/
  vertices_subset : K.vertices ⊆ range P
  /-- Every polygon edge is an unsplit face. -/
  edge_mem : ∀ i, P.edgeVertices i ∈ K.faces
  /-- Every face has a triangular coface. -/
  pure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3

/-- A frugal triangulation has exactly the original vertices:
retaining the polygon edges supplies the reverse inclusion.
See M76 derivation 114. -/
theorem IsTriangulation.vertices_eq {n : ℕ} {P : Polygon (ℝ × ℝ) n}
    {K : SimplicialComplex ℝ (ℝ × ℝ)} (h : P.IsTriangulation K) : K.vertices = range P := by
  classical
  apply Subset.antisymm h.vertices_subset
  rintro x ⟨i, rfl⟩
  apply K.down_closed (h.edge_mem i) _ (Finset.singleton_nonempty _)
  simp [edgeVertices]

/-- A cyclic relabeling changes neither a polygon's triangulation
nor its geometric carrier. See M76 derivation 114. -/
theorem IsTriangulation.of_reindex {m n : ℕ} {P : Polygon (ℝ × ℝ) n}
    {K : SimplicialComplex ℝ (ℝ × ℝ)} (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i))
    (h : (P.reindex e).IsTriangulation K) : P.IsTriangulation K := by
  refine ⟨h.finite_faces, ?_, ?_, ?_, h.pure⟩
  · rw [h.space_eq, P.inside_reindex e he]
  · intro x hx
    obtain ⟨i, rfl⟩ := h.vertices_subset hx
    exact mem_range_self (e i)
  · intro i
    have hi := h.edge_mem (e.symm i)
    rwa [P.edgeVertices_reindex e he, e.apply_symm_apply] at hi

end Polygon
