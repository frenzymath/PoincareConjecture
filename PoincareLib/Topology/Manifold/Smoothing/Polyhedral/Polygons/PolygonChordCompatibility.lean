import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonLocalEdges

/-!
# Compatibility of an interior diagonal with polygon edges

A segment joining two polygon vertices and meeting the boundary
only at these endpoints satisfies the simplicial intersection law
with every polygon edge. See Erickson, Simple Polygons, pp. 8--9
and M76 derivation 104.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- A chord avoiding the boundary except at its endpoints is
simplicially compatible with every edge. See M76 derivation 104. -/
theorem chord_inter_edge (P : Polygon E n) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (a b : Fin n)
    (hchord : segment ℝ (P a) (P b) ∩ P.boundary ℝ ⊆ {P a, P b}) (j : Fin n) :
    segment ℝ (P a) (P b) ∩ P.edgeSet ℝ j ⊆
      convexHull ℝ ({P a, P b} ∩ (P.edgeVertices j : Set E)) := by
  classical
  intro x hx
  have hxend := hchord ⟨hx.1, mem_iUnion.mpr ⟨j, hx.2⟩⟩
  rcases hxend with rfl | hxend
  · apply subset_convexHull ℝ _
    refine ⟨by simp, ?_⟩
    have hi := (P.vertex_mem_edgeSet_iff hP hinj a j).mp hx.2
    rcases hi with rfl | hi
    · simp [edgeVertices]
    · simp [edgeVertices, hi]
  · have hxb : x = P b := hxend
    subst x
    apply subset_convexHull ℝ _
    refine ⟨by simp, ?_⟩
    have hi := (P.vertex_mem_edgeSet_iff hP hinj b j).mp hx.2
    rcases hi with rfl | hi
    · simp [edgeVertices]
    · simp [edgeVertices, hi]

/-- Adding one compatible chord to the available edge pairs
preserves the simplicial intersection law for any two selected
pairs. See Erickson pp. 8--9 and M76 derivation 104. -/
theorem convexHull_inter_of_edges_or_chord (P : Polygon E n)
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (a b : Fin n)
    (hchord : segment ℝ (P a) (P b) ∩ P.boundary ℝ ⊆ {P a, P b})
    {s t : Set E}
    (hs : (∃ i, s = (P.edgeVertices i : Set E)) ∨ s = {P a, P b})
    (ht : (∃ i, t = (P.edgeVertices i : Set E)) ∨ t = {P a, P b}) :
    convexHull ℝ s ∩ convexHull ℝ t ⊆ convexHull ℝ (s ∩ t) := by
  rcases hs with ⟨i, rfl⟩ | rfl <;> rcases ht with ⟨j, rfl⟩ | rfl
  · simpa only [← edgeSet_eq_convexHull] using hP i j
  · simpa only [convexHull_pair, ← edgeSet_eq_convexHull, inter_comm] using
      P.chord_inter_edge hP hinj a b hchord i
  · simpa only [convexHull_pair, ← edgeSet_eq_convexHull] using
      P.chord_inter_edge hP hinj a b hchord j
  · simp only [inter_self, Subset.rfl]

/-- A new cycle made entirely of original edges and one compatible
chord inherits the simplicial edge law. Distinctness of its vertices
is a separate assertion. See M76 derivation 104. -/
theorem hasSimplicialEdges_of_edges_or_chord (P : Polygon E n)
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (a b : Fin n)
    (hchord : segment ℝ (P a) (P b) ∩ P.boundary ℝ ⊆ {P a, P b})
    {m : ℕ} (Q : Polygon E m)
    (hQ : ∀ i, (∃ j, (Q.edgeVertices i : Set E) = (P.edgeVertices j : Set E)) ∨
      (Q.edgeVertices i : Set E) = {P a, P b}) : Q.HasSimplicialEdges := by
  intro i j
  rw [Q.edgeSet_eq_convexHull, Q.edgeSet_eq_convexHull]
  exact P.convexHull_inter_of_edges_or_chord hP hinj a b hchord (hQ i) (hQ j)

end Polygon
