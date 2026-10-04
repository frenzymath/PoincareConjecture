import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplicialPolygon

/-!
# Relabeling a polygon in cyclic order

Equivalences commuting with cyclic successor preserve the edges,
boundary, inside and simplicial intersection law. See Erickson,
Simple Polygons, pp. 8--9 and M76 derivation 112.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} {m n : ℕ}

/-- Relabel a polygon by an equivalence of its finite index sets.
Preserving its geometry requires successor compatibility below.
See M76 derivation 112. -/
def reindex (P : Polygon E n) (e : Fin m ≃ Fin n) : Polygon E m := ⟨P ∘ e⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cyclic relabeling preserves each labeled edge segment.
See M76 derivation 112. -/
theorem edgeSet_reindex (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i)) (i : Fin m) :
    (P.reindex e).edgeSet ℝ i = P.edgeSet ℝ (e i) := by
  change affineSegment ℝ (P (e i)) (P (e (finRotate m i))) = _
  rw [he]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Cyclic relabeling preserves each edge's endpoint set.
See M76 derivation 112. -/
theorem edgeVertices_reindex (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i)) (i : Fin m) :
    (P.reindex e).edgeVertices i = P.edgeVertices (e i) := by
  classical
  simp only [edgeVertices, reindex, Function.comp_apply, he]

/-- Cyclic relabeling preserves the entire boundary.
See Erickson pp. 8--9 and M76 derivation 112. -/
theorem boundary_reindex (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i)) :
    (P.reindex e).boundary ℝ = P.boundary ℝ := by
  simp only [boundary, P.edgeSet_reindex e he]
  exact e.surjective.iUnion_comp _

/-- Cyclic relabeling preserves the simplicial intersection law.
See M76 derivation 112. -/
theorem hasSimplicialEdges_reindex (P : Polygon E n) (hP : P.HasSimplicialEdges)
    (e : Fin m ≃ Fin n) (he : ∀ i, e (finRotate m i) = finRotate n (e i)) :
    (P.reindex e).HasSimplicialEdges := by
  intro i j
  simpa only [P.edgeSet_reindex e he, P.edgeVertices_reindex e he] using hP (e i) (e j)

/-- Cyclic relabeling preserves the canonical inside, even for
degenerate polygons. See M76 derivation 112. -/
theorem inside_reindex (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i)) :
    (P.reindex e).inside = P.inside := by
  simp only [inside, P.boundary_reindex e he]

end Polygon
