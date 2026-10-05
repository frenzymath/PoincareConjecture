import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricSubdivision
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedSurfacePurity
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedSurfaceIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedVertexLinkConnected
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedStarLinks

/-!
# Surface incidence for the actual barycentric subdivision

The actual centroid subdivision preserves pure triangular
cofaces, paired edge cofaces and connected original vertex links.
Distinct original stars meet inside their links. See Hudson 1969,
pp. 8--9, Alexander 1924, pp. 6--8 and M76 derivation 271.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

/-- Barycentric subdivision preserves pure triangular cofaces.
See Hudson pp. 8--9 and M76 derivation 271. -/
theorem barycentricSubdivision_pure_triangles
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    ∀ s ∈ K.barycentricSubdivision.faces,
      ∃ t ∈ K.barycentricSubdivision.faces, t.card = 3 ∧ s ⊆ t := by
  unfold barycentricSubdivision
  exact K.derivedSubdivision_pure_triangles _ _ hpure

/-- Barycentric subdivision preserves paired triangular
cofaces at every edge. See Hudson pp. 8--9 and derivation 271. -/
theorem barycentricSubdivision_two_triangle_cofaces
    (hbound : ∀ u ∈ K.faces, u.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {u : Finset E | u ∈ K.faces ∧ u.card = 3 ∧ e ⊆ u}.ncard = 2) :
    ∀ e ∈ K.barycentricSubdivision.faces, e.card = 2 →
      {u : Finset E | u ∈ K.barycentricSubdivision.faces ∧
        u.card = 3 ∧ e ⊆ u}.ncard = 2 := by
  unfold barycentricSubdivision
  exact K.derivedSubdivision_two_triangle_cofaces _ _ hbound hcofaces

/-- Every original vertex remains a vertex after barycentric
subdivision. See Hudson pp. 8--9 and M76 derivation 271. -/
theorem vertices_subset_barycentricSubdivision_vertices :
    K.vertices ⊆ K.barycentricSubdivision.vertices := by
  intro p hp
  unfold barycentricSubdivision
  rw [K.derivedSubdivision_vertices_eq_range]
  exact ⟨⟨{p}, hp⟩, Finset.centroid_singleton ℝ id p⟩

variable [DecidableEq E]

/-- The actual original-vertex link stays connected under
barycentric subdivision. See Hudson pp. 8--9 and derivation 271. -/
theorem isConnected_barycentric_original_vertex_link {p : E}
    (hp : {p} ∈ K.faces) (hconn : IsConnected (K.link p).space) :
    IsConnected (K.barycentricSubdivision.link p).space := by
  unfold barycentricSubdivision
  exact K.isConnected_derived_original_vertex_link _ _ hp hconn

/-- Shared original-vertex barycentric stars lie in both
literal links. See Hudson pp. 8--9 and M76 derivation 271. -/
theorem barycentric_closedStars_inter_subset_links {p q : E}
    (hp : {p} ∈ K.faces) (hq : {q} ∈ K.faces) (hpq : p ≠ q) :
    (K.barycentricSubdivision.closedStar p).space ∩
        (K.barycentricSubdivision.closedStar q).space ⊆
      (K.barycentricSubdivision.link p).space ∩
        (K.barycentricSubdivision.link q).space := by
  unfold barycentricSubdivision
  exact K.derived_closedStars_inter_subset_links _ _ hp hq hpq

end Geometry.SimplicialComplex
