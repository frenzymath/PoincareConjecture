import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.DerivedSurfacePurity
import PoincareConjecture.Proofs.M76.Mathlib.DerivedSurfaceIncidence
import PoincareConjecture.Proofs.M76.Mathlib.DerivedVertexLinkConnected
import PoincareConjecture.Proofs.M76.Mathlib.DerivedStarLinks










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]



theorem barycentricSubdivision_pure_triangles
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    ∀ s ∈ K.barycentricSubdivision.faces,
      ∃ t ∈ K.barycentricSubdivision.faces, t.card = 3 ∧ s ⊆ t := by
  unfold barycentricSubdivision
  exact K.derivedSubdivision_pure_triangles _ _ hpure



theorem barycentricSubdivision_two_triangle_cofaces
    (hbound : ∀ u ∈ K.faces, u.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {u : Finset E | u ∈ K.faces ∧ u.card = 3 ∧ e ⊆ u}.ncard = 2) :
    ∀ e ∈ K.barycentricSubdivision.faces, e.card = 2 →
      {u : Finset E | u ∈ K.barycentricSubdivision.faces ∧
        u.card = 3 ∧ e ⊆ u}.ncard = 2 := by
  unfold barycentricSubdivision
  exact K.derivedSubdivision_two_triangle_cofaces _ _ hbound hcofaces



theorem vertices_subset_barycentricSubdivision_vertices :
    K.vertices ⊆ K.barycentricSubdivision.vertices := by
  intro p hp
  unfold barycentricSubdivision
  rw [K.derivedSubdivision_vertices_eq_range]
  exact ⟨⟨{p}, hp⟩, Finset.centroid_singleton ℝ id p⟩

variable [DecidableEq E]



theorem isConnected_barycentric_original_vertex_link {p : E}
    (hp : {p} ∈ K.faces) (hconn : IsConnected (K.link p).space) :
    IsConnected (K.barycentricSubdivision.link p).space := by
  unfold barycentricSubdivision
  exact K.isConnected_derived_original_vertex_link _ _ hp hconn



theorem barycentric_closedStars_inter_subset_links {p q : E}
    (hp : {p} ∈ K.faces) (hq : {q} ∈ K.faces) (hpq : p ≠ q) :
    (K.barycentricSubdivision.closedStar p).space ∩
        (K.barycentricSubdivision.closedStar q).space ⊆
      (K.barycentricSubdivision.link p).space ∩
        (K.barycentricSubdivision.link q).space := by
  unfold barycentricSubdivision
  exact K.derived_closedStars_inter_subset_links _ _ hp hq hpq

end Geometry.SimplicialComplex
