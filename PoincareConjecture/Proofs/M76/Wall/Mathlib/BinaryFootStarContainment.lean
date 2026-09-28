import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.DualVertexFaceContainment

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem image_vertex_dual_subset_original_star_and_mark
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K D : SimplicialComplex ℝ E) [Fintype D.faces]
    (hDK : D ≤ K) {p : E} (hp : p ∈ D.vertices) {c : E → E}
    (hmarks : ∀ L : SimplicialComplex ℝ E, L ≤ K → c '' L.space = L.space) :
    c '' (D.barycentricDualBlock {p}).space ⊆ (K.closedStar p).space ∩ D.space := by
  have hstarDK : D.closedStar p ≤ K.closedStar p :=
    fun _ hs => ⟨hDK hs.1, hDK hs.2⟩
  have hstarK : K.closedStar p ≤ K := fun _ hs => hs.1
  have hfootstar : (D.barycentricDualBlock {p}).space ⊆ (K.closedStar p).space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, hst⟩ := D.exists_original_star_face_of_vertex_dual_face hp hs
    exact (K.closedStar p).convexHull_subset_space (hstarDK ht) (hst hxs)
  have hfootD : (D.barycentricDualBlock {p}).space ⊆ D.space := by
    intro x hx
    exact D.barycentricSubdivision_isSubdivision.space_eq.subset
      (space_subset_of_le (D.barycentricDualBlock_le {p}) hx)
  rintro y ⟨x, hx, rfl⟩
  exact ⟨(hmarks (K.closedStar p) hstarK).subset ⟨x, hfootstar hx, rfl⟩,
    (hmarks D hDK).subset ⟨x, hfootD hx, rfl⟩⟩

end Geometry.SimplicialComplex
