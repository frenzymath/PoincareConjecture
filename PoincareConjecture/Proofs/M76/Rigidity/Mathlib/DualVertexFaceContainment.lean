import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem exists_original_star_face_of_vertex_dual_face
    {p : E} (hp : p ∈ K.vertices) {s : Finset E}
    (hs : s ∈ (K.barycentricDualBlock {p}).faces) :
    ∃ t ∈ (K.closedStar p).faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  have hs' : s ∈ (K.barycentricSubdivision.closedStar p).faces := by
    rwa [← K.barycentricDualBlock_singleton_eq_closedStar hp]
  obtain ⟨a, ha, hchain, hsa, hpa⟩ :=
    (K.barycentricSubdivision_closedStar_faces hp s).mp hs'
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
  have him (i : K.faces) (hi : i ∈ a) : i.val ⊆ m.val := by
    rcases hchain i hi m hm with h | h
    · exact h
    · exact hmax hi h
  refine ⟨m.val, ⟨m.property, ?_⟩, ?_⟩
  · simpa only [Finset.insert_eq_of_mem (hpa m hm)] using m.property
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hsa ▸ hx)
    exact convexHull_mono (him i hi)
      (i.val.centroid_mem_convexHull (K.nonempty_of_mem_faces i.property))

end Geometry.SimplicialComplex
