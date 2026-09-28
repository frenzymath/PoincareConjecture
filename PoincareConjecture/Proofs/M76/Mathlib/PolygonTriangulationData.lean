import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegions
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonReindex










set_option autoImplicit false

open Set Geometry

namespace Polygon




structure IsTriangulation {n : ℕ} (P : Polygon (ℝ × ℝ) n)
    (K : SimplicialComplex ℝ (ℝ × ℝ)) : Prop where

  finite_faces : K.faces.Finite

  space_eq : K.space = closure P.inside

  vertices_subset : K.vertices ⊆ range P

  edge_mem : ∀ i, P.edgeVertices i ∈ K.faces

  pure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3




theorem IsTriangulation.vertices_eq {n : ℕ} {P : Polygon (ℝ × ℝ) n}
    {K : SimplicialComplex ℝ (ℝ × ℝ)} (h : P.IsTriangulation K) : K.vertices = range P := by
  classical
  apply Subset.antisymm h.vertices_subset
  rintro x ⟨i, rfl⟩
  apply K.down_closed (h.edge_mem i) _ (Finset.singleton_nonempty _)
  simp [edgeVertices]



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
