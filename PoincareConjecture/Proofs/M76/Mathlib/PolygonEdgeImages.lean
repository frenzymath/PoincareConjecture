import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalEdges









set_option autoImplicit false

open Set

namespace Polygon

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}




theorem hasSimplicialEdges_of_injective_edge_images (P : Polygon E n) (Q : Polygon F n)
    (hn : 3 ≤ n) (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (f : E → F) (hf : InjOn f (P.boundary ℝ)) (hQ : ∀ i, Q i = f (P i))
    (hedge : ∀ i, Q.edgeSet ℝ i = f '' P.edgeSet ℝ i) : Q.HasSimplicialEdges := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hend (v i : Fin (k + 3)) (hvi : P v ∈ P.edgeSet ℝ i) :
      f (P v) ∈ (Q.edgeVertices i : Set F) := by
    rcases (P.vertex_mem_edgeSet_iff hP hinj v i).mp hvi with h | h
    · rw [h]
      simp [edgeVertices, hQ]
    · rw [h]
      simp [edgeVertices, hQ]
  intro i j x hx
  by_cases hij : i = j
  · subst j
    rw [inter_self, ← Q.edgeSet_eq_convexHull]
    exact hx.1
  · obtain ⟨y, hy, hyx⟩ := (hedge i) ▸ hx.1
    obtain ⟨z, hz, hzx⟩ := (hedge j) ▸ hx.2
    have hzy : z = y := hf (mem_iUnion.mpr ⟨j, hz⟩) (mem_iUnion.mpr ⟨i, hy⟩)
      (hzx.trans hyx.symm)
    subst z
    have hyv : y ∈ range P := by
      by_contra h
      exact hij (P.eq_of_mem_edgeSets_of_not_vertex hP hinj h hy hz)
    obtain ⟨v, rfl⟩ := hyv
    exact hyx ▸ subset_convexHull ℝ _ ⟨hend v i hy, hend v j hz⟩

end Polygon
