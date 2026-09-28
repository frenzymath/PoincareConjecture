import PoincareConjecture.Proofs.M76.Mathlib.PolygonSplitSimplicity










set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} {m n : ℕ}



theorem edgeVertices_subset_range (P : Polygon E n) (i : Fin n) :
    (P.edgeVertices i : Set E) ⊆ range P := by
  classical
  simp only [edgeVertices, Finset.coe_pair, pair_subset_iff]
  exact ⟨mem_range_self i, mem_range_self (finRotate n i)⟩



theorem range_split_inter (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (hinj : Function.Injective (Fin.append u v)) :
    range (Fin.snoc u (v 0) : Fin ((m + 1) + 1) → E) ∩
      range (Fin.snoc v (u 0) : Fin ((n + 1) + 1) → E) = {u 0, v 0} := by
  rw [Fin.range_snoc, Fin.range_snoc]
  have hdis := (Fin.append_injective_iff.mp hinj).2.2
  apply Subset.antisymm
  · rintro x ⟨hx, hy⟩
    rcases hx with rfl | ⟨i, hi⟩
    · simp
    · rcases hy with rfl | ⟨j, hj⟩
      · simp
      · exact (hdis i j (hi.trans hj.symm)).elim
  · rintro x (rfl | hx)
    · exact ⟨Or.inr (mem_range_self 0), Or.inl rfl⟩
    · have hxb : x = v 0 := hx
      subst x
      exact ⟨Or.inl rfl, Or.inr (mem_range_self 0)⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem boundary_split_inter (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (hP : (mk (Fin.append u v)).HasSimplicialEdges)
    (hinj : Function.Injective (Fin.append u v))
    (hchord : segment ℝ (u 0) (v 0) ∩ (mk (Fin.append u v)).boundary ℝ ⊆ {u 0, v 0}) :
    (mk (Fin.snoc u (v 0))).boundary ℝ ∩ (mk (Fin.snoc v (u 0))).boundary ℝ =
      segment ℝ (u 0) (v 0) := by
  have hd : segment ℝ ((mk (Fin.append u v)) ((0 : Fin (m + 1)).castAdd (n + 1)))
      ((mk (Fin.append u v)) (Fin.natAdd (m + 1) (0 : Fin (n + 1)))) ∩
        (mk (Fin.append u v)).boundary ℝ ⊆
      {(mk (Fin.append u v)) ((0 : Fin (m + 1)).castAdd (n + 1)),
        (mk (Fin.append u v)) (Fin.natAdd (m + 1) (0 : Fin (n + 1)))} := by
    simpa only [Fin.append_left, Fin.append_right] using hchord
  apply Subset.antisymm
  · rintro x ⟨hx, hy⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    rw [edgeSet_eq_convexHull] at hi hj
    have hcompat := (mk (Fin.append u v)).convexHull_inter_of_edges_or_chord hP hinj _ _ hd
      (by simpa only [Fin.append_left, Fin.append_right] using edgeVertices_split_left_cases u v i)
      (by simpa only [Fin.append_left, Fin.append_right] using edgeVertices_split_right_cases u v j)
    have hsub :
        ((mk (Fin.snoc u (v 0))).edgeVertices i : Set E) ∩
          ((mk (Fin.snoc v (u 0))).edgeVertices j : Set E) ⊆ {u 0, v 0} := by
      rw [← range_split_inter u v hinj]
      exact inter_subset_inter (edgeVertices_subset_range _ i) (edgeVertices_subset_range _ j)
    have hmem := convexHull_mono hsub (hcompat ⟨hi, hj⟩)
    simpa only [convexHull_pair] using hmem
  · intro x hx
    constructor
    · rw [boundary_split_left]
      exact Or.inr hx
    · rw [boundary_split_right]
      exact Or.inr hx

end Polygon
