import PoincareConjecture.Proofs.M76.Mathlib.UniformPolygonSimplicity










set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}




theorem exists_halfOpen_edge_parameter (P : Polygon E (N + 3)) {x : E}
    (hx : x ∈ P.boundary ℝ) :
    ∃ (i : Fin (N + 3)) (t : ℝ), t ∈ Ico (0 : ℝ) 1 ∧
      AffineMap.lineMap (P i) (P (finRotate (N + 3) i)) t = x := by
  obtain ⟨i, t, ht, htx⟩ := mem_iUnion.mp hx
  by_cases ht1 : t = 1
  · refine ⟨finRotate (N + 3) i, 0, ⟨le_rfl, zero_lt_one⟩, ?_⟩
    rw [AffineMap.lineMap_apply_zero]
    simpa only [ht1, AffineMap.lineMap_apply_one] using htx
  · exact ⟨i, t, ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩, htx⟩






theorem exists_subdivision_at_marks (P : Polygon E (N + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {a b : E} (ha : a ∈ P.boundary ℝ) (hb : b ∈ P.boundary ℝ) :
    ∃ (M : ℕ) (Q : Polygon E (M + 3)), Q.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.boundary ℝ = P.boundary ℝ ∧
      a ∈ range Q ∧ b ∈ range Q := by
  classical
  obtain ⟨i, r, hr, hra⟩ := P.exists_halfOpen_edge_parameter ha
  obtain ⟨j, s, hs, hsb⟩ := P.exists_halfOpen_edge_parameter hb
  let T : Finset ℝ := {0, 1, r, s}
  have hT : (T : Set ℝ) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [T, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨hr.1, hr.2.le⟩
    · exact ⟨hs.1, hs.2.le⟩
  obtain ⟨m, t, ht, ht0, ht1, htrange, _⟩ :=
    T.exists_ordered_partition zero_lt_one hT (by simp [T]) (by simp [T])
  have hmarked (k : Fin (N + 3)) {z : ℝ} (hz : z ∈ T) (hz1 : z < 1) :
      AffineMap.lineMap (P k) (P (finRotate (N + 3) k)) z ∈ range (P.subdivide t) := by
    obtain ⟨l, hl⟩ := htrange.symm ▸ (show z ∈ (T : Set ℝ) from hz)
    have hlast : l ≠ Fin.last (m + 1) := by
      intro h
      rw [h, ht1] at hl
      exact hz1.ne hl.symm
    obtain ⟨q, hq⟩ := Fin.eq_castSucc_of_ne_last hlast
    refine ⟨finProdFinEquiv (k, q), ?_⟩
    rw [P.subdivide_apply, hq, hl]
  have hex : ∃ (L : ℕ) (Q : Polygon E L), 3 ≤ L ∧ Q.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.boundary ℝ = P.boundary ℝ ∧
      a ∈ range Q ∧ b ∈ range Q := by
    refine ⟨(N + 3) * (m + 1), P.subdivide t, ?_,
      P.hasSimplicialEdges_subdivide hP hinj t ht ht0 ht1,
      P.injective_subdivide hP hinj t ht ht0 ht1,
      P.subdivide_boundary t ht ht0 ht1, ?_, ?_⟩
    · have hmul : N + 3 ≤ (N + 3) * (m + 1) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N + 3) (by omega : 1 ≤ m + 1)
      omega
    · exact hra ▸ hmarked i (by simp [T]) hr.2
    · exact hsb ▸ hmarked j (by simp [T]) hs.2
  obtain ⟨L, Q, hL, hQ⟩ := hex
  obtain ⟨M, hM⟩ : ∃ M, L = M + 3 := ⟨L - 3, by omega⟩
  subst L
  exact ⟨M, Q, hQ⟩

end Polygon
