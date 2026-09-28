import PoincareConjecture.Proofs.M76.Mathlib.MarkedPolygonSubdivision










set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}





theorem exists_subdivision_at_finite_marks (P : Polygon E (N + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {F : Set E} (hF : F.Finite) (hFP : F ⊆ P.boundary ℝ) :
    ∃ (M : ℕ) (Q : Polygon E (M + 3)), Q.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.boundary ℝ = P.boundary ℝ ∧
      range P ∪ F ⊆ range Q := by
  classical
  let : Fintype F := hF.fintype
  choose i r hr he using fun x : F =>
    P.exists_halfOpen_edge_parameter (hFP x.property)
  let T : Finset ℝ := insert 0 (insert 1 (Finset.univ.image r))
  have hT : (T : Set ℝ) ⊆ Icc (0 : ℝ) 1 := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨le_rfl, zero_le_one⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨zero_le_one, le_rfl⟩
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨(hr x).1, (hr x).2.le⟩
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
  have hretain : range P ∪ F ⊆ range (P.subdivide t) := by
    intro x hx
    rcases hx with ⟨k, rfl⟩ | hx
    · simpa only [AffineMap.lineMap_apply_zero] using
        hmarked k (z := 0) (by simp [T]) zero_lt_one
    · have hrT : r ⟨x, hx⟩ ∈ T := by
        simp only [T, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
        exact Or.inr (Or.inr ⟨⟨x, hx⟩, rfl⟩)
      obtain ⟨j, hj⟩ := hmarked (i ⟨x, hx⟩) hrT (hr ⟨x, hx⟩).2
      exact ⟨j, hj.trans (he ⟨x, hx⟩)⟩
  have hex : ∃ (L : ℕ) (Q : Polygon E L), 3 ≤ L ∧ Q.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.boundary ℝ = P.boundary ℝ ∧
      range P ∪ F ⊆ range Q := by
    refine ⟨(N + 3) * (m + 1), P.subdivide t, ?_,
      P.hasSimplicialEdges_subdivide hP hinj t ht ht0 ht1,
      P.injective_subdivide hP hinj t ht ht0 ht1,
      P.subdivide_boundary t ht ht0 ht1, hretain⟩
    have hmul : N + 3 ≤ (N + 3) * (m + 1) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N + 3) (by omega : 1 ≤ m + 1)
    omega
  obtain ⟨L, Q, hL, hQ⟩ := hex
  obtain ⟨M, hM⟩ : ∃ M, L = M + 3 := ⟨L - 3, by omega⟩
  subst L
  exact ⟨M, Q, hQ⟩

end Polygon
