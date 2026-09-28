import PoincareConjecture.Proofs.M76.Mathlib.PolygonCornerInterior
import Mathlib.Data.Set.Finite.Lemmas










set_option autoImplicit false

open Set



theorem openSegment_zero_subset_cap {d : ℝ × ℝ} (hdx : 0 < d.1) (hdy : 0 < d.2) :
    openSegment ℝ (0, 0) d ⊆ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < d.1 + d.2} := by
  rintro q ⟨a, b, ha, hb, hab, rfl⟩
  change 0 < a * 0 + b * d.1 ∧ 0 < a * 0 + b * d.2 ∧
    (a * 0 + b * d.1) + (a * 0 + b * d.2) < d.1 + d.2
  simp only [mul_zero, zero_add]
  refine ⟨mul_pos hb hdx, mul_pos hb hdy, ?_⟩
  have hb1 : b < 1 := by linarith
  nlinarith [mul_lt_mul_of_pos_right hb1 (add_pos hdx hdy)]

namespace Polygon





theorem exists_corner_diagonal_of_triangle_vertex {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (i : Fin (n + 3))
    (hprev : P ((finRotate (n + 3)).symm i) = (1, 0)) (hcenter : P i = (0, 0))
    (hnext : P (finRotate (n + 3) i) = (0, 1))
    (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ j, L (P j) ≤ 0) (hdir : 0 < L (-1, -1))
    (hex : ∃ j, 0 < (P j).1 ∧ 0 < (P j).2 ∧ (P j).1 + (P j).2 ≤ 1) :
    ∃ j, j ≠ i ∧ j ≠ (finRotate (n + 3)).symm i ∧ j ≠ finRotate (n + 3) i ∧
      openSegment ℝ (P i) (P j) ⊆ P.inside := by
  let S : Set (Fin (n + 3)) := {j | 0 < (P j).1 ∧ 0 < (P j).2 ∧ (P j).1 + (P j).2 ≤ 1}
  obtain ⟨j, hj, hmin⟩ := Set.exists_min_image S (fun k => (P k).1 + (P k).2)
    (Set.toFinite S) hex
  have hcap := P.corner_cap_subset_inside hP hinj i hprev hcenter hnext L hL hdir
    (add_pos hj.1 hj.2.1) hj.2.2 (by
      intro k hk
      have hks : k ∈ S := ⟨hk.1, hk.2.1, hk.2.2.le.trans hj.2.2⟩
      exact (not_le_of_gt hk.2.2) (hmin k hks))
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · intro hji
    have hx := hj.1
    rw [hji, hcenter] at hx
    exact lt_irrefl 0 hx
  · intro hji
    have hy := hj.2.1
    rw [hji, hprev] at hy
    exact lt_irrefl 0 hy
  · intro hji
    have hx := hj.1
    rw [hji, hnext] at hx
    exact lt_irrefl 0 hx
  · rw [hcenter]
    exact (openSegment_zero_subset_cap hj.1 hj.2.1).trans hcap

end Polygon
