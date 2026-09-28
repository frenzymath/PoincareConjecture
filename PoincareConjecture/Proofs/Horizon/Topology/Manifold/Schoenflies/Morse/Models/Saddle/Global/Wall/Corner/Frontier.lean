import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Corner.Coordinates








noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Corner

theorem frontier_body :
    frontier body = {p : E3 | p 2 = (p 1)^2 - (p 0)^2} := by
  rw [body_eq_preimage]
  change frontier (straighten.toHomeomorph ⁻¹'
    ((univ : Set Real) ×ˢ (univ ×ˢ Ici 0))) = _
  rw [← straighten.toHomeomorph.preimage_frontier]
  simp only [frontier_prod_eq, frontier_univ, closure_univ, closure_Ici,
    frontier_Ici, empty_prod, union_empty]
  ext p
  change (True ∧ True ∧ p 2 + (p 0)^2 - (p 1)^2 = 0) ↔ _
  simp only [true_and]
  change (p 2 + (p 0)^2 - (p 1)^2 = 0) ↔
    p 2 = (p 1)^2 - (p 0)^2
  constructor <;> intro h <;> linarith

theorem frontier_leftBody :
    frontier leftBody =
      {p : E3 | p 0 = 0 ∧ (p 1)^2 - (p 0)^2 ≤ p 2} ∪
      {p : E3 | p 0 ≤ 0 ∧ p 2 = (p 1)^2 - (p 0)^2} := by
  rw [leftBody_eq_preimage]
  change frontier (straighten.toHomeomorph ⁻¹'
    (Iic 0 ×ˢ ((univ : Set Real) ×ˢ Ici 0))) = _
  rw [← straighten.toHomeomorph.preimage_frontier]
  simp only [frontier_prod_eq, frontier_univ, closure_prod_eq, closure_univ, closure_Ici,
    closure_Iic, frontier_Ici, frontier_Iic, empty_prod, union_empty]
  rw [union_comm]
  ext p
  change ((p 0 = 0 ∧ True ∧ 0 ≤ p 2 + (p 0)^2 - (p 1)^2) ∨
      (p 0 ≤ 0 ∧ True ∧ p 2 + (p 0)^2 - (p 1)^2 = 0)) ↔ _
  simp only [true_and, mem_union, mem_ofPred_eq]
  constructor
  · rintro (⟨hx, hz⟩ | ⟨hx, hz⟩)
    · exact Or.inl ⟨hx, by linarith⟩
    · exact Or.inr ⟨hx, by linarith⟩
  · rintro (⟨hx, hz⟩ | ⟨hx, hz⟩)
    · exact Or.inl ⟨hx, by linarith⟩
    · exact Or.inr ⟨hx, by linarith⟩

theorem frontier_rightBody :
    frontier rightBody =
      {p : E3 | p 0 = 0 ∧ (p 1)^2 - (p 0)^2 ≤ p 2} ∪
      {p : E3 | 0 ≤ p 0 ∧ p 2 = (p 1)^2 - (p 0)^2} := by
  rw [rightBody_eq_preimage]
  change frontier (straighten.toHomeomorph ⁻¹'
    (Ici 0 ×ˢ ((univ : Set Real) ×ˢ Ici 0))) = _
  rw [← straighten.toHomeomorph.preimage_frontier]
  simp only [frontier_prod_eq, frontier_univ, closure_prod_eq, closure_univ, closure_Ici,
    frontier_Ici, empty_prod, union_empty]
  rw [union_comm]
  ext p
  change ((p 0 = 0 ∧ True ∧ 0 ≤ p 2 + (p 0)^2 - (p 1)^2) ∨
      (0 ≤ p 0 ∧ True ∧ p 2 + (p 0)^2 - (p 1)^2 = 0)) ↔ _
  simp only [true_and, mem_union, mem_ofPred_eq]
  constructor
  · rintro (⟨hx, hz⟩ | ⟨hx, hz⟩)
    · exact Or.inl ⟨hx, by linarith⟩
    · exact Or.inr ⟨hx, by linarith⟩
  · rintro (⟨hx, hz⟩ | ⟨hx, hz⟩)
    · exact Or.inl ⟨hx, by linarith⟩
    · exact Or.inr ⟨hx, by linarith⟩



theorem wall_above_graph_mem_frontiers_and_interior {p : E3}
    (hx : p 0 = 0) (hz : (p 1)^2 < p 2) :
    p ∈ frontier leftBody ∩ frontier rightBody ∧
      p ∈ interior (leftBody ∪ rightBody) := by
  refine ⟨⟨?_, ?_⟩, wall_above_graph_mem_interior_union hx hz⟩
  · rw [frontier_leftBody]
    exact Or.inl ⟨hx, by simpa [hx] using hz.le⟩
  · rw [frontier_rightBody]
    exact Or.inl ⟨hx, by simpa [hx] using hz.le⟩



theorem frontier_union_eq_side_frontiers_diff_wall :
    frontier (leftBody ∪ rightBody) =
      (frontier leftBody ∪ frontier rightBody) \
        {p : E3 | p 0 = 0 ∧ (p 1)^2 < p 2} := by
  rw [sides_union, frontier_body, frontier_leftBody, frontier_rightBody]
  ext p
  simp only [mem_union, mem_sdiff, mem_ofPred_eq]
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · rcases le_total (p 0) 0 with hx | hx
      · exact Or.inl (Or.inr ⟨hx, hz⟩)
      · exact Or.inr (Or.inr ⟨hx, hz⟩)
    · rintro ⟨hx, hlt⟩
      rw [hx] at hz
      nlinarith
  · rintro ⟨(⟨hx, hz⟩ | ⟨_, hz⟩) | (⟨hx, hz⟩ | ⟨_, hz⟩), hnot⟩
    · have hle : p 2 ≤ (p 1)^2 := not_lt.mp (fun hlt => hnot ⟨hx, hlt⟩)
      rw [hx] at hz ⊢
      nlinarith
    · exact hz
    · have hle : p 2 ≤ (p 1)^2 := not_lt.mp (fun hlt => hnot ⟨hx, hlt⟩)
      rw [hx] at hz ⊢
      nlinarith
    · exact hz



theorem side_frontier_not_subset_union_frontier :
    ¬ frontier leftBody ⊆ frontier (leftBody ∪ rightBody) := by
  intro h
  let p : E3 := WithLp.toLp 2 ![0, 0, 1]
  have hp := wall_above_graph_mem_frontiers_and_interior
    (p := p) (by rfl) (by change (0 : Real)^2 < 1; norm_num)
  exact (h hp.1.1).2 hp.2

end Poincare.Manifold.Schoenflies.Saddle.Wall.Corner
