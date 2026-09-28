import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusDepth










set_option autoImplicit false

open Set

namespace PLAnnularStrip


theorem interior_squareAnnulus {L d : ℝ} (hwidth : 2 * d < L) :
    interior (squareAnnulus L d) = depth L ⁻¹' Ioo (-d) d := by
  rw [squareAnnulus, sdiff_eq, interior_inter, interior_prod_eq,
    interior_Icc, interior_compl, closure_prod_eq,
    closure_Ioo (by linarith : d ≠ L - d)]
  ext p
  simp only [mem_inter_iff, mem_prod, mem_Ioo, mem_compl_iff, mem_Icc,
    mem_preimage, depth, lt_min_iff]
  constructor
  · rintro ⟨⟨hx, hy⟩, hn⟩
    refine ⟨⟨⟨hx.1, hy.1⟩, ⟨by linarith [hx.2], by linarith [hy.2]⟩⟩, ?_⟩
    by_contra h
    have h' := le_min_iff.mp (le_of_not_gt h)
    have hxy := le_min_iff.mp h'.1
    have hxy' := le_min_iff.mp h'.2
    exact hn ⟨⟨hxy.1, by linarith [hxy'.1]⟩, ⟨hxy.2, by linarith [hxy'.2]⟩⟩
  · rintro ⟨⟨⟨hx, hy⟩, ⟨hx', hy'⟩⟩, h⟩
    refine ⟨⟨⟨hx, by linarith⟩, ⟨hy, by linarith⟩⟩, ?_⟩
    rintro ⟨⟨ha, hb⟩, ⟨hc, he⟩⟩
    have hl : d ≤ min (min p.1 p.2) (min (L - p.1) (L - p.2)) :=
      le_min (le_min ha hc) (le_min (by linarith) (by linarith))
    exact (not_lt_of_ge hl) h



theorem mem_frontier_squareAnnulus_iff {L d : ℝ} (hd : 0 < d)
    (hwidth : 2 * d < L) {p : ℝ × ℝ} (hp : p ∈ squareAnnulus L d) :
    p ∈ frontier (squareAnnulus L d) ↔ |depth L p| = d := by
  have hclosed : IsClosed (squareAnnulus L d) :=
    (isClosed_Icc.prod isClosed_Icc).sdiff (isOpen_Ioo.prod isOpen_Ioo)
  rw [frontier, hclosed.closure_eq, mem_sdiff, and_iff_right hp,
    interior_squareAnnulus hwidth]
  have hbounds := mem_squareAnnulus_iff_depth.mp hp
  simp only [mem_preimage, mem_Ioo]
  constructor
  · intro h
    rcases lt_or_eq_of_le hbounds.1 with hlo | he
    · rcases lt_or_eq_of_le hbounds.2 with hhi | he
      · exact (h ⟨hlo, hhi⟩).elim
      · rw [he, abs_of_pos hd]
    · rw [← he, abs_neg, abs_of_pos hd]
  · intro he h
    have hlt : |depth L p| < d := abs_lt.mpr h
    linarith

end PLAnnularStrip
