import PoincareConjecture.Proofs.M76.Mathlib.AffineBasisEquivalence
import PoincareConjecture.Proofs.M76.Mathlib.PlanarSegmentHeight
import Mathlib.Analysis.Normed.Module.FiniteDimension









set_option autoImplicit false

open Set

private theorem independent_reference_corner :
    AffineIndependent ℝ ![((-1 : ℝ), (1 : ℝ)), (0, 0), (1, 1)] := by
  let S : AffineSubspace ℝ (ℝ × ℝ) :=
    (affineSpan ℝ {(1 : ℝ)}).comap (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  apply affineIndependent_of_ne_of_mem_of_notMem_of_mem (s := S)
  · norm_num
  · simp [S]
  · simp [S]
  · simp [S]




theorem AffineIndependent.exists_planar_corner_coordinates {a b c : ℝ × ℝ}
    (h : AffineIndependent ℝ ![a, b, c]) :
    ∃ e : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ), e a = (-1, 1) ∧ e b = (0, 0) ∧ e c = (1, 1) := by
  let B : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨![a, b, c], h,
    h.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  let C : AffineBasis (Fin 3) ℝ (ℝ × ℝ) :=
    ⟨![(-1, 1), (0, 0), (1, 1)], independent_reference_corner,
      independent_reference_corner.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
        (by simp [Module.finrank_prod])⟩
  obtain ⟨e, he⟩ := B.exists_affineEquiv_map C 1
  exact ⟨e.toContinuousAffineEquiv, he 0, he 1, he 2⟩




theorem mem_reference_corner_iff {q : ℝ × ℝ} (hq : |q.1| < 1) :
    q ∈ segment ℝ (-1, 1) (0, 0) ∪ segment ℝ (0, 0) (1, 1) ↔ q.2 = |q.1| := by
  rw [mem_union, PlanarSegment.mem_segment_iff (by norm_num : (-1 : ℝ) ≠ 0),
    PlanarSegment.mem_segment_iff (by norm_num : (0 : ℝ) ≠ 1)]
  have hx := abs_lt.mp hq
  norm_num [PlanarSegment.height, AffineMap.lineMap_apply_module', uIcc_of_le] at ⊢
  by_cases hneg : q.1 ≤ 0
  · rw [abs_of_nonpos hneg]
    constructor
    · rintro (h | h)
      · linarith [h.2]
      · have hz : q.1 = 0 := le_antisymm hneg h.1.1
        simpa only [hz, neg_zero] using h.2
    · intro h
      exact Or.inl ⟨⟨hx.1.le, hneg⟩, by linarith⟩
  · have hpos := lt_of_not_ge hneg
    rw [abs_of_nonneg hpos.le]
    constructor
    · rintro (h | h)
      · exact (hneg h.1.2).elim
      · exact h.2
    · intro h
      exact Or.inr ⟨⟨hpos.le, hx.2.le⟩, h⟩
