import PoincareConjecture.Proofs.M76.Rigidity.MatchedCollarMap
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedCoverOpenUnion

set_option autoImplicit false

open Set

namespace Geometry

variable {E F X : Type*} {L : Set E} {K : Set F}
  {Q : E → F} {c : E × ℝ → X} {d : F × ℝ → X}

theorem image_matchedCollarMap_open_strip (hQ : Q '' L = K)
    (hzero : ∀ x ∈ L, c (x, 0) = d (Q x, 0)) {eps : ℝ} (heps : 0 < eps) :
    matchedCollarMap Q c d '' (L ×ˢ Ioo (-eps) eps) =
      c '' (L ×ˢ Ico 0 eps) ∪ d '' (K ×ˢ Ico 0 eps) := by
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    by_cases ht : 0 ≤ z.2
    · exact Or.inl ⟨z, ⟨hz.1, ht, hz.2.2⟩,
        (matchedCollarMap_nonneg Q c d ht).symm⟩
    · refine Or.inr ⟨(Q z.1, -z.2), ?_, ?_⟩
      · exact ⟨hQ.subset ⟨z.1, hz.1, rfl⟩,
          by linarith [lt_of_not_ge ht], by linarith [hz.2.1]⟩
      · simp only [matchedCollarMap, if_neg ht]
  · rintro y (hy | hy)
    · rcases hy with ⟨z, hz, hzy⟩
      refine ⟨z, ⟨hz.1, ?_, hz.2.2⟩, (matchedCollarMap_nonneg Q c d hz.2.1).trans hzy⟩
      linarith [hz.2.1]
    · rcases hy with ⟨w, hw, hwy⟩
      obtain ⟨x, hx, hQx⟩ := hQ.symm.subset hw.1
      have hval : matchedCollarMap Q c d (x, -w.2) = d w := by
        rw [matchedCollarMap_nonpos Q c d hzero hx (by dsimp; linarith [hw.2.1])]
        simp only [neg_neg, hQx, Prod.mk.eta]
      refine ⟨(x, -w.2), ⟨hx, ?_, ?_⟩, hval.trans hwy⟩
      · linarith [hw.2.2]
      · linarith [hw.2.1]

theorem mapsTo_matchedCollarMap_closed_strip {U : Set X} {eps : ℝ}
    (hQ : MapsTo Q L K)
    (hc : MapsTo c (L ×ˢ Icc (0 : ℝ) eps) U)
    (hd : MapsTo d (K ×ˢ Icc (0 : ℝ) eps) U) :
    MapsTo (matchedCollarMap Q c d) (L ×ˢ Icc (-eps) eps) U := by
  intro z hz
  by_cases ht : 0 ≤ z.2
  · rw [matchedCollarMap_nonneg Q c d ht]
    exact hc ⟨hz.1, ht, hz.2.2⟩
  · simp only [matchedCollarMap, if_neg ht]
    exact hd ⟨hQ hz.1, by linarith [lt_of_not_ge ht], by linarith [hz.2.1]⟩

variable [TopologicalSpace E] [TopologicalSpace X] {R : Set X}

theorem isOpen_matchedCollarMap_open_strip
    (hR : IsClosed R) (HB : L ≃ₜ frontier R)
    (hc0 : ∀ x : L, c ((x : E), 0) = HB x)
    (hQ : Q '' L = K) (hzero : ∀ x ∈ L, c (x, 0) = d (Q x, 0))
    (hcR : MapsTo c (L ×ˢ Icc (0 : ℝ) 1) R)
    (hdT : MapsTo d (K ×ˢ Icc (0 : ℝ) 1) (interior R)ᶜ)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hcopen : IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (L ×ˢ Ico 0 eps))))
    (hdopen : IsOpen ((Subtype.val : ((interior R)ᶜ : Set X) → X) ⁻¹'
      (d '' (K ×ˢ Ico 0 eps)))) :
    IsOpen (matchedCollarMap Q c d '' (L ×ˢ Ioo (-eps) eps)) := by
  rw [image_matchedCollarMap_open_strip hQ hzero heps]
  have hbase (y : X) (hy : y ∈ frontier R) :
      y ∈ c '' (L ×ˢ Ico 0 eps) ∩ d '' (K ×ˢ Ico 0 eps) := by
    let x : L := HB.symm ⟨y, hy⟩
    have hvalue : c ((x : E), 0) = y :=
      (hc0 x).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨y, hy⟩))
    exact ⟨⟨((x : E), 0), ⟨x.property, le_rfl, heps⟩, hvalue⟩,
      ⟨(Q x, 0), ⟨hQ.subset ⟨x, x.property, rfl⟩, le_rfl, heps⟩,
        (hzero x x.property).symm.trans hvalue⟩⟩
  apply isOpen_union_of_closed_cover hR isOpen_interior.isClosed_compl
  · apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ R
    · exact Or.inl hx
    · exact Or.inr (fun h => hx (interior_subset h))
  · rintro y ⟨z, hz, rfl⟩
    exact hcR ⟨hz.1, hz.2.1, hz.2.2.le.trans heps1⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hdT ⟨hz.1, hz.2.1, hz.2.2.le.trans heps1⟩
  · intro y hy
    apply hbase y
    rw [hR.frontier_eq]
    exact hy
  · exact hcopen
  · exact hdopen

end Geometry
