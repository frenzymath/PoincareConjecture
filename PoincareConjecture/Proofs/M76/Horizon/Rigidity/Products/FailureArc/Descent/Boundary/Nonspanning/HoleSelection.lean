import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_annular_member_of_disjoint_disk_exteriors
    {S T X A B C QA QB QC : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S)) (hST : S ⊆ interior T)
    (hA : IsFinitePLBallPair P2 A QA) (hB : IsFinitePLBallPair P2 B QB)
    (hC : IsFinitePLBallPair P2 C QC)
    (hAB : Disjoint A B) (hBC : Disjoint B C) (hAC : Disjoint A C)
    (hcover : ((A ∪ B) ∪ C) ∪ X = T) (hXS : Disjoint X S)
    (hQA : QA ⊆ frontier T ∪ X) (hQB : QB ⊆ frontier T ∪ X)
    (hQC : QC ⊆ frontier T ∪ X) :
    ∃ D : Set P2, (D = A ∨ D = B ∨ D = C) ∧ S ⊆ interior D ∧
      (∀ E ∈ ({A, B, C} : Set (Set P2)), E ≠ D → Disjoint E S) ∧
      ∃ H : squareAnnulus 8 1 ≃ₜ (D \ interior S : Set P2), H.IsFinitePL ∧
        (∀ z : squareAnnulus 8 1,
          depth 8 (z : P2) = -1 ↔ (H z : P2) ∈ frontier D) ∧
        ∀ z : squareAnnulus 8 1,
          depth 8 (z : P2) = 1 ↔ (H z : P2) ∈ frontier S := by
  have hsub : S ⊆ A ∪ (B ∪ C) := by
    intro x hx
    have h := (hcover.symm.subset (interior_subset (hST hx))).resolve_right
      (fun hxX => disjoint_left.mp hXS hxX hx)
    simpa only [union_assoc] using h
  have hside : S ⊆ A ∨ S ⊆ B ∨ S ⊆ C := by
    have hi : A ∩ (B ∪ C) = ∅ := by
      rw [inter_union_distrib_left, (show A ∩ B = ∅ from hAB.eq_bot),
        (show A ∩ C = ∅ from hAC.eq_bot), union_empty]
    rcases isPreconnected_subset_one_cut_piece hS.isConnected.isPreconnected
      hA.isCompact.isClosed (hB.isCompact.isClosed.union hC.isCompact.isClosed)
      hsub hi (by simp) with hSA | hSBC
    · exact Or.inl hSA
    · exact Or.inr (isPreconnected_subset_one_cut_piece hS.isConnected.isPreconnected
        hB.isCompact.isClosed hC.isCompact.isClosed hSBC
        (show B ∩ C = ∅ from hBC.eq_bot) (by simp))
  have hinside {D Q : Set P2} (hD : IsFinitePLBallPair P2 D Q)
      (hQ : Q ⊆ frontier T ∪ X) (hSD : S ⊆ D) : S ⊆ interior D := by
    rw [hD.interior_eq_sdiff_of_finrank_eq rfl]
    intro x hx
    refine ⟨hSD hx, ?_⟩
    intro hq
    rcases hQ hq with hxT | hxX
    · exact hxT.2 (hST hx)
    · exact disjoint_left.mp hXS hxX hx
  have selected : ∃ D : Set P2, (D = A ∨ D = B ∨ D = C) ∧
      IsFinitePLBallPair P2 D (frontier D) ∧ S ⊆ interior D := by
    rcases hside with hSA | hSB | hSC
    · exact ⟨A, Or.inl rfl, (hA.frontier_eq_of_finrank_eq rfl).symm ▸ hA,
        hinside hA hQA hSA⟩
    · exact ⟨B, Or.inr (Or.inl rfl), (hB.frontier_eq_of_finrank_eq rfl).symm ▸ hB,
        hinside hB hQB hSB⟩
    · exact ⟨C, Or.inr (Or.inr rfl), (hC.frontier_eq_of_finrank_eq rfl).symm ▸ hC,
        hinside hC hQC hSC⟩
  obtain ⟨D, hD, hDf, hSD⟩ := selected
  obtain ⟨H, hH, hout, hin⟩ := exists_square_annulus_nested_disks hS hDf hSD
    (show (0 : ℝ) < 1 by norm_num) (show (2 : ℝ) * 1 < 8 by norm_num)
  refine ⟨D, hD, hSD, ?_, H, hH, hout, hin⟩
  intro E hE hne
  have hE' : E = A ∨ E = B ∨ E = C := by
    simpa only [mem_insert_iff, mem_singleton_iff] using hE
  have hED : Disjoint E D := by
    rcases hD with rfl | rfl | rfl <;> rcases hE' with rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact hAB.symm
    · exact hAC.symm
    · exact hAB
    · exact (hne rfl).elim
    · exact hBC.symm
    · exact hAC
    · exact hBC
    · exact (hne rfl).elim
  exact hED.mono Subset.rfl (hSD.trans interior_subset)

end PoincareConjecture.M76.Dehn
