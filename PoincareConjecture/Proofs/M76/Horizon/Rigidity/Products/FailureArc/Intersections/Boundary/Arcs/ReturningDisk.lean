import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_returning_arc_disk
    {S T W : Set P2} {a b : P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (ha : a ∈ frontier T) (hb : b ∈ frontier T)
    (hproper : W \ {a, b} ⊆ interior T) (hWS : Disjoint W S) :
    ∃ D B U V : Set P2,
      IsFinitePLBallPair ℝ U {a, b} ∧ IsFinitePLBallPair ℝ V {a, b} ∧
      U ∪ V = frontier T ∧ U ∩ V = {a, b} ∧
      IsFinitePLBallPair P2 D (U ∪ W) ∧
      IsFinitePLBallPair P2 B (W ∪ V) ∧
      D ∪ B = T ∧ D ∩ B = W ∧
      D ∩ frontier T = U ∧ B ∩ frontier T = V ∧
      S ⊆ interior B ∧ Disjoint D S ∧ D ⊆ T \ S ∧
      ∀ K : Set P2, IsPreconnected K → K ⊆ T → Disjoint K W →
        (K ∩ S).Nonempty → Disjoint D K := by
  obtain ⟨U₀, V₀, hU₀, hV₀, hUV₀, hUVi₀⟩ := hT.exists_boundary_arcs ha hb hab
  have hproper' : W \ {a, b} ⊆ T \ frontier T := by
    rw [← hT.interior_eq_sdiff_of_finrank_eq rfl]
    exact hproper
  obtain ⟨D₀, B₀, hD₀, hB₀, hcover₀, hinter₀, hDU₀, hBV₀⟩ :=
    hT.exists_proper_arc_cut hU₀ hV₀ hW hab hUVi₀.subset hUV₀ hproper'
  have hside : S ⊆ D₀ ∨ S ⊆ B₀ :=
    isPreconnected_subset_one_cut_piece hS.isConnected.isPreconnected
      hD₀.isCompact.isClosed hB₀.isCompact.isClosed
      ((hST.trans interior_subset).trans hcover₀.symm.subset) hinter₀ hWS.symm
  have selected : ∃ D B U V : Set P2,
      IsFinitePLBallPair ℝ U {a, b} ∧ IsFinitePLBallPair ℝ V {a, b} ∧
      U ∪ V = frontier T ∧ U ∩ V = {a, b} ∧
      IsFinitePLBallPair P2 D (U ∪ W) ∧
      IsFinitePLBallPair P2 B (W ∪ V) ∧
      D ∪ B = T ∧ D ∩ B = W ∧
      D ∩ frontier T = U ∧ B ∩ frontier T = V ∧ S ⊆ B := by
    rcases hside with hSD | hSB
    · refine ⟨B₀, D₀, V₀, U₀, hV₀, hU₀, ?_, ?_, ?_, ?_, ?_, ?_,
        hBV₀, hDU₀, hSD⟩
      · simpa only [union_comm] using hUV₀
      · simpa only [inter_comm] using hUVi₀
      · simpa only [union_comm] using hB₀
      · simpa only [union_comm] using hD₀
      · simpa only [union_comm] using hcover₀
      · simpa only [inter_comm] using hinter₀
    · exact ⟨D₀, B₀, U₀, V₀, hU₀, hV₀, hUV₀, hUVi₀, hD₀, hB₀,
        hcover₀, hinter₀, hDU₀, hBV₀, hSB⟩
  obtain ⟨D, B, U, V, hU, hV, hUV, hUVi, hD, hB, hcover, hinter,
    hDU, hBV, hSB⟩ := selected
  have hSin : S ⊆ interior B := by
    rw [hB.interior_eq_sdiff_of_finrank_eq rfl]
    intro x hx
    refine ⟨hSB hx, ?_⟩
    rintro (hxW | hxV)
    · exact disjoint_left.mp hWS hxW hx
    · exact (hBV.symm.subset hxV).2.2 (hST hx)
  have hDS : Disjoint D S := by
    refine disjoint_left.mpr ?_
    intro x hxD hxS
    exact disjoint_left.mp hWS (hinter.subset ⟨hxD, hSB hxS⟩) hxS
  refine ⟨D, B, U, V, hU, hV, hUV, hUVi, hD, hB, hcover, hinter,
    hDU, hBV, hSin, hDS, ?_, ?_⟩
  · intro x hx
    exact ⟨hcover.subset (Or.inl hx), fun hxS ↦ disjoint_left.mp hDS hx hxS⟩
  · intro K hK hKT hKW hmeet
    have hKB : K ⊆ B := by
      rcases isPreconnected_subset_one_cut_piece hK hD.isCompact.isClosed
          hB.isCompact.isClosed (hKT.trans hcover.symm.subset) hinter hKW with hKD | hKB
      · obtain ⟨x, hxK, hxS⟩ := hmeet
        exact (disjoint_left.mp hDS (hKD hxK) hxS).elim
      · exact hKB
    exact disjoint_left.mpr fun x hxD hxK ↦
      disjoint_left.mp hKW hxK (hinter.subset ⟨hxD, hKB hxK⟩)

end PoincareConjecture.M76.Dehn.Annuli
