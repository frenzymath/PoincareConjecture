import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected











set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn


theorem isPreconnected_subset_one_cut_piece
    {X : Type*} [TopologicalSpace X] {K A B W : Set X}
    (hK : IsPreconnected K) (hA : IsClosed A) (hB : IsClosed B)
    (hsub : K ⊆ A ∪ B) (hinter : A ∩ B = W) (hdisj : Disjoint K W) :
    K ⊆ A ∨ K ⊆ B := by
  classical
  by_contra h
  push Not at h
  obtain ⟨x, hxK, hxA⟩ := Set.not_subset.mp h.1
  obtain ⟨y, hyK, hyB⟩ := Set.not_subset.mp h.2
  obtain ⟨z, hzK, hzAB⟩ := isPreconnected_closed_iff.mp hK A B hA hB hsub
    ⟨y, hyK, (hsub hyK).resolve_right hyB⟩
    ⟨x, hxK, (hsub hxK).resolve_left hxA⟩
  exact Set.disjoint_left.mp hdisj hzK (hinter.subset hzAB)

private theorem exists_cut_away_from_connected_set
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q W K : Set E} {a b : E}
    (hS : IsFinitePLBallPair (ℝ × ℝ) S Q)
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b)
    (hproper : W \ {a, b} ⊆ S \ Q)
    (hK : IsPreconnected K) (hKS : K ⊆ S) (hKW : Disjoint K W) :
    ∃ A B U V : Set E,
      IsFinitePLBallPair (ℝ × ℝ) A (U ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) B (W ∪ V) ∧
      A ∪ B = S ∧ A ∩ B = W ∧ A ∩ Q = U ∧ B ∩ Q = V ∧ K ⊆ B := by
  obtain ⟨U, V, hU, hV, hUV, hUVi⟩ := hS.exists_boundary_arcs ha hb hab
  obtain ⟨A, B, hA, hB, hAB, hABi, hAQ, hBQ⟩ :=
    hS.exists_proper_arc_cut hU hV hW hab hUVi.subset hUV hproper
  rcases isPreconnected_subset_one_cut_piece hK hA.isCompact.isClosed hB.isCompact.isClosed
      (hKS.trans hAB.symm.subset) hABi hKW with hKA | hKB
  · refine ⟨B, A, V, U, ?_, ?_, ?_, ?_, hBQ, hAQ, hKA⟩
    · simpa only [union_comm] using hB
    · simpa only [union_comm] using hA
    · simpa only [union_comm] using hAB
    · simpa only [inter_comm] using hABi
  · exact ⟨A, B, U, V, hA, hB, hAB, hABi, hAQ, hBQ, hKB⟩





theorem exists_two_proper_arc_cuts_with_union
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q W Z : Set E} {a b c d : E}
    (hS : IsFinitePLBallPair (ℝ × ℝ) S Q)
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hZ : IsFinitePLBallPair ℝ Z {c, d})
    (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q) (hd : d ∈ Q)
    (hab : a ≠ b) (hcd : c ≠ d) (hdisj : Disjoint W Z)
    (hproperW : W \ {a, b} ⊆ S \ Q)
    (hproperZ : Z \ {c, d} ⊆ S \ Q) :
    ∃ A M C : Set E,
      IsFinitePLBallPair (ℝ × ℝ) A ((A ∩ Q) ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) M (((M ∩ Q) ∪ W) ∪ Z) ∧
      IsFinitePLBallPair (ℝ × ℝ) C ((C ∩ Q) ∪ Z) ∧
      (A ∪ M) ∪ C = S ∧ A ∩ M = W ∧ M ∩ C = Z ∧ Disjoint A C ∧
      IsFinitePLBallPair (ℝ × ℝ) (M ∪ C) (((M ∪ C) ∩ Q) ∪ W) := by
  have hZS : Z ⊆ S := by
    intro x hx
    by_cases hmem : x ∈ ({c, d} : Set E)
    · rcases hmem with rfl | rfl
      · exact hS.1 hc
      · exact hS.1 hd
    · exact (hproperZ ⟨hx, hmem⟩).1
  obtain ⟨A, B, U, V, hA, hB, hAB, hABi, hAQ, hBQ, hZB⟩ :=
    exists_cut_away_from_connected_set hS hW ha hb hab hproperW
      hZ.isConnected.isPreconnected hZS hdisj.symm
  have hWB : W ⊆ B := hABi.symm.subset.trans inter_subset_right
  have hcV : c ∈ V := hBQ.subset ⟨hZB (hZ.1 (by simp)), hc⟩
  have hdV : d ∈ V := hBQ.subset ⟨hZB (hZ.1 (by simp)), hd⟩
  have hproperZB : Z \ {c, d} ⊆ B \ (W ∪ V) := by
    intro x hx
    refine ⟨hZB hx.1, ?_⟩
    rintro (hxW | hxV)
    · exact Set.disjoint_left.mp hdisj hxW hx.1
    · exact (hproperZ hx).2 (hBQ.symm.subset hxV).2
  obtain ⟨C, M, R, T, hC, hM, hCM, hCMi, hCR, hMT, hWM⟩ :=
    exists_cut_away_from_connected_set hB hZ (Or.inr hcV) (Or.inr hdV)
      hcd hproperZB hW.isConnected.isPreconnected hWB hdisj
  have hMB : M ⊆ B := subset_union_right.trans hCM.subset
  have hCB : C ⊆ B := subset_union_left.trans hCM.subset
  have hAM : A ∩ M = W := by
    apply Subset.antisymm
    · exact fun x hx => hABi.subset ⟨hx.1, hMB hx.2⟩
    · exact fun x hx => ⟨(hABi.symm.subset hx).1, hWM hx⟩
  have hAC : Disjoint A C := by
    apply Set.disjoint_left.mpr
    intro x hxA hxC
    have hxW := hABi.subset ⟨hxA, hCB hxC⟩
    have hxZ := hCMi.subset ⟨hxC, hWM hxW⟩
    exact Set.disjoint_left.mp hdisj hxW hxZ
  have hT : T = (M ∩ Q) ∪ W := by
    rw [← hMT]
    ext x
    constructor
    · rintro ⟨hxM, hxW | hxV⟩
      · exact Or.inr hxW
      · exact Or.inl ⟨hxM, (hBQ.symm.subset hxV).2⟩
    · rintro (⟨hxM, hxQ⟩ | hxW)
      · exact ⟨hxM, Or.inr (hBQ.subset ⟨hMB hxM, hxQ⟩)⟩
      · exact ⟨hWM hxW, Or.inl hxW⟩
  have hR : R = C ∩ Q := by
    rw [← hCR]
    ext x
    constructor
    · rintro ⟨hxC, hxW | hxV⟩
      · exact False.elim (Set.disjoint_left.mp hAC (hABi.symm.subset hxW).1 hxC)
      · exact ⟨hxC, (hBQ.symm.subset hxV).2⟩
    · rintro ⟨hxC, hxQ⟩
      exact ⟨hxC, Or.inr (hBQ.subset ⟨hCB hxC, hxQ⟩)⟩
  refine ⟨A, M, C, ?_, ?_, ?_, ?_, hAM, ?_, hAC, ?_⟩
  · rwa [hAQ]
  · simpa only [hT, union_comm] using hM
  · rwa [hR] at hC
  · rw [union_assoc, union_comm M C, hCM, hAB]
  · simpa only [inter_comm] using hCMi
  · have hMC : M ∪ C = B := by rwa [union_comm]
    rw [hMC, hBQ]
    simpa only [union_comm] using hB



theorem exists_two_proper_arc_cuts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q W Z : Set E} {a b c d : E}
    (hS : IsFinitePLBallPair (ℝ × ℝ) S Q)
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hZ : IsFinitePLBallPair ℝ Z {c, d})
    (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q) (hd : d ∈ Q)
    (hab : a ≠ b) (hcd : c ≠ d) (hdisj : Disjoint W Z)
    (hproperW : W \ {a, b} ⊆ S \ Q)
    (hproperZ : Z \ {c, d} ⊆ S \ Q) :
    ∃ A M C : Set E,
      IsFinitePLBallPair (ℝ × ℝ) A ((A ∩ Q) ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) M (((M ∩ Q) ∪ W) ∪ Z) ∧
      IsFinitePLBallPair (ℝ × ℝ) C ((C ∩ Q) ∪ Z) ∧
      (A ∪ M) ∪ C = S ∧ A ∩ M = W ∧ M ∩ C = Z ∧ Disjoint A C := by
  obtain ⟨A, M, C, hA, hM, hC, hcover, hAM, hMC, hAC, _⟩ :=
    exists_two_proper_arc_cuts_with_union hS hW hZ ha hb hc hd hab hcd
      hdisj hproperW hproperZ
  exact ⟨A, M, C, hA, hM, hC, hcover, hAM, hMC, hAC⟩

end PoincareConjecture.M76.Dehn
