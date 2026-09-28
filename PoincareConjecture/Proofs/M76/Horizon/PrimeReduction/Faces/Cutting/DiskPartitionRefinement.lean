import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.NormalArcCuts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76



theorem exists_unique_disk_owner_away_from_cuts
    {E κ : Type*} [TopologicalSpace E] [Finite κ] {S T W : Set E}
    (B : κ → Set E) (hB : ∀ k, IsClosed (B k)) (hcover : (⋃ k, B k) = S)
    (hinter : Pairwise fun k l => B k ∩ B l ⊆ T)
    (hW : IsConnected W) (hWS : W ⊆ S) (hWT : Disjoint W T) :
    ∃! k, W ⊆ B k := by
  classical
  obtain ⟨x, hxW⟩ := hW.nonempty
  obtain ⟨k, hxB⟩ := mem_iUnion.mp (hcover.symm.subset (hWS hxW))
  have hsub : W ⊆ B k := by
    let C := ⋃ l : {l : κ // l ≠ k}, B l
    have hWC : W ⊆ B k ∪ C := by
      intro y hy
      obtain ⟨l, hyl⟩ := mem_iUnion.mp (hcover.symm.subset (hWS hy))
      by_cases hl : l = k
      · exact Or.inl (hl ▸ hyl)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨l, hl⟩, hyl⟩)
    have hsep : W ∩ (B k ∩ C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hyW, hyk, hyC⟩
      obtain ⟨l, hyl⟩ := mem_iUnion.mp hyC
      exact disjoint_left.mp hWT hyW (hinter l.property ⟨hyl, hyk⟩)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hW.isPreconnected
        (B k) C (hB k) (isClosed_iUnion_of_finite fun l => hB l) hWC hsep with h | h
    · exact h
    · obtain ⟨l, hxl⟩ := mem_iUnion.mp (h hxW)
      exact False.elim (disjoint_left.mp hWT hxW (hinter l.property ⟨hxl, hxB⟩))
  refine ⟨k, hsub, ?_⟩
  intro l hl
  by_contra hlk
  exact disjoint_left.mp hWT hxW (hinter hlk ⟨hl hxW, hsub hxW⟩)




theorem exists_proper_arc_disk_partition_refinement
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite κ]
    {S Q T W : Set E} {p q : E} (B R : κ → Set E)
    (hB : ∀ k, IsFinitePLBallPair (ℝ × ℝ) (B k) (R k))
    (hR : ∀ k, R k = B k ∩ (Q ∪ T))
    (hcover : (⋃ k, B k) = S)
    (hinter : Pairwise fun k l => B k ∩ B l ⊆ T)
    (hW : IsFinitePLBallPair ℝ W {p, q}) (hpq : p ≠ q)
    (hWS : W ⊆ S) (hWrim : ({p, q} : Set E) = W ∩ Q) (hWT : Disjoint W T) :
    ∃ B' R' : Option κ → Set E,
      (∀ k, IsFinitePLBallPair (ℝ × ℝ) (B' k) (R' k)) ∧
      (∀ k, R' k = B' k ∩ (Q ∪ (T ∪ W))) ∧
      (⋃ k, B' k) = S ∧
      Pairwise (fun k l => B' k ∩ B' l ⊆ T ∪ W) := by
  classical
  obtain ⟨k, hWB, _⟩ := exists_unique_disk_owner_away_from_cuts B (fun l => (hB l).isCompact.isClosed)
    hcover hinter hW.isConnected hWS hWT
  have hpR : p ∈ R k := (hR k).symm.subset
    ⟨hWB (hW.1 (by simp)), Or.inl ((hWrim.subset (by simp)).2)⟩
  have hqR : q ∈ R k := (hR k).symm.subset
    ⟨hWB (hW.1 (by simp)), Or.inl ((hWrim.subset (by simp)).2)⟩
  have hproper : W \ {p, q} ⊆ B k \ R k := by
    intro x hx
    refine ⟨hWB hx.1, ?_⟩
    intro hxr
    rcases ((hR k).subset hxr).2 with hxQ | hxT
    · exact hx.2 (hWrim.symm.subset ⟨hx.1, hxQ⟩)
    · exact disjoint_left.mp hWT hx.1 hxT
  obtain ⟨U, V, hU, hV, hUV, hUiV⟩ := (hB k).exists_boundary_arcs hpR hqR hpq
  obtain ⟨A, C, hA, hC, hAC, hAiC, hAR, hCR⟩ :=
    (hB k).exists_proper_arc_cut hU hV hW hpq hUiV.subset hUV hproper
  have hAB : A ⊆ B k := subset_union_left.trans hAC.subset
  have hCB : C ⊆ B k := subset_union_right.trans hAC.subset
  have hWA : W ⊆ A := hAiC.symm.subset.trans inter_subset_left
  have hWC : W ⊆ C := hAiC.symm.subset.trans inter_subset_right
  have hother (l : κ) (hl : l ≠ k) : Disjoint (B l) W := by
    apply disjoint_left.mpr
    intro x hxl hxW
    exact disjoint_left.mp hWT hxW (hinter hl ⟨hxl, hWB hxW⟩)
  let B' : Option κ → Set E := fun z => match z with
    | none => C
    | some l => if l = k then A else B l
  let R' : Option κ → Set E := fun z => B' z ∩ (Q ∪ (T ∪ W))
  have hRA : A ∩ (Q ∪ (T ∪ W)) = U ∪ W := by
    ext x
    constructor
    · rintro ⟨hxA, hxQ | hxT | hxW⟩
      · exact Or.inl (hAR.subset ⟨hxA, (hR k).symm.subset ⟨hAB hxA, Or.inl hxQ⟩⟩)
      · exact Or.inl (hAR.subset ⟨hxA, (hR k).symm.subset ⟨hAB hxA, Or.inr hxT⟩⟩)
      · exact Or.inr hxW
    · rintro (hxU | hxW)
      · have hx := hAR.symm.subset hxU
        refine ⟨hx.1, ?_⟩
        rcases ((hR k).subset hx.2).2 with hxQ | hxT
        · exact Or.inl hxQ
        · exact Or.inr (Or.inl hxT)
      · exact ⟨hWA hxW, Or.inr (Or.inr hxW)⟩
  have hRC : C ∩ (Q ∪ (T ∪ W)) = W ∪ V := by
    ext x
    constructor
    · rintro ⟨hxC, hxQ | hxT | hxW⟩
      · exact Or.inr (hCR.subset ⟨hxC, (hR k).symm.subset ⟨hCB hxC, Or.inl hxQ⟩⟩)
      · exact Or.inr (hCR.subset ⟨hxC, (hR k).symm.subset ⟨hCB hxC, Or.inr hxT⟩⟩)
      · exact Or.inl hxW
    · rintro (hxW | hxV)
      · exact ⟨hWC hxW, Or.inr (Or.inr hxW)⟩
      · have hx := hCR.symm.subset hxV
        refine ⟨hx.1, ?_⟩
        rcases ((hR k).subset hx.2).2 with hxQ | hxT
        · exact Or.inl hxQ
        · exact Or.inr (Or.inl hxT)
  have hRO (l : κ) (hl : l ≠ k) : B l ∩ (Q ∪ (T ∪ W)) = R l := by
    rw [hR l]
    ext x
    constructor
    · rintro ⟨hxl, hxQ | hxT | hxW⟩
      · exact ⟨hxl, Or.inl hxQ⟩
      · exact ⟨hxl, Or.inr hxT⟩
      · exact False.elim (disjoint_left.mp (hother l hl) hxl hxW)
    · rintro ⟨hxl, hxQ | hxT⟩
      · exact ⟨hxl, Or.inl hxQ⟩
      · exact ⟨hxl, Or.inr (Or.inl hxT)⟩
  refine ⟨B', R', ?_, fun _ => rfl, ?_, ?_⟩
  · intro z
    cases z with
    | none => simpa only [R', B', hRC] using hC
    | some l =>
      by_cases hl : l = k
      · simpa [R', B', hl, hRA] using hA
      · simpa only [R', B', hl, if_false, hRO l hl] using hB l
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨z, hz⟩ := mem_iUnion.mp hx
      apply hcover.subset
      cases z with
      | none => exact mem_iUnion.mpr ⟨k, hCB hz⟩
      | some l =>
        by_cases hl : l = k
        · have hxA : x ∈ A := by simpa only [B', hl, if_pos rfl] using hz
          exact mem_iUnion.mpr ⟨k, hAB hxA⟩
        · exact mem_iUnion.mpr ⟨l, by simpa only [B', hl, if_false] using hz⟩
    · intro x hx
      obtain ⟨l, hxl⟩ := mem_iUnion.mp (hcover.symm.subset hx)
      by_cases hl : l = k
      · rcases hAC.symm.subset (hl ▸ hxl) with hxA | hxC
        · exact mem_iUnion.mpr ⟨some k, by simpa only [B', if_pos rfl] using hxA⟩
        · exact mem_iUnion.mpr ⟨none, hxC⟩
      · exact mem_iUnion.mpr ⟨some l, by simpa only [B', hl, if_false] using hxl⟩
  · intro z w hzw x hx
    cases z with
    | none =>
      cases w with
      | none => exact False.elim (hzw rfl)
      | some l =>
        by_cases hl : l = k
        · have hxA : x ∈ A := by simpa only [B', hl, if_pos rfl] using hx.2
          exact Or.inr (hAiC.subset ⟨hxA, hx.1⟩)
        · have hxl : x ∈ B l := by simpa only [B', hl, if_false] using hx.2
          exact Or.inl (hinter hl ⟨hxl, hCB hx.1⟩)
    | some l =>
      cases w with
      | none =>
        by_cases hl : l = k
        · have hxA : x ∈ A := by simpa only [B', hl, if_pos rfl] using hx.1
          exact Or.inr (hAiC.subset ⟨hxA, hx.2⟩)
        · have hxl : x ∈ B l := by simpa only [B', hl, if_false] using hx.1
          exact Or.inl (hinter hl ⟨hxl, hCB hx.2⟩)
      | some m =>
        have hlm : l ≠ m := fun he => hzw (congrArg some he)
        by_cases hl : l = k
        · have hm : m ≠ k := fun he => hlm (hl.trans he.symm)
          have hxA : x ∈ A := by simpa only [B', hl, if_pos rfl] using hx.1
          have hxm : x ∈ B m := by simpa only [B', hm, if_false] using hx.2
          exact Or.inl (hinter hm ⟨hxm, hAB hxA⟩)
        · have hxl : x ∈ B l := by simpa only [B', hl, if_false] using hx.1
          by_cases hm : m = k
          · have hxA : x ∈ A := by simpa only [B', hm, if_pos rfl] using hx.2
            exact Or.inl (hinter hl ⟨hxl, hAB hxA⟩)
          · have hxm : x ∈ B m := by simpa only [B', hm, if_false] using hx.2
            exact Or.inl (hinter hlm ⟨hxl, hxm⟩)

end PoincareConjecture.M76
