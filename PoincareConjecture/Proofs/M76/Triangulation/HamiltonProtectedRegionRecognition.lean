import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexThreeRegionBalls











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem hasAlexanderRegionBalls_identifies_closed_region {S C D : Set E}
    (hregions : HasAlexanderRegionBalls S C)
    (hD : IsClosed D) (hne : (interior D).Nonempty)
    (hDf : frontier D = S) (hDC : D ⊆ interior C) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) D S := by
  obtain ⟨U, hU, hUc, hUf, hUC, hUB, hUE⟩ := hregions
  have hVf : frontier (interior D) ⊆ S := hDf ▸ frontier_interior_subset
  have hVU : interior D ⊆ U := by
    intro x hx
    by_contra hxU
    let Z := frontier (C ×ˢ Icc (-1 : ℝ) 1)
    let Q : Set Z := (Subtype.val : Z → E × ℝ) ⁻¹'
      ((Z \ U ×ˢ {1}) \ S ×ˢ {1})
    let W : Set Z := (Subtype.val : Z → E × ℝ) ⁻¹' (interior D ×ˢ {1})
    have hQ : IsPreconnected Q := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      have hsubset : ((Z \ U ×ˢ {(1 : ℝ)}) \ S ×ˢ {1}) ⊆ Z :=
        sdiff_subset.trans sdiff_subset
      rw [image_preimage_eq_of_subset (by simpa using hsubset)]
      exact hUE.isConnected_sdiff.isPreconnected
    have hW : IsOpen W :=
      isOpen_preimage_top_face isOpen_interior (interior_subset.trans hDC)
    have hWf : frontier W ⊆ (Subtype.val : Z → E × ℝ) ⁻¹' (S ×ˢ {1}) := by
      rw [frontier_preimage_top_face isOpen_interior (interior_subset.trans hDC)]
      exact preimage_mono (prod_mono hVf subset_rfl)
    have hdis : Disjoint (frontier W) Q :=
      Set.disjoint_left.mpr fun _ hz hq => hq.2 (hWf hz)
    have hxC : x ∈ C := interior_subset (hDC (interior_subset hx))
    have hxtop : (x, (1 : ℝ)) ∈ Z :=
      prod_singleton_one_subset_frontier_cylinder (Subset.rfl : C ⊆ C) ⟨hxC, rfl⟩
    have hxS : x ∉ S := by
      rw [← hDf]
      exact fun hf => hf.2 hx
    have hQW : (Q ∩ W).Nonempty := by
      refine ⟨⟨(x, 1), hxtop⟩, ⟨⟨hxtop, ?_⟩, ?_⟩, hx, rfl⟩
      · exact fun h => hxU h.1
      · exact fun h => hxS h.1
    have hQsub : Q ⊆ W := hQ.m76_subset_of_disjoint_frontier hW hdis hQW
    have hxbottom : (x, (-1 : ℝ)) ∈ Z := by
      dsimp [Z]
      rw [frontier_prod_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Or.inl ⟨subset_closure hxC, by simp⟩
    have hbottomQ : (⟨(x, -1), hxbottom⟩ : Z) ∈ Q := by
      refine ⟨⟨hxbottom, ?_⟩, ?_⟩ <;> intro h <;> norm_num at h
    have hbad := (hQsub hbottomQ).2
    norm_num at hbad
  have hUV : U ⊆ interior D := by
    apply hUc.isPreconnected.m76_subset_of_disjoint_frontier isOpen_interior
    · apply Set.disjoint_left.mpr
      intro x hx hxU
      have hxF : x ∈ frontier U := hUf.symm ▸ hVf hx
      exact hxF.2 (hU.interior_eq.symm ▸ hxU)
    · obtain ⟨x, hx⟩ := hne
      exact ⟨x, hVU hx, hx⟩
  have hDU : D = closure U := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxi : x ∈ interior D
      · exact subset_closure (hVU hxi)
      · have hxS : x ∈ S := hDf ▸ (show x ∈ frontier D from ⟨subset_closure hx, hxi⟩)
        exact frontier_subset_closure (hUf.symm ▸ hxS)
    · exact closure_minimal (hUV.trans interior_subset) hD
  rwa [← hDU] at hUB

end PoincareConjecture.M76
