import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.TwoSidedCollarFrontier

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem closed_collar_interval_geometry
    {E X : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X] {A : Set E} (hA : IsCompact A)
    (c : E × ℝ → X)
    (hc : ContinuousOn c (A ×ˢ Icc (-1 : ℝ) 1))
    (hi : InjOn c (A ×ˢ Icc (-1 : ℝ) 1))
    {a b : ℝ} (ha : -1 < a) (hab : a < b) (hb : b < 1)
    (ho : IsOpen (c '' (A ×ˢ Ioo a b))) :
    let K := c '' (A ×ˢ Icc a b)
    IsCompact K ∧ interior K = c '' (A ×ˢ Ioo a b) ∧
      closure (interior K) = K ∧
      frontier K = c '' (A ×ˢ {a}) ∪ c '' (A ×ˢ {b}) := by
  let K := c '' (A ×ˢ Icc a b)
  let O := c '' (A ×ˢ Ioo a b)
  have hsub : A ×ˢ Icc a b ⊆ A ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono subset_rfl (Icc_subset_Icc ha.le hb.le)
  have hK : IsCompact K := (hA.prod isCompact_Icc).image_of_continuousOn (hc.mono hsub)
  have hclsource : closure (A ×ˢ Ioo a b) = A ×ˢ Icc a b := by
    rw [closure_prod_eq,hA.isClosed.closure_eq,closure_Ioo hab.ne]
  have hclosure : closure O = K := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)) hK.isClosed
    · change c '' (A ×ˢ Icc a b) ⊆ closure (c '' (A ×ˢ Ioo a b))
      rw [←hclsource]
      apply ContinuousOn.image_closure
      rw [hclsource]
      exact hc.mono hsub
  have hleft (x : E) (hx : x ∈ A) : c (x,a) ∉ interior K := by
    have hout : MapsTo c (A ×ˢ Ioo (-1) a) Kᶜ := by
      rintro z hz ⟨w,hw,heq⟩
      have hzw := hi (hsub hw)
        ⟨hz.1,hz.2.1.le,(hz.2.2.le.trans hab.le).trans hb.le⟩ heq
      have he := congrArg Prod.snd hzw
      linarith [hw.2.1,hz.2.2]
    have hcl : closure (A ×ˢ Ioo (-1) a) = A ×ˢ Icc (-1) a := by
      rw [closure_prod_eq,hA.isClosed.closure_eq,closure_Ioo ha.ne]
    have hcont : ContinuousOn c (closure (A ×ˢ Ioo (-1) a)) := by
      rw [hcl]
      exact hc.mono (prod_mono subset_rfl (Icc_subset_Icc le_rfl (hab.le.trans hb.le)))
    have hm := hout.closure_of_continuousOn hcont
      (hcl.symm.subset (show (x,a) ∈ A ×ˢ Icc (-1) a from ⟨hx,ha.le,le_rfl⟩))
    simpa only [closure_compl,mem_compl_iff] using hm
  have hright (x : E) (hx : x ∈ A) : c (x,b) ∉ interior K := by
    have hout : MapsTo c (A ×ˢ Ioo b 1) Kᶜ := by
      rintro z hz ⟨w,hw,heq⟩
      have hzw := hi (hsub hw)
        ⟨hz.1,ha.le.trans (hab.le.trans hz.2.1.le),hz.2.2.le⟩ heq
      have he := congrArg Prod.snd hzw
      linarith [hw.2.2,hz.2.1]
    have hcl : closure (A ×ˢ Ioo b 1) = A ×ˢ Icc b 1 := by
      rw [closure_prod_eq,hA.isClosed.closure_eq,closure_Ioo hb.ne]
    have hcont : ContinuousOn c (closure (A ×ˢ Ioo b 1)) := by
      rw [hcl]
      exact hc.mono (prod_mono subset_rfl (Icc_subset_Icc (ha.le.trans hab.le) le_rfl))
    have hm := hout.closure_of_continuousOn hcont
      (hcl.symm.subset (show (x,b) ∈ A ×ˢ Icc b 1 from ⟨hx,le_rfl,hb.le⟩))
    simpa only [closure_compl,mem_compl_iff] using hm
  have hint : interior K = O := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := interior_subset hx
      refine ⟨z,⟨hz.1,?_,?_⟩,rfl⟩
      · apply lt_of_le_of_ne hz.2.1
        intro heq
        exact hleft z.1 hz.1 (heq ▸ hx)
      · apply lt_of_le_of_ne hz.2.2
        intro heq
        exact hright z.1 hz.1 (heq ▸ hx)
    · exact interior_maximal (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)) ho
  refine ⟨hK,hint,by rw [hint,hclosure],?_⟩
  rw [hK.isClosed.frontier_eq,hint]
  ext x
  constructor
  · rintro ⟨⟨z,hz,rfl⟩,hnot⟩
    have he : z.2 = a ∨ z.2 = b := by
      by_cases he : z.2 = a
      · exact Or.inl he
      · right
        by_contra he'
        exact hnot ⟨z,⟨hz.1,lt_of_le_of_ne hz.2.1 (Ne.symm he),
          lt_of_le_of_ne hz.2.2 he'⟩,rfl⟩
    exact he.elim (fun h => Or.inl ⟨z,⟨hz.1,h⟩,rfl⟩)
      (fun h => Or.inr ⟨z,⟨hz.1,h⟩,rfl⟩)
  · rintro (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩)
    · have he : z.2 = a := hz.2
      refine ⟨⟨z,⟨hz.1,by rw [he]; exact ⟨le_rfl,hab.le⟩⟩,rfl⟩,?_⟩
      rw [←hint]
      simpa only [←he] using hleft z.1 hz.1
    · have he : z.2 = b := hz.2
      refine ⟨⟨z,⟨hz.1,by rw [he]; exact ⟨hab.le,le_rfl⟩⟩,rfl⟩,?_⟩
      rw [←hint]
      simpa only [←he] using hright z.1 hz.1

end PoincareConjecture.M76
