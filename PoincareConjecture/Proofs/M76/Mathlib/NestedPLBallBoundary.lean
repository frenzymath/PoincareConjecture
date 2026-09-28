import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace Set

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.mem_closure_sdiff_of_nested
    {s b t c : Set E} (hs : IsFinitePLBallPair V s b)
    (ht : IsFinitePLBallPair V t c) (hst : s ⊆ t)
    {x : E} (hxb : x ∈ b) (hxc : x ∉ c) : x ∈ closure (t \ s) := by
  have hxt : x ∈ t := hst (hs.1 hxb)
  obtain ⟨_, C, hC, _, _, e, he, heb⟩ := ht
  have hecopy := he
  obtain ⟨f, hf, hfval⟩ := hecopy
  obtain ⟨g, hg, hgval⟩ := he.symm
  have hfmap (z : E) (hz : z ∈ t) : f z ∈ C :=
    hfval ⟨z, hz⟩ ▸ (e ⟨z, hz⟩).property
  have hinj : InjOn f t := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hfval ⟨z, hz⟩).trans (hzw.trans (hfval ⟨w, hw⟩).symm))))
  have hgmap (y : V) (hy : y ∈ C) : g y ∈ t :=
    hgval ⟨y, hy⟩ ▸ (e.symm ⟨y, hy⟩).property
  have hfg (y : V) (hy : y ∈ C) : f (g y) = y := by
    rw [← hgval ⟨y, hy⟩, ← hfval (e.symm ⟨y, hy⟩), e.apply_symm_apply]
  have hgf (z : E) (hz : z ∈ t) : g (f z) = z := by
    rw [← hfval ⟨z, hz⟩, ← hgval (e ⟨z, hz⟩), e.symm_apply_apply]
  have hsmall := hs.image_of_subset hf hst hinj
  have hxfront : f x ∈ frontier (f '' s) := by
    rw [hsmall.frontier_eq_of_finrank_eq rfl]
    exact mem_image_of_mem f hxb
  have hxint : f x ∈ interior C := by
    by_contra hn
    have hxfrontC : f x ∈ frontier C := ⟨subset_closure (hfmap x hxt), hn⟩
    exact hxc ((heb ⟨x, hxt⟩).mpr (by rwa [hfval]))
  have hxcompl : f x ∈ closure (f '' s)ᶜ := by
    rw [closure_compl]
    exact hxfront.2
  have hxcl : f x ∈ closure (C \ f '' s) :=
    closure_mono (inter_subset_inter_left _ interior_subset)
      (isOpen_interior.inter_closure ⟨hxint, hxcompl⟩)
  have hmap : MapsTo g (C \ f '' s) (t \ s) := by
    intro y hy
    refine ⟨hgmap y hy.1, ?_⟩
    intro hys
    exact hy.2 ⟨g y, hys, hfg y hy.1⟩
  have hcontinuous : ContinuousOn g (closure (C \ f '' s)) :=
    hg.continuousOn.mono (closure_minimal sdiff_subset hC.isClosed)
  have hresult := hmap.closure_of_continuousOn hcontinuous hxcl
  rwa [hgf x hxt] at hresult

theorem IsFinitePLBallPair.boundary_eq_of_same_carrier
    {s b c : Set E} (hb : IsFinitePLBallPair V s b)
    (hc : IsFinitePLBallPair V s c) : b = c := by
  apply Subset.antisymm
  · intro x hx
    by_contra hn
    have h := hb.mem_closure_sdiff_of_nested hc Subset.rfl hx hn
    simp only [sdiff_self, closure_empty, mem_empty_iff_false] at h
  · intro x hx
    by_contra hn
    have h := hc.mem_closure_sdiff_of_nested hb Subset.rfl hx hn
    simp only [sdiff_self, closure_empty, mem_empty_iff_false] at h

end Set
