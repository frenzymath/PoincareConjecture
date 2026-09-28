import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.TwoSidedCollarStrips
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
open Set

variable {E X : Type*} [TopologicalSpace E] [T2Space E]
  [TopologicalSpace X] [T2Space X]

theorem ContinuousOn.closure_image_collar_strip
    {A : Set E} (hA : IsCompact A) {c : E × ℝ → X}
    (hc : ContinuousOn c (A ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1) :
    closure (c '' (A ×ˢ Ioo (-ε) ε)) = c '' (A ×ˢ Icc (-ε) ε) := by
  have hsub : A ×ˢ Icc (-ε) ε ⊆ A ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩
  have hcl : closure (A ×ˢ Ioo (-ε) ε) = A ×ˢ Icc (-ε) ε := by
    rw [closure_prod_eq, hA.isClosed.closure_eq, closure_Ioo (by linarith : -ε ≠ ε)]
  apply le_antisymm
  · apply closure_minimal
    · exact image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
    · exact ((hA.prod isCompact_Icc).image_of_continuousOn (hc.mono hsub)).isClosed
  · rw [← hcl]
    apply ContinuousOn.image_closure
    rw [hcl]
    exact hc.mono hsub

theorem Topology.IsEmbedding.frontier_image_collar_strip
    {A : Set E} (hA : IsCompact A) {c : E × ℝ → X}
    (hc : Topology.IsEmbedding
      (fun z : (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1)
    (ho : IsOpen (c '' (A ×ˢ Ioo (-ε) ε))) :
    frontier (c '' (A ×ˢ Ioo (-ε) ε)) =
      c '' (A ×ˢ {-ε}) ∪ c '' (A ×ˢ {ε}) := by
  have hcont : ContinuousOn c (A ×ˢ Icc (-1 : ℝ) 1) :=
    continuousOn_iff_continuous_domRestrict.mpr hc.continuous
  have hinj : InjOn c (A ×ˢ Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hc.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hsub : A ×ˢ Icc (-ε) ε ⊆ A ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩
  rw [frontier, ho.interior_eq, hcont.closure_image_collar_strip hA hε hεsmall]
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hn⟩
    have hnot : ¬(-ε < z.2 ∧ z.2 < ε) := fun ht => hn ⟨z, ⟨hz.1, ht⟩, rfl⟩
    have heq : z.2 = -ε ∨ z.2 = ε := by
      rcases hz.2 with ⟨hl, hu⟩
      by_cases he : z.2 = -ε
      · exact Or.inl he
      · exact Or.inr (by by_contra hu'; exact hnot ⟨lt_of_le_of_ne hl (Ne.symm he),
          lt_of_le_of_ne hu hu'⟩)
    rcases heq with hl | hu
    · exact Or.inl ⟨z, ⟨hz.1, hl⟩, rfl⟩
    · exact Or.inr ⟨z, ⟨hz.1, hu⟩, rfl⟩
  · intro hx
    have hz : ∃ z ∈ A ×ˢ Icc (-ε) ε, c z = x ∧ (z.2 = -ε ∨ z.2 = ε) := by
      rcases hx with ⟨z, hz, hzx⟩ | ⟨z, hz, hzx⟩
      · exact ⟨z, ⟨hz.1, by rw [show z.2 = -ε from hz.2]; constructor <;> linarith⟩,
          hzx, Or.inl hz.2⟩
      · exact ⟨z, ⟨hz.1, by rw [show z.2 = ε from hz.2]; constructor <;> linarith⟩,
          hzx, Or.inr hz.2⟩
    obtain ⟨z, hz, rfl, hend⟩ := hz
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro ⟨w, hw, heq⟩
    have hwc : w ∈ A ×ˢ Icc (-ε) ε := ⟨hw.1, hw.2.1.le, hw.2.2.le⟩
    have hwz := hinj (hsub hwc) (hsub hz) heq
    subst w
    rcases hend with hend | hend <;> linarith [hw.2.1, hw.2.2]
