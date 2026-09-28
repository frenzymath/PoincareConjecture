import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.DenselyOrdered









set_option autoImplicit false

open Set

variable {E X : Type*} [TopologicalSpace E] [T2Space E]
  [TopologicalSpace X] [T2Space X]



theorem compact_collar_strip_geometry {B : Set E} {K : Set X}
    (hB : IsCompact B) (HB : B ≃ₜ frontier K) (c : E × ℝ → X)
    (hc : ContinuousOn c (B ×ˢ Icc 0 1)) (hi : InjOn c (B ×ˢ Icc 0 1))
    (hinside : MapsTo c (B ×ˢ Icc 0 1) K)
    (hbase : ∀ z : B, c ((z : E), 0) = HB z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IsCompact (c '' (B ×ˢ Icc 0 ε)) ∧ c '' (B ×ˢ Icc 0 ε) ⊆ K ∧
      c '' (B ×ˢ Ico 0 ε) ⊆ c '' (B ×ˢ Icc 0 ε) ∧
      closure (c '' (B ×ˢ Ico 0 ε)) = c '' (B ×ˢ Icc 0 ε) ∧
      (c '' (B ×ˢ Icc 0 ε)) \ (c '' (B ×ˢ Ico 0 ε)) = c '' (B ×ˢ {ε}) ∧
      frontier K ⊆ c '' (B ×ˢ Ico 0 ε) := by
  have hsub : B ×ˢ Icc (0 : ℝ) ε ⊆ B ×ˢ Icc 0 1 := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans hε1⟩
  have hcompact : IsCompact (c '' (B ×ˢ Icc 0 ε)) :=
    (hB.prod isCompact_Icc).image_of_continuousOn (hc.mono hsub)
  have hUN : c '' (B ×ˢ Ico 0 ε) ⊆ c '' (B ×ˢ Icc 0 ε) :=
    image_mono (prod_mono Subset.rfl Ico_subset_Icc_self)
  have hsource : closure (B ×ˢ Ico (0 : ℝ) ε) = B ×ˢ Icc 0 ε := by
    rw [closure_prod_eq, hB.isClosed.closure_eq, closure_Ico hε.ne]
  refine ⟨hcompact, ?_, hUN, ?_, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact hinside (hsub hz)
  · apply Subset.antisymm (closure_minimal hUN hcompact.isClosed)
    have hcont : ContinuousOn c (closure (B ×ˢ Ico (0 : ℝ) ε)) := by
      rw [hsource]
      exact hc.mono hsub
    simpa only [hsource] using hcont.image_closure
  · ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hnot⟩
      have ht : z.2 = ε := le_antisymm hz.2.2 (le_of_not_gt (fun h =>
        hnot ⟨z, ⟨hz.1, hz.2.1, h⟩, rfl⟩))
      exact ⟨z, ⟨hz.1, ht⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have ht : z.2 = ε := mem_singleton_iff.mp hz.2
      have hzN : z ∈ B ×ˢ Icc (0 : ℝ) ε := by
        refine ⟨hz.1, ?_⟩
        rw [ht]
        exact ⟨hε.le, le_rfl⟩
      refine ⟨⟨z, hzN, rfl⟩, ?_⟩
      rintro ⟨w, hw, heq⟩
      have hwN : w ∈ B ×ˢ Icc (0 : ℝ) ε :=
        ⟨hw.1, hw.2.1, hw.2.2.le⟩
      have hwz : w = z := hi (hsub hwN) (hsub hzN) heq
      have hwt : w.2 = ε := (congrArg Prod.snd hwz).trans ht
      exact (lt_irrefl ε) (hwt ▸ hw.2.2)
  · intro x hx
    let z : B := HB.symm ⟨x, hx⟩
    refine ⟨((z : E), 0), ⟨z.property, le_rfl, hε⟩, ?_⟩
    exact (hbase z).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨x, hx⟩))
