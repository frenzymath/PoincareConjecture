import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M47

variable {X : Type*} [TopologicalSpace X]

def limitRP2CompactCollar (h : X ≃ₜ (RealProjectiveTwo × ℝ)) : Set X :=
  h.symm '' ((univ : Set RealProjectiveTwo) ×ˢ Icc (-2 : ℝ) 2)

def limitRP2InnerCollar (h : X ≃ₜ (RealProjectiveTwo × ℝ))
    (p : RealProjectiveTwo × Ioo (-1 : ℝ) 1) : X :=
  h.symm (p.1, p.2.val)

theorem limitRP2CompactCollar_isCompact (h : X ≃ₜ (RealProjectiveTwo × ℝ)) :
    IsCompact (limitRP2CompactCollar h) := by
  exact (isCompact_univ.prod isCompact_Icc).image h.symm.continuous

theorem limitRP2InnerCollar_isOpenEmbedding
    (h : X ≃ₜ (RealProjectiveTwo × ℝ)) :
    Topology.IsOpenEmbedding (limitRP2InnerCollar h) := by
  exact h.symm.isOpenEmbedding.comp
    (Topology.IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal)

theorem limitRP2InnerCollar_mem_compact
    (h : X ≃ₜ (RealProjectiveTwo × ℝ))
    (p : RealProjectiveTwo × Ioo (-1 : ℝ) 1) :
    limitRP2InnerCollar h p ∈ limitRP2CompactCollar h := by
  refine ⟨(p.1, p.2.val), ⟨mem_univ _, ?_⟩, rfl⟩
  constructor <;> linarith [p.2.property.1, p.2.property.2]

theorem limitRP2InnerCollar_isOpenEmbedding_codRestrict
    (h : X ≃ₜ (RealProjectiveTwo × ℝ)) {U : Set X} (hU : IsOpen U)
    (hcover : limitRP2CompactCollar h ⊆ U) :
    Topology.IsOpenEmbedding (fun p : RealProjectiveTwo × Ioo (-1 : ℝ) 1 =>
      (⟨limitRP2InnerCollar h p,
        hcover (limitRP2InnerCollar_mem_compact h p)⟩ : U)) := by
  exact Topology.IsOpenEmbedding.of_comp _ hU.isOpenEmbedding_subtypeVal
    (limitRP2InnerCollar_isOpenEmbedding h)

theorem limitRP2_eventually_compact_subset {J : Set ℝ}
    {L : BlowupLimitFlow.{u} J} (E : BlowupExhaustion L)
    {B : Set L.sliceCarrier.carrier} (hB : IsCompact B) :
    ∀ᶠ k : ℕ in atTop, B ⊆ E.space k := by
  obtain ⟨k, hk⟩ := hB.elim_directed_cover E.space E.space_open
    (by rw [E.space_covers]; exact subset_univ _) (by
      intro i j
      exact ⟨max i j, E.space_increasing (le_max_left _ _),
        E.space_increasing (le_max_right _ _)⟩)
  exact eventually_atTop.2 ⟨k, fun j hj => hk.trans (E.space_increasing hj)⟩

theorem limitRP2_compactCollar_subset_domain {J : Set ℝ}
    {L : BlowupLimitFlow.{u} J} (E : BlowupExhaustion L)
    (h : L.sliceCarrier.carrier ≃ₜ (RealProjectiveTwo × ℝ)) :
    ∃ k, limitRP2CompactCollar h ⊆ E.space k :=
  (limitRP2_eventually_compact_subset E (limitRP2CompactCollar_isCompact h)).exists

end PoincareConjecture.M47
