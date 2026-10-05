import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Products
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry

/-!
# Compact projective-plane collars in the actual limit

The closed collar of width two fits inside one open exhaustion domain;
its inner collar has the width in the surgery exclusion predicate.
Source: Morgan--Tian, Proposition 17.1, pp. 407-408, and the reviewed
`proof-work/tasks/M47/derivations/limit-rp2-compact-collar.md`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareMT.M47

variable {X : Type*} [TopologicalSpace X]

/-- The actual closed product collar, with fixed outer width two. -/
def limitRP2CompactCollar (h : X ≃ₜ (RealProjectiveTwo × ℝ)) : Set X :=
  h.symm '' ((univ : Set RealProjectiveTwo) ×ˢ Icc (-2 : ℝ) 2)

/-- The literal inner product collar, with the width used by surgery. -/
def limitRP2InnerCollar (h : X ≃ₜ (RealProjectiveTwo × ℝ))
    (p : RealProjectiveTwo × Ioo (-1 : ℝ) 1) : X :=
  h.symm (p.1, p.2.val)

/-- Compactness uses the actual antipodal quotient of the unit sphere. -/
theorem limitRP2CompactCollar_isCompact (h : X ≃ₜ (RealProjectiveTwo × ℝ)) :
    IsCompact (limitRP2CompactCollar h) := by
  exact (isCompact_univ.prod isCompact_Icc).image h.symm.continuous

/-- The inner collar retains the product topology and its normal interval. -/
theorem limitRP2InnerCollar_isOpenEmbedding
    (h : X ≃ₜ (RealProjectiveTwo × ℝ)) :
    Topology.IsOpenEmbedding (limitRP2InnerCollar h) := by
  exact h.symm.isOpenEmbedding.comp
    (Topology.IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal)

/-- Every inner-collar point lies in the fixed compact outer collar. -/
theorem limitRP2InnerCollar_mem_compact
    (h : X ≃ₜ (RealProjectiveTwo × ℝ))
    (p : RealProjectiveTwo × Ioo (-1 : ℝ) 1) :
    limitRP2InnerCollar h p ∈ limitRP2CompactCollar h := by
  refine ⟨(p.1, p.2.val), ⟨mem_univ _, ?_⟩, rfl⟩
  constructor <;> linarith [p.2.property.1, p.2.property.2]

/-- An inner collar landing in an open set remains an open embedding
after codomain restriction to that set. -/
theorem limitRP2InnerCollar_isOpenEmbedding_codRestrict
    (h : X ≃ₜ (RealProjectiveTwo × ℝ)) {U : Set X} (hU : IsOpen U)
    (hcover : limitRP2CompactCollar h ⊆ U) :
    Topology.IsOpenEmbedding (fun p : RealProjectiveTwo × Ioo (-1 : ℝ) 1 =>
      (⟨limitRP2InnerCollar h p,
        hcover (limitRP2InnerCollar_mem_compact h p)⟩ : U)) := by
  exact Topology.IsOpenEmbedding.of_comp _ hU.isOpenEmbedding_subtypeVal
    (limitRP2InnerCollar_isOpenEmbedding h)

/-- Compact subsets of the actual increasing exhaustion eventually lie
in every domain. This is derived coverage, not an additional input. -/
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

/-- The entire compact RP2 collar fits in one literal convergence domain. -/
theorem limitRP2_compactCollar_subset_domain {J : Set ℝ}
    {L : BlowupLimitFlow.{u} J} (E : BlowupExhaustion L)
    (h : L.sliceCarrier.carrier ≃ₜ (RealProjectiveTwo × ℝ)) :
    ∃ k, limitRP2CompactCollar h ⊆ E.space k :=
  (limitRP2_eventually_compact_subset E (limitRP2CompactCollar_isCompact h)).exists

end PoincareMT.M47
