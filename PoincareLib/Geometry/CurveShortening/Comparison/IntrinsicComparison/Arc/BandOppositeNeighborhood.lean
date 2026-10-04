import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Two.CornerOrientedBands

/-! The opposite boundary arc has an open neighborhood avoiding all bands
already fitted to the trimmed first arc.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, including Claim 19.40,
pp. 470-471. These project constructions supply actual occupied boundary collars
and attachment coverage for the regional Gauss--Bonnet argument.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareMT

/-- A finite closed family of occupied bands with lower arcs inside the original open arc
leaves an open neighborhood of the complete complementary frontier. Source:
`proof-work/tasks/M64/reviews/2026-09-27-intrinsic-boundary-coverage-review.md`, round_1,
semantic check 18. -/
theorem m64Intrinsic_arc_band_carriers_avoid_remainder
    {I : Type*} [Finite I] (S lower : I → Set AnnulusCoordinates)
    (hclosed : ∀ i, IsClosed (S i))
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} {K U : Set AnnulusCoordinates}
    (hU : IsOpen U) (hfront : frontier U = gamma '' Icc 0 T ∪ K)
    (havoid : Disjoint (gamma '' Ioo 0 T) K)
    (hlower : ∀ i, lower i ⊆ gamma '' Ioo 0 T)
    (hregion : ∀ i, S i \ lower i ⊆ U) :
    IsOpen (⋃ i, S i)ᶜ ∧ K ⊆ (⋃ i, S i)ᶜ := by
  refine ⟨(isClosed_iUnion_of_finite hclosed).isOpen_compl, ?_⟩
  intro p hpK hpS
  obtain ⟨i, hpi⟩ := mem_iUnion.mp hpS
  by_cases hp : p ∈ lower i
  · exact disjoint_left.mp havoid (hlower i hp) hpK
  · have hpU := hregion i ⟨hpi, hp⟩
    have hpfront : p ∈ frontier U := hfront ▸ Or.inr hpK
    exact (disjoint_frontier_iff_isOpen.mpr hU).le_bot ⟨hpfront, hpU⟩

end PoincareMT
