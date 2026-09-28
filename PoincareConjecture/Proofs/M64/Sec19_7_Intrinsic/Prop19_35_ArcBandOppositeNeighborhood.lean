import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoCornerOrientedBands









noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture





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

end PoincareConjecture
