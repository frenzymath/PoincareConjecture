import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue










set_option autoImplicit false

open Set Filter
open scoped Topology





theorem m64ContinuousOn_avoids_closed_of_local_contact
    {X : Type*} [TopologicalSpace X] {gamma : ℝ → X} {L : ℝ} {C : Set X}
    (hc : ContinuousOn gamma (Icc 0 L)) (hC : IsClosed C) (hzero : gamma 0 ∉ C)
    (hlocal : ∀ u ∈ Ioo 0 L, gamma u ∈ C → ∀ᶠ t in 𝓝 u, gamma t ∈ C) :
    ∀ u ∈ Ioo 0 L, gamma u ∉ C := by
  let O := Ioo (0 : ℝ) L ∩ interior (gamma ⁻¹' C)
  have hO : IsOpen O := isOpen_Ioo.inter isOpen_interior
  have hclosed : IsClosed (Icc (0 : ℝ) L ∩ gamma ⁻¹' C) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc hC
  have hclosure : closure O ⊆ Icc 0 L ∩ gamma ⁻¹' C := by
    apply closure_minimal _ hclosed
    intro t ht
    exact ⟨Ioo_subset_Icc_self ht.1, interior_subset ht.2⟩
  have hlimit : closure O ∩ Ico 0 L ⊆ O := by
    intro t ht
    have hmem : gamma t ∈ C := (hclosure ht.1).2
    have htpos : 0 < t := by
      rcases ht.2.1.eq_or_lt with heq | hlt
      · exact False.elim (hzero (heq.symm ▸ hmem))
      · exact hlt
    exact ⟨⟨htpos, ht.2.2⟩, mem_interior_iff_mem_nhds.mpr (hlocal t ⟨htpos, ht.2.2⟩ hmem)⟩
  intro u hu hmem
  have huO : u ∈ O :=
    ⟨hu, mem_interior_iff_mem_nhds.mpr (hlocal u hu hmem)⟩
  have hall : Ico (0 : ℝ) L ⊆ O :=
    isPreconnected_Ico.subset_of_closure_inter_subset
      hO ⟨u, ⟨hu.1.le, hu.2⟩, huO⟩ hlimit
  exact (lt_irrefl (0 : ℝ)) (hall ⟨le_rfl, hu.1.trans hu.2⟩).1.1
