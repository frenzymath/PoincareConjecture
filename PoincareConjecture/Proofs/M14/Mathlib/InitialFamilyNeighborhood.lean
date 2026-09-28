import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M14




theorem exists_open_initial_family_neighborhood {E : Type*} [TopologicalSpace E]
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {a b : ℝ} (hab : a < b) {S : Set (E × ℝ)}
    (hS : S ∈ 𝓝[U ×ˢ Icc a b] (x, a)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ d : ℝ, a < d ∧ d ≤ b ∧ V ×ˢ Icc a d ⊆ S := by
  rw [nhdsWithin_prod_eq, nhdsWithin_eq_nhds.mpr (hU.mem_nhds hx)] at hS
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.mp hS
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (inter_mem hA (hU.mem_nhds hx))
  obtain ⟨N, hN, haN, hNB⟩ := mem_nhdsWithin.mp hB
  obtain ⟨l, u, ⟨hla, hau⟩, hln⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hN.mem_nhds haN)
  obtain ⟨d, had, hd⟩ := exists_between (lt_min hab hau)
  have hdb : d ≤ b := hd.le.trans (min_le_left _ _)
  refine ⟨V, hV, hxV, fun _ hy => (hVsub hy).2, d, had, hdb, ?_⟩
  intro z hz
  exact hAB ⟨(hVsub hz.1).1, hNB
    ⟨hln ⟨hla.trans_le hz.2.1, hz.2.2.trans_lt (hd.trans_le (min_le_right _ _))⟩,
      hz.2.1, hz.2.2.trans hdb⟩⟩

end PoincareConjecture.M14
