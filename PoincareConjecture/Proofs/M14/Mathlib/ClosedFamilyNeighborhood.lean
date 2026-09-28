import PoincareConjecture.Proofs.M14.Mathlib.ClosedLeftNeighborhood
import Mathlib.Topology.Constructions









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M14




theorem exists_open_closed_family_neighborhood {E : Type*} [TopologicalSpace E]
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {a b t : ℝ} (hat : a < t) (htb : t ≤ b) {S : Set (E × ℝ)}
    (hS : S ∈ 𝓝[U ×ˢ Icc a b] (x, t)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ c d : ℝ, a < c ∧ c < t ∧ t ≤ d ∧ d ≤ b ∧ V ×ˢ Icc c d ⊆ S ∧
        Icc c d ∈ 𝓝[Icc a b] t := by
  rw [nhdsWithin_prod_eq, nhdsWithin_eq_nhds.mpr (hU.mem_nhds hx)] at hS
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.mp hS
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (inter_mem hA (hU.mem_nhds hx))
  obtain ⟨c, d, hac, hct, htd, hdb, hC, hnear⟩ :=
    exists_closed_left_neighborhood hat htb hB
  exact ⟨V, hV, hxV, fun _ hy => (hVsub hy).2, c, d, hac, hct, htd, hdb,
    fun z hz => hAB ⟨(hVsub hz.1).1, hC hz.2⟩, hnear⟩

end PoincareConjecture.M14
