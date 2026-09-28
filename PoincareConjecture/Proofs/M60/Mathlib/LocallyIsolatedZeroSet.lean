import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M60




theorem finite_of_locally_mem_or_isolated
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [PreconnectedSpace X]
    {S : Set X} (hproper : S ≠ univ)
    (hlocal : ∀ x : X, S ∈ 𝓝 x ∨ ∀ᶠ y in 𝓝[≠] x, y ∉ S) : S.Finite := by
  have hclosed : IsClosed (interior S) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hx' : S ∉ 𝓝 x := by
      simpa only [mem_compl_iff, mem_interior_iff_mem_nhds] using hx
    have hi := (hlocal x).resolve_left hx'
    rw [eventually_nhdsWithin_iff] at hi
    filter_upwards [hi] with y hy
    change y ∉ interior S
    intro hyS
    by_cases hyx : y = x
    · exact hx (hyx ▸ hyS)
    · exact hy hyx (interior_subset hyS)
  have hempty : interior S = ∅ := by
    rcases isClopen_iff.mp ⟨hclosed, isOpen_interior⟩ with h | h
    · exact h
    · exact False.elim (hproper (univ_subset_iff.mp (h ▸ interior_subset)))
  by_contra hinfinite
  obtain ⟨x, hx⟩ := Set.Infinite.exists_accPt_principal hinfinite
  have hi : ∀ᶠ y in 𝓝[≠] x, y ∉ S := (hlocal x).resolve_left fun h => by
    have hm := mem_interior_iff_mem_nhds.mpr h
    rw [hempty] at hm
    exact hm
  exact (accPt_iff_frequently_nhdsNE.mp hx) hi

end PoincareConjecture.M60
