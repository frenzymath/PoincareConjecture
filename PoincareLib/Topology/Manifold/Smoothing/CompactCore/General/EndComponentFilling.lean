import PoincareLib.Topology.Manifold.Smoothing.CompactCore.General.WeakEndNoncompact
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Topology.Mathlib.ConnectedComponentFilling

/-!
# The actual exterior component selected by the frozen weak end

A connected tail is contained in one literal component of the compact
core complement. Its complement is a closed subset of the compact
tail cutoff. Filling uses no ball recognition or finite component count.
See Wall derivation008, sections1--2 and Hamilton1976 Lemma2.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [LocallyConnectedSpace Y] [PreconnectedSpace Y]

/-- The frozen end selects a literal exterior component with compact
connected complement. Its full frontier lies in the original frontier,
and every other component has compact closure. See Wall008, sections1--2. -/
theorem HasOneSimplyConnectedEnd.exists_compact_connected_filling
    (hend : HasOneSimplyConnectedEnd Y) {K : Set Y}
    (hK : IsCompact K) (hconn : IsConnected K) :
    ∃ x ∈ Kᶜ,
      let U := connectedComponentIn Kᶜ x
      IsOpen U ∧ IsConnected U ∧ K ⊆ Uᶜ ∧ IsCompact Uᶜ ∧ IsConnected Uᶜ ∧
        frontier U ⊆ frontier K ∧ ¬ IsCompact (closure U) ∧
        ∀ y ∈ Kᶜ, connectedComponentIn Kᶜ y ≠ U →
          IsCompact (closure (connectedComponentIn Kᶜ y)) := by
  obtain ⟨D, hD, hKD, htail, _⟩ := hend K hK
  obtain ⟨x, hxD⟩ := htail.nonempty
  have hxK : x ∈ Kᶜ := fun hx => hxD (interior_subset (hKD hx))
  let U := connectedComponentIn Kᶜ x
  have hopen : IsOpen U := hK.isClosed.isOpen_compl.connectedComponentIn
  have htailU : Dᶜ ⊆ U := htail.isPreconnected.subset_connectedComponentIn hxD
    (fun _ hy hk => hy (interior_subset (hKD hk)))
  have hfilled : IsCompact Uᶜ := hD.of_isClosed_subset hopen.isClosed_compl
    (fun y hy => by
      by_contra hyD
      exact hy (htailU hyD))
  have hKU : K ⊆ Uᶜ := fun _ hy hU => connectedComponentIn_subset Kᶜ x hU hy
  refine ⟨x, hxK, hopen, isConnected_connectedComponentIn_iff.mpr hxK,
    hKU, hfilled, hK.isClosed.isConnected_compl_connectedComponentIn hconn x,
    hK.isClosed.frontier_connectedComponentIn_compl_subset_frontier x, ?_, ?_⟩
  · intro hcl
    apply hend.not_isCompact_univ
    have heq : Uᶜ ∪ closure U = univ := by
      apply eq_univ_of_forall
      intro y
      by_cases hy : y ∈ U
      · exact Or.inr (subset_closure hy)
      · exact Or.inl hy
    exact heq ▸ hfilled.union hcl
  · intro y _ hne
    have hsub : connectedComponentIn Kᶜ y ⊆ Uᶜ := by
      intro z hzY hzU
      exact hne ((connectedComponentIn_eq hzY).trans (connectedComponentIn_eq hzU).symm)
    exact hfilled.of_isClosed_subset isClosed_closure
      (closure_minimal hsub hopen.isClosed_compl)

end PoincareMT.M76
