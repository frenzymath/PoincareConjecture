import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Protection.BoundaryDisks.JordanFillingCoverage

set_option autoImplicit false
open Set

namespace PoincareMT.M76

/-- A connected marked patch disjoint from a Jordan rim cannot meet the
closed bounded side when one of its points is outside that side. -/
theorem connected_mark_disjoint_closed_side
    {X : Type*} [TopologicalSpace X] {U T : Set X}
    (hU : IsOpen U) (hT : IsPreconnected T)
    (hdis : Disjoint T (frontier U))
    (hex : ∃ x ∈ T, x ∉ closure U) : Disjoint T (closure U) := by
  have hcover : T ⊆ U ∪ (closure U)ᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr (fun hcl => hdisjoint hx hcl hxU)
  have hdu : Disjoint U (closure U)ᶜ := disjoint_left.mpr (fun _ hx hn =>
    hn (subset_closure hx))
  rcases hT.subset_or_subset hU isClosed_closure.isOpen_compl hdu hcover with hs | hs
  · obtain ⟨x, hx, hnx⟩ := hex
    exact False.elim (hnx (subset_closure (hs hx)))
  · exact disjoint_left.mpr (fun x hx hc => hs hx hc)
where
  hdisjoint {x : X} (hx : x ∈ T) (hcl : x ∈ closure U) (hxU : x ∉ U) : False := by
    have : x ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hcl, hxU⟩
    exact disjoint_left.mp hdis hx this

end PoincareMT.M76
