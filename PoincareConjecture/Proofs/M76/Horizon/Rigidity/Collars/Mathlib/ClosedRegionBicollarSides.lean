import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FiniteComponentExcision

set_option autoImplicit false

open Set

namespace Poincare.Topology

theorem opposite_sides_of_frontier_neighborhood {X : Type*} [TopologicalSpace X]
    {D P N U : Set X} (hD : IsClosed D) (hregular : closure (interior D) = D)
    (hne : (frontier D).Nonempty) (hU : IsOpen U) (hFU : frontier D ⊆ U)
    (hcover : U ⊆ frontier D ∪ P ∪ N)
    (hP : IsPreconnected P) (hN : IsPreconnected N)
    (hPF : Disjoint P (frontier D)) (hNF : Disjoint N (frontier D)) :
    (P ⊆ interior D ∧ Disjoint N D) ∨ (N ⊆ interior D ∧ Disjoint P D) := by
  obtain ⟨x, hx⟩ := hne
  have hxD : x ∈ D := hD.frontier_subset hx
  have hxcl : x ∈ closure (interior D) := hregular.symm ▸ hxD
  obtain ⟨y, hyU, hyint⟩ := mem_closure_iff.mp hxcl U hU (hFU hx)
  have hxcompl : x ∈ closure Dᶜ := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  obtain ⟨z, hzU, hzout⟩ := mem_closure_iff.mp hxcompl U hU (hFU hx)
  have hy : y ∈ P ∪ N := by
    rcases hcover hyU with (hf | hp) | hn
    · exact (hf.2 hyint).elim
    · exact Or.inl hp
    · exact Or.inr hn
  have hz : z ∈ P ∪ N := by
    rcases hcover hzU with (hf | hp) | hn
    · exact (hzout (hD.frontier_subset hf)).elim
    · exact Or.inl hp
    · exact Or.inr hn
  rcases subset_interior_or_disjoint_of_disjoint_frontier hP hD hPF with hPi | hPo
  · rcases subset_interior_or_disjoint_of_disjoint_frontier hN hD hNF with hNi | hNo
    · exact (hzout (interior_subset (hz.elim (fun h => hPi h) (fun h => hNi h)))).elim
    · exact Or.inl ⟨hPi, hNo⟩
  · rcases subset_interior_or_disjoint_of_disjoint_frontier hN hD hNF with hNi | hNo
    · exact Or.inr ⟨hNi, hPo⟩
    · exact (hy.elim (fun h => disjoint_left.mp hPo h (interior_subset hyint))
        (fun h => disjoint_left.mp hNo h (interior_subset hyint))).elim

end Poincare.Topology
