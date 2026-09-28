import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Selection.Separation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryEndCut

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {N P : EpsilonNeck g}
  (C : SurgeryEndCut N) (D : SurgeryEndCut P)

theorem carrier_subset_tail_or_disjoint_closure
    (hneck : Disjoint N.carrier P.carrier) :
    N.carrier ⊆ D.tail ∨ Disjoint N.carrier (closure D.tail) := by
  have hfront : Disjoint N.carrier (frontier D.tail) := by
    rw [D.frontier_eq]
    exact hneck.mono_right P.central_sphere_subset
  have hcover : N.carrier ⊆ D.tail ∪ (closure D.tail)ᶜ := by
    intro x hx
    by_cases ht : x ∈ D.tail
    · exact Or.inl ht
    · exact Or.inr (fun hc => disjoint_left.mp hfront hx
        ⟨hc, fun hi => ht (interior_subset hi)⟩)
  rcases N.isConnected_carrier.isPreconnected.subset_or_subset
      D.tail_isOpen isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hcover with h | h
  · exact Or.inl h
  · exact Or.inr (disjoint_left.mpr fun _ hx => h hx)

private theorem tail_subset_of_carrier_subset_tail
    (hN : N.carrier ⊆ D.tail) (hP : Disjoint P.carrier (closure C.tail)) :
    C.tail ⊆ D.tail := by
  apply (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    C.tail_isConnected.isPreconnected ?_ ?_).trans interior_subset
  · rw [D.frontier_eq]
    exact (hP.mono P.central_sphere_subset subset_closure).symm
  · exact ⟨C.point, C.positive_subset C.point_positive,
      D.tail_isOpen.interior_eq.symm ▸ hN C.point_positive.1⟩

private theorem not_mutual_carrier_tail {p : M}
    (hpC : p ∈ connectedComponent N.center \ closure C.tail)
    (hpD : p ∈ connectedComponent P.center \ closure D.tail)
    (hN : N.carrier ⊆ D.tail) (hP : P.carrier ⊆ C.tail) : False := by
  have hret : connectedComponent N.center \ closure C.tail ⊆
      connectedComponent P.center \ closure D.tail := by
    rw [D.retained_eq_component hpD]
    apply C.retained_isConnected.isPreconnected.subset_connectedComponentIn hpC
    intro x hx hs
    exact hx.2 (subset_closure (hP (P.central_sphere_subset hs)))
  have hi := inv_pos.mpr N.epsilon_pos
  obtain ⟨q, hq⟩ := (N.isConnected_region le_rfl hi.le (neg_lt_zero.mpr hi)).nonempty
  have hqret : q ∈ connectedComponent N.center \ closure C.tail :=
    ⟨N.carrier_subset_connectedComponent hq.1,
      disjoint_left.mp C.negative_disjoint_closure hq⟩
  exact (hret hqret).2 (subset_closure (hN hq.1))

theorem tails_disjoint_or_subset_or_subset
    (hneck : Disjoint N.carrier P.carrier) {p : M}
    (hpC : p ∈ connectedComponent N.center \ closure C.tail)
    (hpD : p ∈ connectedComponent P.center \ closure D.tail) :
    Disjoint C.tail D.tail ∨ C.tail ⊆ D.tail ∨ D.tail ⊆ C.tail := by
  rcases D.carrier_subset_tail_or_disjoint_closure hneck with hN | hN
  · rcases C.carrier_subset_tail_or_disjoint_closure hneck.symm with hP | hP
    · exact False.elim (C.not_mutual_carrier_tail D hpC hpD hN hP)
    · exact Or.inr (Or.inl (C.tail_subset_of_carrier_subset_tail D hN hP))
  · rcases C.carrier_subset_tail_or_disjoint_closure hneck.symm with hP | hP
    · exact Or.inr (Or.inr (D.tail_subset_of_carrier_subset_tail C hP hN))
    · left
      apply disjoint_left.mpr
      intro x hxC hxD
      have hsub : C.tail ⊆ D.tail := by
        apply (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
          C.tail_isConnected.isPreconnected ?_
          ⟨x, hxC, D.tail_isOpen.interior_eq.symm ▸ hxD⟩).trans interior_subset
        rw [D.frontier_eq]
        exact (hP.mono P.central_sphere_subset subset_closure).symm
      exact disjoint_left.mp hN C.point_positive.1
        (subset_closure (hsub (C.positive_subset C.point_positive)))

end PoincareConjecture.SurgeryEndCut
