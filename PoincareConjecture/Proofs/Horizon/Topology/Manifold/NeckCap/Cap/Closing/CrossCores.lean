import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.FrontierContact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.CoreConnected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.NeckContainment
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_mutual_core_avoidance_or_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
          Disjoint D.closed_core C.carrier →
          Disjoint C.closed_core D.carrier ∨
            (C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
              IsCompact (C.carrier ∪ D.carrier)) := by
  obtain ⟨ε₁, hε₁, hsmall, hnotneck⟩ := exists_closed_core_neck_noncontainment_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hmixed⟩ := exists_mixed_overlap_containment_or_closing_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε hDC hdis
  by_cases havoid : Disjoint C.closed_core D.carrier
  · exact Or.inl havoid
  right
  have hnotCD : ¬ C.closed_core ⊆ D.carrier := by
    intro hCD
    apply hnotneck C.epsilon_pos (hε.trans (min_le_left _ _)) C D.end_neck rfl
      (D.end_neck_epsilon.trans hDC)
    intro x hx
    rcases D.carrier_eq_closed_core_union_end ▸ hCD hx with hxD | hxD
    · exact (disjoint_left.mp hdis hxD (C.closed_core_subset_carrier hx)).elim
    · exact hxD
  have hmeet : (C.closed_core ∩ D.carrier).Nonempty :=
    not_disjoint_iff.mp havoid
  obtain ⟨p, hpC, hpD⟩ := hmeet
  obtain ⟨q, hqD, hqC⟩ := mem_closure_iff.mp
    (C.closure_core_eq_closed_core.symm ▸ hpC) D.carrier D.carrier_open hpD
  obtain ⟨d, hd⟩ := D.core_nonempty
  have hdout : d ∉ C.carrier := fun h =>
    disjoint_left.mp hdis (D.core_subset_closed_core hd) h
  have hnoncontain : ¬ D.carrier ⊆ C.carrier := fun h =>
    hdout (h (D.core_subset_carrier hd))
  have hboundary : (C.boundary_sphere ∩ D.carrier).Nonempty := by
    rw [inter_comm]
    exact C.boundary_inter_nonempty_of_crossing D.isConnected_carrier.isPreconnected
      ⟨q, hqD, hqC⟩ ⟨d, D.core_subset_carrier hd,
        fun h => hdout (C.closed_core_subset_carrier h)⟩
  have hcontact : (frontier D.carrier ∩ C.closed_core).Nonempty := by
    by_contra hnone
    have hdisfront : Disjoint C.closed_core (frontier D.carrier) :=
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnone)).symm
    exact hnotCD ((Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      C.isConnected_closed_core.isPreconnected hdisfront
      ⟨p, hpC, D.carrier_open.interior_eq.symm ▸ hpD⟩).trans interior_subset)
  have hclose : D.carrier ∪ C.carrier = connectedComponent D.boundary_neck.center ∧
      IsCompact (D.carrier ∪ C.carrier) := by
    by_cases hcontained : C.boundary_sphere ⊆ D.carrier
    · exact D.compact_component_of_boundary_subset C hcontained hcontact
    · exact (hmixed D C (hDC.trans_le (hε.trans (min_le_right _ _))) hDC.symm
        hboundary hcontained).resolve_left hnoncontain
  have hcenter : C.boundary_neck.center ∈ connectedComponent D.boundary_neck.center := by
    rw [← hclose.1]
    exact Or.inr (C.boundary_neck_subset
      (C.boundary_neck.central_sphere_subset C.boundary_neck.center_on_central_sphere))
  rw [union_comm] at hclose
  exact ⟨hclose.1.trans (connectedComponent_eq hcenter), hclose.2⟩

end PoincareConjecture.CapCertificate
