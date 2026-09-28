import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.FrontierContact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.CoreConnected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cover
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

namespace CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem frontier_core_contact_of_closed_core_contact (C D : CapCertificate g)
    {x : M} (hx : x ∈ D.core \ C.carrier)
    (hmeet : (D.closed_core ∩ C.carrier).Nonempty) :
    (frontier C.carrier ∩ D.core).Nonempty := by
  obtain ⟨p, hpD, hpC⟩ := hmeet
  obtain ⟨q, hqC, hqD⟩ := mem_closure_iff.mp
    (D.closure_core_eq_closed_core.symm ▸ hpD) C.carrier C.carrier_open hpC
  by_contra hnone
  have hdisj : Disjoint D.core (frontier C.carrier) := by
    apply Disjoint.symm
    exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnone)
  have hsub := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    D.isConnected_core.isPreconnected hdisj
    ⟨q, hqD, C.carrier_open.interior_eq.symm ▸ hqC⟩
  exact hx.2 (interior_subset (hsub hx.1))

end CapCertificate

namespace ConnectedNeckCapCover

theorem exists_closed_core_encounter_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (H : ConnectedNeckCapCover g) (C D : CapCertificate g),
          H.epsilon ≤ ε₀ → C ∈ H.caps → D ∈ H.caps →
          (∀ A ∈ H.caps, C.carrier ⊆ A.carrier →
            Disjoint (frontier C.carrier) A.closed_core) →
          ∀ x ∈ H.X, x ∈ D.core → x ∉ C.carrier →
            (D.closed_core ∩ C.carrier).Nonempty →
            H.X ⊆ C.carrier ∪ D.carrier ∧
              C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
                IsCompact (C.carrier ∪ D.carrier) := by
  obtain ⟨ε₁, hε₁, -, hclose⟩ := CapCertificate.exists_frontier_contact_closing_threshold.{u}
  refine ⟨min ε₁ (1 / 1000), lt_min hε₁ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g H C D hε hC hD hmax x hxX hxD hxout hmeet
  have hcontact := C.frontier_core_contact_of_closed_core_contact D ⟨hxD, hxout⟩ hmeet
  have hnoncontain : ¬ C.carrier ⊆ D.carrier := by
    intro hCD
    obtain ⟨p, hpfront, hpD⟩ := hcontact
    exact disjoint_left.mp (hmax D hD hCD) hpfront (D.core_subset_closed_core hpD)
  obtain ⟨heq, hcompact⟩ := hclose C D
    ((H.cap_epsilon C hC).trans_le (hε.trans (min_le_left _ _)))
    ((H.cap_epsilon D hD).trans (H.cap_epsilon C hC).symm) hcontact hnoncontain
  have hxcomponent : x ∈ connectedComponent C.boundary_neck.center :=
    heq ▸ Or.inr (D.core_subset_carrier hxD)
  refine ⟨?_, heq, hcompact⟩
  rw [heq, connectedComponent_eq hxcomponent]
  exact H.connected_X.isPreconnected.subset_connectedComponent hxX

end ConnectedNeckCapCover

end PoincareConjecture
