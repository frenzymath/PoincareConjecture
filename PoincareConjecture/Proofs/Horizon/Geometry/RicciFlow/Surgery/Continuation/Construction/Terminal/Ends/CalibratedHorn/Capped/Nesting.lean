import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.CoreTube
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.ChainEncounter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Overlap

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem closed_core_meets_cap_of_cappedTube (D : CapCertificate g)
    (Y : CappedTubeCertificate g) (hD : D.closed_core ⊆ Y.carrier) :
    (D.closed_core ∩ Y.cap.carrier).Nonempty := by
  by_contra hnone
  apply D.closed_core_tube_noncontainment_of_epsilon_le Y.tube Y.tube.epsilon_le_threshold
  intro x hx
  exact (Y.carrier_eq_union ▸ hD hx).resolve_left
    (fun h => hnone ⟨x, hx, h⟩)

theorem frontier_core_contact_of_cappedTube (D : CapCertificate g)
    (Y : CappedTubeCertificate g) (hD : D.closed_core ⊆ Y.carrier)
    {x : M} (hx : x ∈ D.core \ Y.cap.carrier) :
    (frontier Y.cap.carrier ∩ D.core).Nonempty :=
  Y.cap.frontier_core_contact_of_closed_core_contact D hx
    (D.closed_core_meets_cap_of_cappedTube Y hD)

theorem mixed_boundary_of_frontier_core_contact_of_noncompact
    (C D : CapCertificate g)
    (hnoncompact : ¬ IsCompact (connectedComponent C.boundary_neck.center))
    (hcontact : (frontier C.carrier ∩ D.core).Nonempty)
    (hnot : ¬ C.carrier ⊆ D.carrier) :
    (D.boundary_sphere ∩ C.carrier).Nonempty ∧ ¬ D.boundary_sphere ⊆ C.carrier := by
  have hmeet : (D.boundary_sphere ∩ C.carrier).Nonempty := by
    by_contra hnone
    have hdis : Disjoint C.carrier D.boundary_sphere :=
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnone)).symm
    exact hnot ((D.subset_core_of_disjoint_boundary_of_frontier_core_contact
      C.isConnected_carrier.isPreconnected hdis hcontact).trans D.core_subset_carrier)
  refine ⟨hmeet, ?_⟩
  intro hsub
  have hcontact' : (frontier C.carrier ∩ D.closed_core).Nonempty := by
    obtain ⟨x, hx, hxD⟩ := hcontact
    exact ⟨x, hx, D.core_subset_closed_core hxD⟩
  obtain ⟨heq, hcompact⟩ := C.compact_component_of_boundary_subset D hsub hcontact'
  exact hnoncompact (heq ▸ hcompact)

end PoincareConjecture.CapCertificate
