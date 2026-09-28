import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.CompactPrefix
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Growth.MixedBoundary

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem frontier_carrier_subset_closure_positive_region (C : CapCertificate g)
    {b : ℝ} (hb : b < C.epsilon⁻¹) :
    frontier C.carrier ⊆ closure (C.end_neck.region b C.epsilon⁻¹) := by
  obtain ⟨a, ha, hab⟩ := exists_between (max_lt hb
    (neg_lt_self (inv_pos.mpr C.epsilon_pos)))
  have hprefix := (C.isCompact_truncated_core hab).2
  intro x hx
  have hends := C.end_neck.frontier_subset_closure_ends
    (a := a) (b := a)
    (by rw [C.end_neck_epsilon]; exact (le_max_right _ _).trans_lt ha)
    (by rw [C.end_neck_epsilon]; exact hab)
    (C.frontier_carrier_subset_frontier_end hx)
  rw [C.end_neck_epsilon] at hends
  have hpositive := hends.resolve_left fun hn =>
    (C.carrier_open.frontier_eq ▸ hx).2 (hprefix (Or.inr hn))
  apply closure_mono _ hpositive
  intro y hy
  exact ⟨hy.1, (lt_of_le_of_lt (le_max_left _ _) ha).trans hy.2.1, hy.2.2⟩

theorem mixed_boundary_positive_end_contact (C D : CapCertificate g)
    (hmeet : (D.boundary_sphere ∩ C.carrier).Nonempty)
    (hmiss : ¬ D.boundary_sphere ⊆ C.carrier) :
    ∃ x : M, x ∈ frontier C.carrier ∧
      x ∈ frontier C.end_neck.carrier ∧
      x ∈ closure (C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ∧
      x ∈ D.boundary_neck.central_sphere := by
  obtain ⟨x, hx, hxD⟩ := C.frontier_inter_boundary_nonempty_of_mixed D hmeet hmiss
  exact ⟨x, hx, C.frontier_carrier_subset_frontier_end hx,
    C.frontier_carrier_subset_closure_positive_region
      (by have h := inv_pos.mpr C.epsilon_pos; linarith) hx,
    D.boundary_eq_neck_sphere ▸ hxD⟩

end PoincareConjecture.CapCertificate
