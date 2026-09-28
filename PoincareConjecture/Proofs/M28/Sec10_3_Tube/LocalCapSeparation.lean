import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalCapRegularCore
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.InnerAttachment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Separation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

omit [T2Space M] in
theorem boundary_subset_closure_end_m28 : C.boundary_sphere ⊆ closure C.end_neck.carrier := by
  rw [C.boundary_eq_end_frontier]
  exact inter_subset_right.trans frontier_subset_closure

omit [T2Space M] in
theorem boundary_neck_inter_core_nonempty_m28 :
    (C.boundary_neck.carrier ∩ C.core).Nonempty := by
  have hclosure : C.boundary_sphere ⊆ closure C.core := by
    rw [← C.closed_core_eq_closure_core]
    exact C.boundary_subset_closed_core_m28
  apply (mem_closure_iff.mp (hclosure
    (C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere)))
    _ C.boundary_neck.carrier_open
  exact C.boundary_neck.central_sphere_subset C.boundary_neck.center_on_central_sphere

omit [T2Space M] in
theorem boundary_neck_inter_end_nonempty_m28 :
    (C.boundary_neck.carrier ∩ C.end_neck.carrier).Nonempty := by
  apply (mem_closure_iff.mp (C.boundary_subset_closure_end_m28
    (C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere)))
    _ C.boundary_neck.carrier_open
  exact C.boundary_neck.central_sphere_subset C.boundary_neck.center_on_central_sphere



theorem boundary_neck_isSeparating_m28 : C.boundary_neck.IsSeparating := by
  refine ⟨C.boundary_neck.component_diff_central_sphere_nonempty, ?_⟩
  intro hc
  have hin : ((connectedComponent C.boundary_neck.center \
      C.boundary_neck.central_sphere) ∩ C.core).Nonempty := by
    obtain ⟨x, hx, hxin⟩ := C.boundary_neck_inter_core_nonempty_m28
    refine ⟨x, ⟨C.boundary_neck.carrier_subset_connectedComponent hx, ?_⟩, hxin⟩
    rw [← C.boundary_eq_neck_sphere]
    exact fun hb => Set.disjoint_left.mp C.disjoint_core_boundary_m28 hxin hb
  have hout : ((connectedComponent C.boundary_neck.center \
      C.boundary_neck.central_sphere) ∩ C.end_neck.carrier).Nonempty := by
    obtain ⟨x, hx, hxend⟩ := C.boundary_neck_inter_end_nonempty_m28
    refine ⟨x, ⟨C.boundary_neck.carrier_subset_connectedComponent hx, ?_⟩, hxend⟩
    rw [← C.boundary_eq_neck_sphere]
    exact fun hb => Set.disjoint_left.mp C.disjoint_closed_core_end_m28
      (C.boundary_subset_closed_core_m28 hb) hxend
  obtain ⟨x, hx, hb⟩ := C.boundary_inter_nonempty_of_core_end_m28 hc.2 hin hout
  exact hx.2 (C.boundary_eq_neck_sphere ▸ hb)

end PoincareConjecture.CapCertificate
