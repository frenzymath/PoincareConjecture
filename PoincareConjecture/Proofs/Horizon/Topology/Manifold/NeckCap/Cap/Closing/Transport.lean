import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Union












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C D : CapCertificate g)

theorem image_carrier_subset_component_of_boundary_transport (e : M ≃ₜ M)
    (hboundary : e '' D.boundary_sphere = C.boundary_sphere) :
    e '' D.carrier ⊆ connectedComponent C.boundary_neck.center := by
  have hmem : e D.boundary_neck.center ∈ C.boundary_sphere := by
    rw [← hboundary]
    apply mem_image_of_mem
    rw [D.boundary_eq_neck_sphere]
    exact D.boundary_neck.center_on_central_sphere
  have hcomp := C.carrier_subset_boundary_component (C.boundary_subset hmem)
  rw [connectedComponent_eq hcomp]
  apply (D.isConnected_carrier.image e e.continuous.continuousOn).subset_connectedComponent
  apply mem_image_of_mem
  exact D.boundary_neck_subset
    (D.boundary_neck.central_sphere_subset D.boundary_neck.center_on_central_sphere)

theorem image_core_eq_or_eq_exterior_of_boundary_transport (e : M ≃ₜ M)
    (hboundary : e '' D.boundary_sphere = C.boundary_sphere) :
    e '' D.core = C.core ∨
      e '' D.core = connectedComponent C.boundary_neck.center \ C.closed_core := by
  obtain ⟨x, hx⟩ := D.core_nonempty
  have hxavoid : x ∈ D.boundary_sphereᶜ := Set.disjoint_left.mp D.disjoint_core_boundary hx
  have hexavoid : e x ∉ C.boundary_sphere := by
    rw [← hboundary, e.injective.mem_set_image]
    exact hxavoid
  have hcomponent := C.image_carrier_subset_component_of_boundary_transport D e hboundary
    (mem_image_of_mem e (D.core_subset_carrier hx))
  have hxside : e x ∈ C.core ∪
      (connectedComponent C.boundary_neck.center \ C.closed_core) := by
    rw [C.core_union_exterior]
    exact ⟨hcomponent, hexavoid⟩
  have himage : e '' D.core = connectedComponentIn C.boundary_sphereᶜ (e x) := by
    rw [D.core_eq_connectedComponentIn hx, e.image_connectedComponentIn hxavoid,
      e.image_compl, hboundary]
  rcases hxside with hcore | hext
  · exact Or.inl (himage.trans (C.core_eq_connectedComponentIn hcore).symm)
  · exact Or.inr (himage.trans (C.exterior_eq_connectedComponentIn hext).symm)



theorem union_eq_component_of_boundary_transport (e : M ≃ₜ M)
    (hboundary : e '' D.boundary_sphere = C.boundary_sphere)
    (hcarrier : e '' D.carrier = D.carrier) (hcore : e '' D.core ≠ C.core) :
    C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center := by
  have hext := (C.image_core_eq_or_eq_exterior_of_boundary_transport D e hboundary).resolve_left
    hcore
  have hclosed : C.closed_core ∪ e '' D.closed_core =
      connectedComponent C.boundary_neck.center := by
    rw [← D.closure_core_eq_closed_core, e.image_closure, hext]
    exact C.closed_core_union_closure_exterior
  apply Subset.antisymm
  · apply union_subset C.carrier_subset_boundary_component
    rw [← hcarrier]
    exact C.image_carrier_subset_component_of_boundary_transport D e hboundary
  · rw [← hclosed]
    apply union_subset_union C.closed_core_subset_carrier
    rw [← hcarrier]
    exact image_mono D.closed_core_subset_carrier

theorem isCompact_union_of_boundary_transport (e : M ≃ₜ M)
    (hboundary : e '' D.boundary_sphere = C.boundary_sphere)
    (hcarrier : e '' D.carrier = D.carrier) (hcore : e '' D.core ≠ C.core) :
    IsCompact (C.carrier ∪ D.carrier) := by
  have hext := (C.image_core_eq_or_eq_exterior_of_boundary_transport D e hboundary).resolve_left
    hcore
  have hclosed : C.closed_core ∪ e '' D.closed_core =
      connectedComponent C.boundary_neck.center := by
    rw [← D.closure_core_eq_closed_core, e.image_closure, hext]
    exact C.closed_core_union_closure_exterior
  rw [C.union_eq_component_of_boundary_transport D e hboundary hcarrier hcore, ← hclosed]
  exact C.closed_core_compact.union (D.closed_core_compact.image e.continuous)



theorem image_core_ne_of_fixed_frontier_point (e : M ≃ₜ M) {x : M}
    (hx : x ∈ frontier C.carrier) (hxD : x ∈ D.closed_core) (hfix : e x = x) :
    e '' D.core ≠ C.core := by
  intro hsame
  have hclosed : e '' D.closed_core = C.closed_core := by
    rw [← D.closure_core_eq_closed_core, e.image_closure, hsame,
      C.closure_core_eq_closed_core]
  have hxC : x ∈ C.closed_core := by
    rw [← hclosed]
    exact ⟨x, hxD, hfix⟩
  exact hx.2 (C.carrier_open.interior_eq.symm ▸ C.closed_core_subset_carrier hxC)

theorem compact_component_of_fixed_frontier_point (e : M ≃ₜ M)
    (hboundary : e '' D.boundary_sphere = C.boundary_sphere)
    (hcarrier : e '' D.carrier = D.carrier) {x : M}
    (hx : x ∈ frontier C.carrier) (hxD : x ∈ D.closed_core) (hfix : e x = x) :
    C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
      IsCompact (C.carrier ∪ D.carrier) := by
  have hcore := C.image_core_ne_of_fixed_frontier_point D e hx hxD hfix
  exact ⟨C.union_eq_component_of_boundary_transport D e hboundary hcarrier hcore,
    C.isCompact_union_of_boundary_transport D e hboundary hcarrier hcore⟩



theorem compact_component_of_boundary_transport_fixed_outside (e : M ≃ₜ M)
    (hboundary : e '' C.boundary_sphere = D.boundary_sphere)
    (hfix : EqOn e id C.carrierᶜ)
    (hcontact : (frontier C.carrier ∩ D.closed_core).Nonempty) :
    C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
      IsCompact (C.carrier ∪ D.carrier) := by
  obtain ⟨x, hx, hxD⟩ := hcontact
  have hcarrier : e '' C.carrier = C.carrier := by
    have h := hfix.image_eq_self
    rw [e.image_compl] at h
    exact compl_injective h
  have hfixInv : e.symm x = x := by
    apply e.injective
    rw [e.apply_symm_apply, hfix ((C.carrier_open.frontier_eq ▸ hx).2)]
    rfl
  have hcore : e '' C.core ≠ D.core := by
    intro heq
    apply C.image_core_ne_of_fixed_frontier_point D e.symm hx hxD hfixInv
    rw [← heq]
    exact e.toEquiv.symm_image_image C.core
  have hD : D.boundary_sphere ⊆ C.carrier := by
    rw [← hboundary, ← hcarrier]
    exact image_mono C.boundary_subset
  have hcomp : connectedComponent D.boundary_neck.center =
      connectedComponent C.boundary_neck.center := by
    apply (connectedComponent_eq _).symm
    apply C.carrier_subset_boundary_component (hD _)
    rw [D.boundary_eq_neck_sphere]
    exact D.boundary_neck.center_on_central_sphere
  constructor
  · simpa only [union_comm, hcomp] using
      D.union_eq_component_of_boundary_transport C e hboundary hcarrier hcore
  · simpa only [union_comm] using
      D.isCompact_union_of_boundary_transport C e hboundary hcarrier hcore

end PoincareConjecture.CapCertificate
