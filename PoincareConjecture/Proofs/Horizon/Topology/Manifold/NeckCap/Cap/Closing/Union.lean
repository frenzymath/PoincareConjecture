import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement












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

theorem boundary_component_eq_of_boundary_eq (hboundary : D.boundary_sphere = C.boundary_sphere) :
    connectedComponent D.boundary_neck.center = connectedComponent C.boundary_neck.center := by
  apply (connectedComponent_eq ?_).symm
  apply C.carrier_subset_boundary_component
  apply C.boundary_subset
  rw [← hboundary, D.boundary_eq_neck_sphere]
  exact D.boundary_neck.center_on_central_sphere

theorem core_eq_or_eq_exterior_of_boundary_eq
    (hboundary : D.boundary_sphere = C.boundary_sphere) :
    D.core = C.core ∨
      D.core = connectedComponent C.boundary_neck.center \ C.closed_core := by
  obtain ⟨x, hx⟩ := D.core_nonempty
  have hcomponent : x ∈ connectedComponent C.boundary_neck.center := by
    rw [← C.boundary_component_eq_of_boundary_eq D hboundary]
    exact D.carrier_subset_boundary_component (D.core_subset_carrier hx)
  have havoid : x ∉ C.boundary_sphere := by
    rw [← hboundary]
    exact Set.disjoint_left.mp D.disjoint_core_boundary hx
  have hxside : x ∈ C.core ∪
      (connectedComponent C.boundary_neck.center \ C.closed_core) := by
    rw [C.core_union_exterior]
    exact ⟨hcomponent, havoid⟩
  rcases hxside with hcore | hext
  · left
    rw [D.core_eq_connectedComponentIn hx, C.core_eq_connectedComponentIn hcore, hboundary]
  · right
    rw [D.core_eq_connectedComponentIn hx, C.exterior_eq_connectedComponentIn hext, hboundary]

theorem union_eq_component_of_boundary_eq_of_core_ne
    (hboundary : D.boundary_sphere = C.boundary_sphere) (hcore : D.core ≠ C.core) :
    C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center := by
  have hext := (C.core_eq_or_eq_exterior_of_boundary_eq D hboundary).resolve_left hcore
  have hclosed : C.closed_core ∪ D.closed_core = connectedComponent C.boundary_neck.center := by
    rw [← D.closure_core_eq_closed_core, hext]
    exact C.closed_core_union_closure_exterior
  apply Subset.antisymm
  · apply union_subset C.carrier_subset_boundary_component
    rw [← C.boundary_component_eq_of_boundary_eq D hboundary]
    exact D.carrier_subset_boundary_component
  · rw [← hclosed]
    exact union_subset_union C.closed_core_subset_carrier D.closed_core_subset_carrier

theorem isCompact_union_of_boundary_eq_of_core_ne
    (hboundary : D.boundary_sphere = C.boundary_sphere) (hcore : D.core ≠ C.core) :
    IsCompact (C.carrier ∪ D.carrier) := by
  have hext := (C.core_eq_or_eq_exterior_of_boundary_eq D hboundary).resolve_left hcore
  have hclosed : C.closed_core ∪ D.closed_core = connectedComponent C.boundary_neck.center := by
    rw [← D.closure_core_eq_closed_core, hext]
    exact C.closed_core_union_closure_exterior
  rw [C.union_eq_component_of_boundary_eq_of_core_ne D hboundary hcore, ← hclosed]
  exact C.closed_core_compact.union D.closed_core_compact

end PoincareConjecture.CapCertificate
