import PoincareLib.Topology.Manifold.NeckCap.Cap.Core.EnclosingRegion

/-!
# Closing caps when one boundary sphere is contained in the other carrier

An enclosing region traps one closed side of the contained boundary sphere.
Contact of its closed core with the other carrier's frontier forces the
trapped side to be its exterior. The two original carriers therefore cover
a compact ambient component.

Reference: Morgan--Tian, Claim A.24, p. 512.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

/-- Boundary containment and closed-core frontier contact close a compact
component, without any additional smallness assumption. -/
theorem compact_component_of_boundary_subset (C D : CapCertificate g)
    (hboundary : D.boundary_sphere ⊆ C.carrier)
    (hcontact : (frontier C.carrier ∩ D.closed_core).Nonempty) :
    C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
      IsCompact (C.carrier ∪ D.carrier) := by
  rcases C.closed_side_subset_of_boundary_subset D hboundary with hinside | ⟨hc, houtside⟩
  · obtain ⟨x, hx, hxD⟩ := hcontact
    exact False.elim ((C.carrier_open.frontier_eq ▸ hx).2 (hinside hxD))
  · have hcenter : D.boundary_neck.center ∈ C.carrier := by
      apply hboundary
      rw [D.boundary_eq_neck_sphere]
      exact D.boundary_neck.center_on_central_sphere
    have hcomponent : connectedComponent D.boundary_neck.center =
        connectedComponent C.boundary_neck.center :=
      (connectedComponent_eq (C.carrier_subset_boundary_component hcenter)).symm
    have hunion : C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center := by
      apply Subset.antisymm
      · apply union_subset C.carrier_subset_boundary_component
        rw [← hcomponent]
        exact D.carrier_subset_boundary_component
      · rw [← hcomponent, ← D.closed_core_union_closure_exterior]
        exact union_subset (D.closed_core_subset_carrier.trans subset_union_right)
          (houtside.trans subset_union_left)
    refine ⟨hunion, ?_⟩
    rw [hunion, ← hcomponent, ← D.closed_core_union_closure_exterior]
    exact D.closed_core_compact.union hc

end PoincareMT.CapCertificate
