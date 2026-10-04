import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.ContainedSphere
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.CoreExpansion

/-!
# Closing caps along an outward boundary graph

A graph in the second cap's end retains its original closed core on the
enclosed side. If this graph lies in the first cap and the original closed
core meets its frontier, the two original carriers form a compact component.

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

/-- An outward graph of the second cap boundary contained in the first cap
closes the original carriers when its original closed core meets the frontier. -/
theorem compact_component_of_outward_boundary_graph (C D : CapCertificate g)
    (h : UnitTwoSphere → ℝ) (hh : Continuous h)
    (hdom : ∀ q, h q ∈ Ioo (-D.boundary_neck.epsilon⁻¹) D.boundary_neck.epsilon⁻¹)
    (hinside : ∀ q, D.boundary_neck.coordinate_map (q, h q) ∈ C.carrier)
    (hend : ∀ q, D.boundary_neck.coordinate_map (q, h q) ∈ D.end_neck.carrier)
    (hcontact : (frontier C.carrier ∩ D.closed_core).Nonempty) :
    C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
      IsCompact (C.carrier ∪ D.carrier) := by
  obtain ⟨r, hr, hrB, hbound⟩ := D.boundary_neck.exists_graph_collar h hh hdom
  let e := D.boundary_neck.graphTransport hr hrB h hh hbound
  have hboundary : e '' D.boundary_sphere ⊆ C.carrier := by
    rw [D.boundary_eq_neck_sphere,
      D.boundary_neck.graphTransport_image_central_sphere hr hrB h hh hbound]
    rintro _ ⟨q, rfl⟩
    exact hinside q
  have hfix : EqOn e id D.carrierᶜ := by
    intro x hx
    apply D.boundary_neck.graphTransport_fixed hr hrB h hh hbound
    intro hxK
    exact hx (D.boundary_neck_subset (D.boundary_neck.closedCollar_subset_carrier hrB hxK))
  have hcarrier : e '' D.carrier = D.carrier := by
    have hc := hfix.image_eq_self
    rw [e.image_compl] at hc
    exact compl_injective hc
  apply C.compact_component_of_transported_boundary_subset D e hboundary hcarrier
  obtain ⟨x, hx, hxD⟩ := hcontact
  exact ⟨x, hx, D.closed_core_subset_graphTransport_of_graph_in_end
    hr hrB h hh hbound hend hxD⟩

/-- The constant-height instance used for the shifted boundary sphere. -/
theorem compact_component_of_outward_boundary_slice (C D : CapCertificate g)
    {a : ℝ} (ha : a ∈ Ioo (-D.boundary_neck.epsilon⁻¹) D.boundary_neck.epsilon⁻¹)
    (hinside : ∀ q, D.boundary_neck.coordinate_map (q, a) ∈ C.carrier)
    (hend : ∀ q, D.boundary_neck.coordinate_map (q, a) ∈ D.end_neck.carrier)
    (hcontact : (frontier C.carrier ∩ D.closed_core).Nonempty) :
    C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
      IsCompact (C.carrier ∪ D.carrier) :=
  C.compact_component_of_outward_boundary_graph D (fun _ => a) continuous_const
    (fun _ => ha) hinside hend hcontact

end PoincareMT.CapCertificate
