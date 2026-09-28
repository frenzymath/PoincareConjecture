import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Noncompact

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem image_closed_core_subset_of_boundary_image_subset_core
    (C : CapCertificate g) (e : M ≃ₜ M) {L : Set M}
    (hL : IsCompact L) (hLC : L ⊆ C.carrier)
    (hfix : ∀ x, x ∉ L → e x = x)
    (hboundary : e '' C.boundary_sphere ⊆ C.core) :
    e '' C.closed_core ⊆ C.closed_core := by
  have hnot : ¬ C.carrier ⊆ C.closed_core ∪ L := by
    intro h
    have heq := Subset.antisymm h (union_subset C.closed_core_subset_carrier hLC)
    exact C.not_isCompact_carrier (heq ▸ C.closed_core_compact.union hL)
  obtain ⟨p, hpC, hpout⟩ := not_subset.mp hnot
  have hp : p ∈ connectedComponent C.boundary_neck.center \ C.closed_core :=
    ⟨C.carrier_subset_boundary_component hpC, fun h => hpout (Or.inl h)⟩
  have hfp := hfix p (fun h => hpout (Or.inr h))
  have havoid : connectedComponent C.boundary_neck.center \ C.closed_core ⊆
      (e '' C.boundary_sphere)ᶜ :=
    fun _ hx hb => hx.2 (C.core_subset_closed_core (hboundary hb))
  have hcomp : e '' connectedComponent C.boundary_neck.center =
      connectedComponent C.boundary_neck.center := by
    rw [connectedComponent_eq hp.1]
    have h := e.image_connectedComponentIn (s := univ) (x := p) (mem_univ _)
    simpa only [image_univ, e.surjective.range_eq, connectedComponentIn_univ, hfp] using h
  have hext : connectedComponent C.boundary_neck.center \ C.closed_core ⊆
      e '' (connectedComponent C.boundary_neck.center \ C.closed_core) := by
    have hpavoid : p ∈ C.boundary_sphereᶜ :=
      fun hb => hp.2 (C.boundary_subset_closed_core hb)
    rw [C.exterior_eq_connectedComponentIn hp,
      e.image_connectedComponentIn hpavoid,
      e.image_compl, hfp]
    rw [← C.exterior_eq_connectedComponentIn hp]
    exact C.isConnected_component_diff_closed_core.isPreconnected.subset_connectedComponentIn
      hp havoid
  intro x hx
  by_contra hxc
  have hxcomponent : x ∈ connectedComponent C.boundary_neck.center := by
    rw [← hcomp]
    exact image_mono (C.closed_core_subset_carrier.trans C.carrier_subset_boundary_component) hx
  obtain ⟨y, hy, hyx⟩ := hext ⟨hxcomponent, hxc⟩
  obtain ⟨z, hz, hzx⟩ := hx
  exact hy.2 (e.injective (hyx.trans hzx.symm) ▸ hz)

end PoincareConjecture.CapCertificate
