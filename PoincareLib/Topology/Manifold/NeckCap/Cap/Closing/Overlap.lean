import PoincareLib.Topology.Manifold.NeckCap.Cap.Boundary

/-!
# Core contact across a region's frontier

A connected region avoiding a cap boundary lies on one side of that
boundary. Contact of its frontier with the open core forces the core side.
This excludes the disjoint-boundary case for a maximal cap.

Reference: Morgan--Tian, Claim A.23, pp. 512--513.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

/-- An open-core contact fixes the side of a connected region avoiding
the cap boundary. The region can itself be a cap or a capped tube. -/
theorem subset_core_of_disjoint_boundary_of_frontier_core_contact
    (D : CapCertificate g) {S : Set M} (hS : IsPreconnected S)
    (hdis : Disjoint S D.boundary_sphere)
    (hcontact : (frontier S ∩ D.core).Nonempty) : S ⊆ D.core := by
  obtain ⟨x, hx, hxD⟩ := hcontact
  obtain ⟨y, hyD, hy⟩ := mem_closure_iff.mp (frontier_subset_closure hx)
    D.core D.isOpen_core hxD
  rcases D.subset_core_or_compl_closed_core hS hdis with hcore | hext
  · exact hcore
  · exact False.elim (hext hy (D.core_subset_closed_core hyD))

end PoincareMT.CapCertificate
