import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}



theorem subset_core_of_disjoint_boundary_of_frontier_core_contact
    (D : CapCertificate g) {S : Set M} (hS : IsPreconnected S)
    (hdis : Disjoint S D.boundary_sphere)
    (hcontact : (frontier S ∩ D.core).Nonempty) : S ⊆ D.core := by
  letI : T2Space M := @T25Space.t2Space M _ (T3Space.t25Space (X := M))
  obtain ⟨x, hx, hxD⟩ := hcontact
  obtain ⟨y, hyD, hy⟩ := mem_closure_iff.mp (frontier_subset_closure hx)
    D.core D.isOpen_core hxD
  rcases D.subset_core_or_compl_closed_core hS hdis with hcore | hext
  · exact hcore
  · exact False.elim (hext hy (D.core_subset_closed_core hyD))

end PoincareConjecture.CapCertificate
