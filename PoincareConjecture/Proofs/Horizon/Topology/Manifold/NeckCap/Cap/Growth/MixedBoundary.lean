import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.EndFrontier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}


theorem frontier_inter_boundary_nonempty_of_mixed (C D : CapCertificate g)
    (hmeet : (D.boundary_sphere ∩ C.carrier).Nonempty)
    (hmiss : ¬ D.boundary_sphere ⊆ C.carrier) :
    (frontier C.carrier ∩ D.boundary_sphere).Nonempty := by
  by_contra h
  have hconn : IsConnected D.boundary_sphere :=
    D.boundary_eq_neck_sphere.symm ▸ D.boundary_neck.isConnected_central_sphere
  let : ConnectedSpace D.boundary_sphere := isConnected_iff_connectedSpace.mp hconn
  have hdis : Disjoint (frontier C.carrier) D.boundary_sphere :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
  have hclopen := isClopen_preimage_val C.carrier_open hdis
  obtain ⟨x, hxD, hxC⟩ := hmeet
  have hfull := hclopen.eq_univ ⟨⟨x, hxD⟩, hxC⟩
  apply hmiss
  intro y hy
  have hmem : (⟨y, hy⟩ : D.boundary_sphere) ∈ Subtype.val ⁻¹' C.carrier := by
    rw [hfull]
    exact mem_univ _
  exact hmem



theorem exists_mixed_boundary_positive_end_contact :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ →
          (D.boundary_sphere ∩ C.carrier).Nonempty →
          (¬ D.boundary_sphere ⊆ C.carrier) →
          ∃ x : M, x ∈ frontier C.carrier ∧
            x ∈ frontier C.end_neck.carrier ∧
            x ∈ closure (C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ∧
            x ∈ D.boundary_neck.central_sphere := by
  obtain ⟨ε₀, hε₀, hsmall, hfrontier⟩ :=
    exists_frontier_carrier_subset_closure_positive_end.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε hmeet hmiss
  obtain ⟨x, hx, hxD⟩ := C.frontier_inter_boundary_nonempty_of_mixed D hmeet hmiss
  exact ⟨x, hx, C.frontier_carrier_subset_frontier_end hx, hfrontier C hε hx,
    D.boundary_eq_neck_sphere ▸ hxD⟩

end PoincareConjecture.CapCertificate
