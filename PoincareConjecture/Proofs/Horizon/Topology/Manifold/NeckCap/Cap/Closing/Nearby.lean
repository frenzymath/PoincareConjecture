import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Transport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Nearby













set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate



theorem exists_nearby_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (C D : CapCertificate g),
        C.epsilon = ε → D.epsilon = ε →
        D.boundary_neck.center ∈ C.boundary_neck.region (-ε⁻¹ / 2) (ε⁻¹ / 2) →
        (frontier C.carrier ∩ D.closed_core).Nonempty →
        C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
          IsCompact (C.carrier ∪ D.carrier) := by
  obtain ⟨ε₀, hε₀, hsmall, htransport⟩ := EpsilonNeck.exists_nearby_compact_transport.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε hεpos hε C D hC hD hnear hcontact
  obtain ⟨e, K, _, hK, hfix, _, hsphere⟩ :=
    htransport hεpos hε C.boundary_neck D.boundary_neck
      (C.boundary_neck_epsilon.trans hC) (D.boundary_neck_epsilon.trans hD) hnear
  have hfixC : EqOn e id C.carrierᶜ := by
    intro y hy
    exact hfix y (fun hyK => hy (C.boundary_neck_subset (hK hyK)))
  have hboundary : e '' C.boundary_sphere = D.boundary_sphere := by
    simpa only [C.boundary_eq_neck_sphere, D.boundary_eq_neck_sphere] using hsphere
  exact C.compact_component_of_boundary_transport_fixed_outside D e hboundary hfixC hcontact

end PoincareConjecture.CapCertificate
