import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.ChainTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.ChainContainedSphere











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate



theorem exists_finite_chain_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T → ∀ b : ℤ, T.shape = .finite 0 b →
          Disjoint D.closed_core C.carrier →
          (frontier (C.carrier ∪ (T.unionOpen : Set M)) ∩ D.core).Nonempty →
          C.carrier ∪ (T.unionOpen : Set M) ∪ D.carrier =
              connectedComponent C.boundary_neck.center ∧
            IsCompact (C.carrier ∪ (T.unionOpen : Set M) ∪ D.carrier) := by
  obtain ⟨ε₁, hε₁, hsmall, htransport⟩ := exists_outgoing_chain_boundary_transport_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hclose⟩ := exists_finite_chain_transported_boundary_closing_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε hDC H T hT b hshape hdis hcontact
  obtain ⟨e, hboundary, hcarrier, hcontact'⟩ :=
    htransport C D (hε.trans (min_le_left _ _)) hDC H T hT b hshape hdis hcontact
  exact hclose C (hε.trans (min_le_right _ _)) H T hT b hshape D e
    hboundary hcarrier hcontact'

end PoincareConjecture.CapCertificate
