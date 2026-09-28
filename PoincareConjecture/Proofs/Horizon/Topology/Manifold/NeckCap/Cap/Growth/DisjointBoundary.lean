import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.NeckContainment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate



theorem exists_disjoint_boundary_core_containment_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (C D : CapCertificate g),
        C.epsilon = ε → D.epsilon = ε → C.carrier ⊆ D.carrier →
        Disjoint C.carrier D.boundary_sphere → C.carrier ⊆ D.core := by
  obtain ⟨ε₀, hε₀, hsmall, hnoncontain⟩ := exists_neck_noncontainment_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε hεpos hε C D hC hD hCD hdis
  rcases D.subset_core_or_compl_closed_core C.isConnected_carrier.isPreconnected hdis with h | h
  · exact h
  · exfalso
    apply hnoncontain hεpos hε C D.end_neck hC (D.end_neck_epsilon.trans hD)
    intro x hx
    by_contra hn
    apply h hx
    rw [D.closed_core_eq_complement_end]
    exact ⟨hCD hx, hn⟩

end PoincareConjecture.CapCertificate
