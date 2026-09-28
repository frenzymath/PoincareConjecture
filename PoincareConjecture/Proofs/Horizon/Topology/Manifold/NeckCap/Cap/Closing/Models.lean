import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Certificate
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Euclidean
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Mixed.TwoCaps
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Mixed.Exterior
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Projective.TwoCaps
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Tube.Models
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.CollarFilling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.ProjectiveModel
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.CollarFilling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts















set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate



theorem exists_two_cap_closed_model_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
        (C D : CapCertificate g),
        C.epsilon = D.epsilon → C.epsilon ≤ ε₀ →
        IsCompact (C.carrier ∪ D.carrier) →
        (∃ x : M, C.carrier ∪ D.carrier = connectedComponent x) →
        ∃ kind : ClosedComponentKind,
          Nonempty (ClosedComponentCertificate kind (C.carrier ∪ D.carrier)) := by
  refine ⟨1 / 200, by norm_num, le_rfl, ?_⟩
  intro M _ _ _ _ _ _ _ g C D _ _ hcompact hcomponent
  cases hC : C.model_kind with
  | euclidean =>
    cases hD : D.model_kind with
    | euclidean =>
      exact ⟨.threeSphere,
        C.nonempty_two_euclidean_cap_closedComponentCertificate D hC hD hcompact hcomponent⟩
    | puncturedProjective =>
      refine ⟨.realProjectiveThree, ?_⟩
      simpa only [union_comm] using
        D.nonempty_mixed_cap_closedComponentCertificate C hD hC
          (union_comm C.carrier D.carrier ▸ hcompact)
          (union_comm C.carrier D.carrier ▸ hcomponent)
  | puncturedProjective =>
    cases hD : D.model_kind with
    | euclidean =>
      exact ⟨.realProjectiveThree,
        C.nonempty_mixed_cap_closedComponentCertificate D hC hD hcompact hcomponent⟩
    | puncturedProjective =>
      exact C.nonempty_two_projective_cap_closedComponentCertificate D hC hD hcompact hcomponent



theorem exists_double_capped_tube_closed_model_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
        (T : DoubleCappedTubeCertificate g),
        T.cap₁.epsilon = T.cap₂.epsilon →
        T.cap₁.epsilon = T.tube.epsilon → T.cap₁.epsilon ≤ ε₀ →
        (∃ x : M, T.carrier = connectedComponent x) →
        ∃ kind : ClosedComponentKind,
          Nonempty (ClosedComponentCertificate kind T.carrier) := by
  exact DoubleCappedTubeCertificate.exists_closed_model_threshold

end PoincareConjecture.CapCertificate
