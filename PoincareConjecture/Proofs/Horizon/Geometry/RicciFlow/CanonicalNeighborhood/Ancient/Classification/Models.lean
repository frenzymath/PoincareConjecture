import PoincareConjecture.Statements.M27Providers
import PoincareConjecture.Definitions.M27KappaAlternatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.WholeTube
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.StrongNeck











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


theorem m27SphereLineAlternatives (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ {M : Type u} [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
          [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
          (K : AncientKappaSolution 3 M) (_model : M27SphereLineFlowCertificate K)
          (C : ℝ), M27KappaNine93Conclusion K epsilon C := by
  obtain ⟨epsilon₀, hpos, hsmall, hglobal⟩ := P.global_neck_cap
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon hepsilon hle M _ _ _ _ _ _ _ _ _ K model C
  have hstrong : ∀ x : M, ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x :=
    fun x => model.exists_strongEvolvingNeck le_rfl hepsilon (by linarith) x
  let H := NoncompactKappa.wholeNeckCover K hepsilon hpos hsmall hle hstrong
  obtain ⟨conclusion⟩ := hglobal (K.flow.metric 0) H hle rfl
  let : NoncompactSpace M := model.identification.toHomeomorph.isClosedEmbedding.noncompactSpace
  rcases conclusion.tube_or_capped_of_noncompact (K.complete 0 le_rfl)
    (noncompact_univ M) with
    ⟨tube, he, hwhole⟩ | ⟨tube, _, _, _, hconstant⟩
  · apply M27KappaNine93Conclusion.sphereLine model
    exact
      { time_mem := le_rfl
        epsilon_pos := hepsilon
        tube := tube
        strong_at := fun x => by
          obtain ⟨N, hN⟩ := hstrong x
          exact ⟨N, hN, by simp only [hwhole, Set.mem_univ]⟩
        tube_epsilon := he
        carrier_eq_univ := hwhole }
  · exact (not_le_of_gt tube.cap.one_lt_cap_constant hconstant).elim

end PoincareConjecture
