import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Twisted.Construction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CompactKappa

theorem uniform_twisted_caps_with_fine_strong_exterior_of_m27
    (P : M27KappaAlternativePredecessors.{u})
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) :
    ∃ delta C : ℝ, 0 < delta ∧ delta < epsilon ∧ 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (_model : M27TwistedSphereLineFlowCertificate K)
        (t : ℝ), t ≤ 0 →
          ∃ cap : CapCertificate (K.flow.metric t),
            cap.epsilon = epsilon ∧ cap.cap_constant = C ∧
            cap.connection = K.flow.connection t ∧ IsCompact (closure cap.carrier) ∧
            IsCompact (closure cap.carrier \ cap.core) ∧
            ∀ x : M, x ∉ cap.core →
              ∃ N : StrongEvolvingNeck K t delta, N.center = x := by
  refine ⟨epsilon / 2, P.capServices.twistedCapConstant (epsilon / 2), half_pos hepsilon,
    by linarith, P.capServices.twistedCapConstant_pos (half_pos hepsilon), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K model t ht
  exact P.capServices.exists_buffered_cap_core_or_strong_neck model ht hepsilon hsmall

end PoincareConjecture.CompactKappa
