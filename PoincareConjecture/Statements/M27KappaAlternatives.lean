import PoincareConjecture.Definitions.M27KappaAlternatives

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedKappaAlternativeTheory : Prop where
  theorem_9_93 : ∃ epsilonBar : ℝ, 0 < epsilonBar ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonBar →
      ∃ C : ℝ, 0 < C ∧
        ∀ {M : Type u} [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
          [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
          ∀ K : AncientKappaSolution 3 M, RepairedKappaAlternativeCertificate K epsilon C
  corollary_9_94 : ∃ epsilonPrime : ℝ, 0 < epsilonPrime ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonPrime →
      ∃ C : ℝ, 0 < C ∧
        ∀ {M : Type u} [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
          [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
          ∀ K : AncientKappaSolution 3 M,
            ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K) →
              ∀ t, t ≤ 0 → ∀ x : M, M27StrongCanonicalNeighborhood K t x epsilon C

end PoincareConjecture
