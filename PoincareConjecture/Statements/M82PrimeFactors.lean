import PoincareConjecture.Definitions.M82PrimeFactors


















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

def M82PrimeFactorLedgerStatement : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N)
    (C : M72ReconstructionConclusion I),
    (F : M73SphereFactorConclusion I C) →
      Nonempty (M82PrimeFactorLedger I C F)

end PoincareConjecture
