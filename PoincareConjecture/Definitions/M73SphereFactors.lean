import PoincareConjecture.Definitions.M72FiniteReconstruction
import PoincareConjecture.Statement

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

structure M73SphereFactorConclusion
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) (C : M72ReconstructionConclusion I) where
  factor_kind : ∀ j : Fin C.summand_count,
    (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.kind
      (C.summand_index j).2.1 = .spaceform
  factor_sphere : ∀ j : Fin C.summand_count,
    Diffeomorph (𝓡 3) (𝓡 3) (C.pieces j).carrier ThreeSphere ∞

end PoincareConjecture
