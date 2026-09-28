import PoincareConjecture.Definitions.M72FiniteReconstruction
































set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

def M72FiniteReconstructionStatement : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N),
    Nonempty (M72ReconstructionConclusion I)

end PoincareConjecture
