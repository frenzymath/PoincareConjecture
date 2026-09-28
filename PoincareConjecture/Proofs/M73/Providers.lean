import PoincareConjecture.Proofs.M72
import PoincareConjecture.Proofs.M73

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

theorem m73SphereFactors_from_M72
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)} (I : M72ReconstructionInput N) :
    ∃ C : M72ReconstructionConclusion I, Nonempty (M73SphereFactorConclusion I C) := by
  obtain ⟨C⟩ := m72FiniteReconstruction I
  exact ⟨C, m73SphereFactors I C⟩

end PoincareConjecture
