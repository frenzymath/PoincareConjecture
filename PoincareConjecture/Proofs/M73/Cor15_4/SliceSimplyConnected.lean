import PoincareConjecture.Definitions.M72FiniteReconstruction
import PoincareConjecture.Proofs.M55.Mathlib.SimplyConnected













set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture




theorem m73_sliceZero_simplyConnected
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) :
    SimplyConnectedSpace (I.global.certificate.flow.slice 0).carrier := by
  let e := I.global.certificate.initial_identification.toHomeomorph.symm
  exact e.toHomotopyEquiv.simplyConnectedSpace

end PoincareConjecture
