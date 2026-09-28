import PoincareConjecture.Definitions.Ch09.AsymptoticSoliton

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

structure AncientBlowupSetup
    (K : AncientKappaSolution n M) (reference : M) (tau : ℕ → ℝ) where
  sequence : AncientRescalingSequence K
  reference_eq : sequence.reference = reference
  scale_eq : sequence.scale = tau

end PoincareConjecture
