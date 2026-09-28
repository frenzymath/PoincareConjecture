import PoincareConjecture.Definitions.M39ComparisonMap
import PoincareConjecture.Statements.M38LocalTopology











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




















structure RepairedComparisonMapTheory : Prop where
  comparison : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
    ∀ {g₀ : StandardInitialMetric},
      ∀ D : RepairedSurgeryFlowData.{u} g₀,
        2 * D.flow.parameters.epsilon ≤ epsilon₀ →
        Nonempty (RepairedComparisonMapData D)

end PoincareConjecture
