import PoincareConjecture.Definitions.M38LocalTopology
import PoincareConjecture.Statements.M25NeckCapTopology











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture








structure RawLocalSurgeryTopologyTheory : Prop where
  topology : ∀ N : RepairedNeckCapTopologyTheory.{u},
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ N.epsilon₀ ∧
      ∀ F : SurgeryFlowData.{u},
        SurgeryFlowAdmissible F →
        2 * F.parameters.epsilon ≤ epsilon₀ →
          Nonempty (RawLocalSurgeryTopologyData F)


structure RepairedLocalSurgeryTopologyTheory : Prop where
  topology : ∀ N : RepairedNeckCapTopologyTheory.{u},
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ N.epsilon₀ ∧
      ∀ {g₀ : StandardInitialMetric},
        ∀ D : RepairedSurgeryFlowData.{u} g₀,
          SurgeryFlowAdmissible D.flow →
          2 * D.flow.parameters.epsilon ≤ epsilon₀ →
            Nonempty (RepairedLocalSurgeryTopologyData D)

end PoincareConjecture
