import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.Local
import PoincareLib.Topology.Manifold.NeckCap.Theory

/-!
# M38 raw local surgery topology and repaired-flow specialization

The topology threshold is chosen uniformly before the actual raw flow. Each
nonempty terminal event returns one selected finite connected-sum conclusion
with cap correspondence, while each vanishing event returns one selected
conclusion containing no survivor pieces. These are the two local branches of
Proposition 15.3; no global endpoint reconstruction is assumed.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/- Morgan--Tian Proposition 15.3 (printed pp. 357--358) says that, at a
   singular time satisfying Assumptions (1)--(7), the pre-surgery slice is
   obtained from the post-surgery slice together with finitely many
   two-sphere bundles and positive-curvature spaceforms by connected-sum
   operations. The source uses the local surgery operation of Definition 15.8
   (pp. 361--362); the empty-terminal branch is the corresponding extinction
   specialization. -/
structure RawLocalSurgeryTopologyTheory : Prop where
  topology : ∀ N : RepairedNeckCapTopologyTheory.{u},
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ N.epsilon₀ ∧
      ∀ F : SurgeryFlowData.{u},
        SurgeryFlowAdmissible F →
        terminalAccuracyFactor * F.parameters.epsilon ≤ epsilon₀ →
          Nonempty (RawLocalSurgeryTopologyData F)

/-- The existing repaired-flow callers use the same local theorem at `D.flow`. -/
structure RepairedLocalSurgeryTopologyTheory : Prop where
  topology : ∀ N : RepairedNeckCapTopologyTheory.{u},
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ N.epsilon₀ ∧
      ∀ {g₀ : StandardInitialMetric},
        ∀ D : RepairedSurgeryFlowData.{u} g₀,
          SurgeryFlowAdmissible D.flow →
          terminalAccuracyFactor * D.flow.parameters.epsilon ≤ epsilon₀ →
            Nonempty (RepairedLocalSurgeryTopologyData D)

end PoincareMT
