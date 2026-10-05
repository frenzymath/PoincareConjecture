import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Homotopy
import PoincareLib.Topology.Manifold.ThreeDimensional.Conclusion
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Extension.Theory
/-!
# SurgeryComparison.Transport repaired comparison-map homotopy statement

The local comparison map transports homotopy and degree data under the audited
closed simply connected three-manifold topology interface.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

def RepairedClosedTopologyProvider : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [SimplyConnectedSpace M],
    Nonempty (ClosedSimplyConnectedThreeManifoldConclusion (M := M))

def RepairedComparisonMapProviderRealization
    (G39 : RepairedComparisonMapTheory.{u})
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (K : RepairedComparisonMapData D) : Prop :=
  let epsilon₀ := Classical.choose G39.comparison
  let hprovider := Classical.choose_spec G39.comparison
  ∃ hsmall : terminalAccuracyFactor * D.flow.parameters.epsilon ≤ epsilon₀,
    K = Classical.choice (hprovider.2 D hsmall)

structure RepairedComparisonHomotopyTheory : Prop where
  homotopy : (P : RepairedClosedTopologyProvider.{u}) →
    (G39 : RepairedComparisonMapTheory.{u}) →
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
      ∀ {g₀ : StandardInitialMetric},
        ∀ D : RepairedSurgeryFlowData.{u} g₀,
          terminalAccuracyFactor * D.flow.parameters.epsilon ≤ epsilon₀ →
          ∀ K : RepairedComparisonMapData D,
            RepairedComparisonMapProviderRealization G39 D K →
              Nonempty (RepairedComparisonHomotopyData D K)

end PoincareMT
