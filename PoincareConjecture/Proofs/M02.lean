import PoincareConjecture.Statements.Ch01.Topology
import PoincareConjecture.Proofs.M02.Topology.IntegralThreeManifoldH2
import PoincareConjecture.Proofs.M02.Topology.ThreeManifoldTopologyAssembly

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem closedSimplyConnectedThreeManifoldTopology
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [SimplyConnectedSpace M] :
    Nonempty (ClosedSimplyConnectedThreeManifoldConclusion (M := M)) := by
  exact Proofs.M02.Topology.nonempty_threeManifoldTopologyConclusion_of_integralHomology_two_isZero
    (PoincareConjecture.Proofs.M02.Topology.integralThreeManifoldHomologyTwo_isZero (M := M))

end PoincareConjecture
