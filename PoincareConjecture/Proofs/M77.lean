import PoincareConjecture.Statements.M77Transport
import PoincareConjecture.Proofs.M02

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

set_option linter.style.haveILetI false

theorem m77TransportTopologicalHypotheses : M77TransportStatement.{u} := by
  intro M _ _ _ _ _ _ P S
  letI : TopologicalSpace S.model := S.model_topology
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) S.model := S.model_charted
  letI : IsManifold (𝓡 3) ∞ S.model := S.model_manifold
  letI : T2Space S.model := S.model_t2
  letI : SecondCountableTopology S.model := S.model_second_countable
  letI : CompactSpace S.model := S.model_compact
  have model_simply_connected : SimplyConnectedSpace S.model :=
    S.model_homeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  letI : SimplyConnectedSpace S.model := model_simply_connected
  exact ⟨⟨model_simply_connected, closedSimplyConnectedThreeManifoldTopology⟩⟩

end PoincareConjecture
