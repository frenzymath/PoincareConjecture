import PoincareConjecture.Statements.M78EndpointTransport
import Mathlib.Geometry.Manifold.Diffeomorph









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

set_option linter.style.haveILetI false







theorem m78EndpointTransport : M78EndpointTransportStatement.{u} := by
  intro M _ _ _ _ _ _ P S T hSmooth
  letI : TopologicalSpace S.model := S.model_topology
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) S.model := S.model_charted
  letI : IsManifold (𝓡 3) ∞ S.model := S.model_manifold
  letI : T2Space S.model := S.model_t2
  letI : SecondCountableTopology S.model := S.model_second_countable
  letI : CompactSpace S.model := S.model_compact
  letI : SimplyConnectedSpace S.model := T.model_simply_connected
  rcases hSmooth S.model with ⟨d⟩
  exact ⟨{ identification := S.model_homeomorph.trans d.toHomeomorph }⟩

end PoincareConjecture
