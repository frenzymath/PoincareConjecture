import PoincareLib.Topology.Manifold.Poincare.Transport.Statement
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Adapted from Mapher `PoincareMT/Proofs/M78.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M78 proof entry

This is a checked logical adapter.  It consumes the concrete M75 service and
the M76/M77 model data, then performs only the explicit homeomorphism
composition.  There is no theorem-owned admission in this wrapper.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

set_option linter.style.haveILetI false

/-- M78: given a compact simply connected topological three-manifold, its
M76 compatible smooth model, the M77 transported hypotheses and smooth
Poincare, obtain a diffeomorphism on that same model and compose its underlying
homeomorphism with the M76 map. The result is a homeomorphism from the original
manifold to the standard sphere. Source: the M76 compatible-smoothing bridge
and Morgan--Tian Corollary 0.2(a); this composition has no admission. -/
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

end PoincareMT
