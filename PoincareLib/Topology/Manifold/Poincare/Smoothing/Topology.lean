import PoincareLib.Topology.Manifold.Poincare.Smoothing.TopologyStatement
import PoincareLib.Topology.Manifold.ThreeDimensional.ClosedSimplyConnected

/-! Adapted from Mapher `PoincareMT/Proofs/M77.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M77 proof entry

The proof transports simple connectedness along the M76 homeomorphism and
applies the closed M02 theorem to the smooth model.  M76 and M02 are read-only
predecessors; this file contains no admission.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

set_option linter.style.haveILetI false

/-- M77: transport simple connectedness and apply M02 on the M76 model. -/
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

end PoincareMT
