import PoincareLib.Topology.Manifold.Poincare.Smoothing.TopologyData

/-! Adapted from Mapher `PoincareMT/Statements/M77Transport.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M77 topological-hypothesis transport

Natural-language theorem statement: let `M` be a compact, Hausdorff,
second-countable, charted topological three-manifold with simple connectedness.
For an M76 smoothing bridge `S` from `M` to its explicit smooth model, the
model is simply connected and carries the concrete M02 topology package.
The homeomorphism is the one already stored by `S`; no sphere endpoint is
assumed or concluded here.

Source and dependency: simple connectedness is invariant under the
homeomorphism via Mathlib's `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`.
The second output is exactly M02's `ClosedSimplyConnectedThreeManifoldConclusion`,
whose source review is `reviews/contracts/M02-round1.md` (with actual type
review in `reviews/declarations/M02-round2.md`).  M76 supplies the model and
homeomorphism.  This is an adapter milestone, not a Poincare theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

def M77TransportStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M]
    (P : SmoothingBridgeInput (M := M))
    (S : SmoothingBridgeConclusion P),
    Nonempty (M77TransportConclusion P S)

end PoincareMT
