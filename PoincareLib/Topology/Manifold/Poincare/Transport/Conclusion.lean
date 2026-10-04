import PoincareLib.Topology.Manifold.Poincare.Smoothing.TopologyData
import PoincareLib.Topology.Manifold.Poincare.Statement

/-! Adapted from Mapher `PoincareMT/Definitions/M78EndpointTransport.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M78 smooth-endpoint transport

This is the admission-free adapter that composes the M76 homeomorphism with
the M75 smooth endpoint diffeomorphism on the same transported model.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

structure M78EndpointConclusion {M : Type u} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : SmoothingBridgeInput (M := M))
    (S : SmoothingBridgeConclusion P)
    (T : M77TransportConclusion P S) where
  identification : M ≃ₜ ThreeSphere

end PoincareMT
