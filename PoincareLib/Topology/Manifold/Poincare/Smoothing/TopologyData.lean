import PoincareLib.Topology.Manifold.Poincare.Smoothing.Basic
import PoincareLib.Topology.Manifold.ThreeDimensional.Conclusion

/-! Adapted from Mapher `PoincareMT/Definitions/M77Transport.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M77 transport to the compatible smooth model

M76 supplies explicit model instances and a homeomorphism.  M77 transports
simple connectedness along that homeomorphism and applies the already reviewed
M02 topology service to the model.  The endpoint propositions are not part of
this interface.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

structure M77TransportConclusion {M : Type u} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : SmoothingBridgeInput (M := M))
    (S : SmoothingBridgeConclusion P) where
  /-- Simple connectedness transported to the M76 smooth model. -/
  model_simply_connected : @SimplyConnectedSpace S.model S.model_topology
  /-- The M02 homotopy/topology package on the transported smooth model. -/
  model_topology :
    Nonempty (@ClosedSimplyConnectedThreeManifoldConclusion S.model
      S.model_topology S.model_charted S.model_manifold)

end PoincareMT
