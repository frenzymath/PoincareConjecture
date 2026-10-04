import PoincareLib.Topology.Manifold.Poincare.Transport.Conclusion

/-! Adapted from Mapher `PoincareMT/Statements/M78EndpointTransport.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M78 smooth-endpoint transport statement

Natural-language theorem statement: for a compact simply connected topological
three-manifold `M`, an M76 bridge `S`, an M77 transport conclusion `T`, and the
concrete M75 `SmoothPoincare` service, apply that service to `S.model`.  The
resulting diffeomorphism `d : S.model ≃ₘ ThreeSphere` is converted to a
homeomorphism and composed with `S.model_homeomorph : M ≃ₜ S.model`.

The output is only `Nonempty (M ≃ₜ ThreeSphere)`.  This adapter does not state
the universal `TopologicalPoincare` proposition and does not accept a
prebuilt endpoint.  Source: Morgan--Tian Corollary 0.2(a) as exposed by M75,
the M76/M77 interfaces, and Mathlib `Diffeomorph.toHomeomorph` plus
`Homeomorph.trans`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

def M78EndpointTransportStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M]
    (P : SmoothingBridgeInput (M := M))
    (S : SmoothingBridgeConclusion P)
    (T : M77TransportConclusion P S)
    (_hSmooth : SmoothPoincare.{u}),
    Nonempty (M78EndpointConclusion P S T)

end PoincareMT
