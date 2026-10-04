import PoincareLib.Topology.Manifold.Poincare.Assembly.Conclusion

/-! Adapted from Mapher `PoincareMT/Statements/M80EndpointAssembly.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M80 endpoint assembly statement

Natural-language theorem statement: given the concrete M75 `SmoothPoincare`
service and the concrete M79 `TopologicalPoincare` service, return a record
containing exactly those two services.  This is a checked packaging adapter;
it does not prove either proposition, accept a prebuilt final theorem, or add
an endpoint-equivalent field.

Source: the primitive endpoint declarations in `PoincareMT.Statement` and
the reviewed M75/M79 service boundaries.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

def M80EndpointAssemblyStatement : Prop :=
  ∀ (_h75 : SmoothPoincare.{u}) (_h79 : TopologicalPoincare.{u}),
    Nonempty M80EndpointConclusion.{u}

end PoincareMT
