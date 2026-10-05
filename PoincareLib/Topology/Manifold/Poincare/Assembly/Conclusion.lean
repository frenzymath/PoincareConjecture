import PoincareLib.Topology.Manifold.Poincare.Statement

/-! Adapted from Mapher `PoincareMT/Definitions/M80EndpointAssembly.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M80 endpoint assembly adapter

M80 packages the two independently produced primitive endpoint propositions.
It performs no mathematical proof and introduces no new endpoint premise.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

structure M80EndpointConclusion where
  smooth : SmoothPoincare.{u}
  topological : TopologicalPoincare.{u}

end PoincareMT
