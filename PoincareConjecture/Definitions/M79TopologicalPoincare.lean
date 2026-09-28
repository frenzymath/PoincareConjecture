import PoincareConjecture.Statements.M76SmoothingBridge
import PoincareConjecture.Statements.M77Transport
import PoincareConjecture.Statements.M78EndpointTransport
import PoincareConjecture.Statement

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

def M79TopologicalPoincareStatement : Prop :=
  ∀ (_h76 : M76SmoothingStatement.{u})
    (_h77 : M77TransportStatement.{u})
    (_h75 : SmoothPoincare.{u})
    (_h78 : M78EndpointTransportStatement.{u}),
    TopologicalPoincare.{u}

end PoincareConjecture
