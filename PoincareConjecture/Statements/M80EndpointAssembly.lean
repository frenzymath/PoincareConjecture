import PoincareConjecture.Definitions.M80EndpointAssembly














set_option autoImplicit false

universe u

namespace PoincareConjecture

def M80EndpointAssemblyStatement : Prop :=
  ∀ (_h75 : SmoothPoincare.{u}) (_h79 : TopologicalPoincare.{u}),
    Nonempty M80EndpointConclusion.{u}

end PoincareConjecture
