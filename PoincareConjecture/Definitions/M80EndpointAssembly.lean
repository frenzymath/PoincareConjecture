import PoincareConjecture.Statement








set_option autoImplicit false

universe u

namespace PoincareConjecture

structure M80EndpointConclusion where
  smooth : SmoothPoincare.{u}
  topological : TopologicalPoincare.{u}

end PoincareConjecture
