import PoincareConjecture.Statements.M80EndpointAssembly

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem m80EndpointAssembly : M80EndpointAssemblyStatement.{u} := by
  intro h75 h79
  exact ⟨{ smooth := h75, topological := h79 }⟩

end PoincareConjecture
