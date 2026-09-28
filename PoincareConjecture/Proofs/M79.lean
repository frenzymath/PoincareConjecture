import PoincareConjecture.Statements.M79TopologicalPoincare

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

theorem m79TopologicalPoincare : M79TopologicalPoincareStatement.{u} := by
  intro h76 h77 h75 h78 M _ _ _ _ _ _
  let P : SmoothingBridgeInput (M := M) :=
    { connected := isConnected_univ
      nonempty := Set.univ_nonempty }
  rcases h76 M P with ⟨S⟩
  rcases h77 M P S with ⟨T⟩
  rcases h78 M P S T h75 with ⟨C⟩
  exact ⟨C.identification⟩

end PoincareConjecture
