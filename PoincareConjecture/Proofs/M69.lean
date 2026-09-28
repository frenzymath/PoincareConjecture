import PoincareConjecture.Statements.M69

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem m69FinitePiecePropagation : M69FinitePieceStatement.{u} := by
  intro g₀ D W T P hcomparison hscalar K C H B A S initial hM61 hM64 hM65
    hM58 hM66 hM67 hM68
  dsimp
  let selected := m69M67Choice W P hcomparison hscalar K C H B A S initial
    hM61 hM65 hM58 hM66 hM67
  let X := selected.1
  let HX := selected.2.estimate
  intro L I
  let P := M69FinitePieceInput.profile L I HX
  let profile := Classical.choice (hM68 X HX P)
  refine ⟨⟨⟨profile, ?_, ?_⟩, rfl⟩⟩
  · rw [X.width_eq_based]
    exact (I.start_width_properties.eq_free
      (X.slice (M68ProfileInput.start P)).family
      (X.slice (M68ProfileInput.start P)).family_null
      (X.slice (M68ProfileInput.start P)).represents)
  · intro s
    rw [L.alpha_eq_slice]
    exact (X.slice s).class_nonzero

end PoincareConjecture
