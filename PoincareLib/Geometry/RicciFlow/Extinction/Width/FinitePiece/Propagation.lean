import PoincareLib.Geometry.RicciFlow.Extinction.Width.FinitePiece.Statement

/-!
# M69 finite-piece width propagation proof entry

This checked application retains the exact M68 profile on the selected M67
path and applies the M61 based/free identity at the same start time.
Class coherence is an M67 output; this application owns no new admission.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Given one initial class and induced metric under a coherent M59 system,
and strict comparison bounds at all surgeries in [0,T], the actual scalar
lower bound and the indexed M58/M61/M65/M66 services, select the M67 width
preserving those objects and apply M68 on the supplied
finite interval. For a coherent class ledger, retain the exact selected
profile, identify based/free width at that interval's actual start, and
retain nonzero transported classes. Source: Morgan--Tian Proposition 18.18
and its application in Theorem 18.1, pp. 431--432. The initial-data anchor is
at zero; the profile's based/free identity is at its own start time. -/
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

end PoincareMT
