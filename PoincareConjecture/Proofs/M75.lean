import PoincareConjecture.Statements.M75SmoothPoincare
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

theorem m75SmoothPoincare : M75SmoothPoincareStatement.{u} := by
  intro hService M _ _ _ _ _ _ _
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  letI : T3Space M := inferInstance
  letI : SecondCountableTopology M := inferInstance
  obtain ⟨N, ⟨I⟩⟩ := hService M
  obtain ⟨R⟩ := I.reduction
  obtain ⟨d⟩ := R.reduction
  exact ⟨Diffeomorph.trans I.global.certificate.initial_identification d⟩

end PoincareConjecture
