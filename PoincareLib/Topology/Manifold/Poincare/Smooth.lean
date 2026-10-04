import PoincareLib.Topology.Manifold.Poincare.Smooth.Statement
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Adapted from Mapher `PoincareMT/Proofs/M75.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M75 proof entry

This entry performs the checked endpoint composition.  The substantial
construction of its input service remains owned by M52 and M71--M74.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

/-- M75: if the earlier milestones supply a normalized metric, an actual
global flow and an M74 reduction of its initial slice for every compact
simply connected smooth three-manifold, compose the two diffeomorphisms to
prove exactly `SmoothPoincare`. The M90 producer supplies this service.
Source: Morgan--Tian Corollary 0.2(a), Corollary 15.4(2), pp. 358-359,
and the initial identification in Theorem 15.9/Corollary 15.10, pp. 363-364.
This is a checked logical adapter with no theorem admission. -/
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

end PoincareMT
