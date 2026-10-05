import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Assembly

/-!
# Differential Harnack estimates and ancient consequences

The original M06 theorem, relative to the supplied M04 curvature theory.
The per-slice curvature continuation, bounded-flow Hamilton block argument,
ancient differential limit, and path comparison construct all frozen fields.

References: Morgan--Tian, Theorem 4.37 and Corollary 4.39, p. 81;
Theorem 4.40, p. 82; Definition 9.2, p. 180.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Complete nonnegatively curved flows with per-slice curvature bounds satisfy
the differential and zero-safe integrated Harnack estimates, including the
ancient terminal time. -/
theorem differentialHarnackAncientTheory
    (hM04 : RicciFlowCurvatureTheory.{u}) : HarnackAncientTheory.{u} := by
  exact differentialHarnackAncientTheory_of_bounded_ancient_zero_volume hM04

end PoincareMT
