import PoincareLib.Geometry.RicciFlow.Extinction.Global.Definitions

/-!
# The fixed initial width in Theorem 18.1

The width is fixed before selecting a target time or component path. Its
nonnegativity is the M61 width property used in Morgan--Tian's proof of
Theorem 18.1, printed p. 432, with Definition 18.17 on p. 430.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow}
  {ancestry : RepairedFiniteAncestryData D.flow W}

/-- The single initial width used for every target in the zero-time branch
of Morgan--Tian Theorem 18.1, p. 432. -/
noncomputable def m71InitialWidth (Q : M71FiniteContinuationService D W ancestry) : ℝ :=
  m61BasedClassWidth Q.identification_system.quotient Q.initial.metric
    ancestry.initial_component.basepoint Q.initial.alpha

/-- M61 supplies nonnegativity of the fixed initial width, as used in
Morgan--Tian Theorem 18.1, p. 432. -/
theorem m71InitialWidth_nonneg (Q : M71FiniteContinuationService D W ancestry) :
    0 ≤ m71InitialWidth Q :=
  (Q.hM61.based_class Q.initial.metric ancestry.initial_component.compact
    ancestry.initial_component.connected ancestry.initial_component.basepoint
    Q.initial.pi_two_trivial Q.initial.alpha).nonnegative

end PoincareMT
