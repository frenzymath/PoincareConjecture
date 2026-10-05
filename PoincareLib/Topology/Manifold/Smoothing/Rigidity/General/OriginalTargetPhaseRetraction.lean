import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.OriginalTargetTranslation

/-!
# The literal original target retraction onto one entire phase

The same three-circle coordinates preserve both tangent components and
replace only the last component by the specified phase. This constructs
an actual retraction, with its complete quotient-representative formula.
It is not an ambient homeomorphism. See Waldhausen1968, p.60, and
rigidity057, section2.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

/-- The actual global target retraction retains both tangent circles
and the literal selected normal phase. See rigidity057, section2. -/
noncomputable def hamiltonZeroTargetPhaseRetraction (theta : ℝ) : C(X0, X0) :=
  ⟨fun y => (Q0).symm ((Q0 y).1, (theta : C0)),
    (Q0).symm.continuous.comp
      ((continuous_fst.comp (Q0).continuous).prodMk continuous_const)⟩

/-- Both tangential coordinates and the selected normal coordinate
are literal on the whole original target. See rigidity057, section2. -/
theorem hamiltonZeroTargetPhaseRetraction_coordinates (theta : ℝ) (y : X0) :
    Q0 (hamiltonZeroTargetPhaseRetraction theta y) = ((Q0 y).1, (theta : C0)) :=
  (Q0).apply_symm_apply _

/-- Every point of the complete selected target phase is fixed by
the constructed retraction. See rigidity057, section2. -/
theorem hamiltonZeroTargetPhaseRetraction_fixed (theta : ℝ) (y : X0)
    (hy : (Q0 y).2 = (theta : C0)) :
    hamiltonZeroTargetPhaseRetraction theta y = y := by
  apply (Q0).injective
  rw [hamiltonZeroTargetPhaseRetraction_coordinates, ← hy]

/-- The image is the entire selected target torus, with every tangent
point retained. See rigidity057, section2. -/
theorem range_hamiltonZeroTargetPhaseRetraction (theta : ℝ) :
    range (hamiltonZeroTargetPhaseRetraction theta) =
      (fun y : X0 => (Q0 y).2) ⁻¹' {(theta : C0)} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change (Q0 (hamiltonZeroTargetPhaseRetraction theta x)).2 = (theta : C0)
    rw [hamiltonZeroTargetPhaseRetraction_coordinates]
  · intro hy
    exact ⟨y, hamiltonZeroTargetPhaseRetraction_fixed theta y hy⟩

/-- Every original quotient representative is mapped by the literal
affine coordinate replacement. This is the formula used for the
original-atlas PL proof. See rigidity057, section2. -/
theorem hamiltonZeroTargetPhaseRetraction_mk (theta : ℝ)
    (x : Fin 0 → ℝ) (v : Fin 3 → ℝ) :
    hamiltonZeroTargetPhaseRetraction theta (x, QuotientAddGroup.mk v) =
      (x, QuotientAddGroup.mk ![v 0, v 1, theta]) := by
  apply (Q0).injective
  rw [hamiltonZeroTargetPhaseRetraction_coordinates]
  rfl

end PoincareMT.M76
