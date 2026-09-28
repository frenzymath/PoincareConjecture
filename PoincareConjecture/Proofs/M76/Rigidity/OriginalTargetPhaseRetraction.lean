import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetTranslation











set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates



noncomputable def hamiltonZeroTargetPhaseRetraction (theta : ℝ) : C(X0, X0) :=
  ⟨fun y => (Q0).symm ((Q0 y).1, (theta : C0)),
    (Q0).symm.continuous.comp
      ((continuous_fst.comp (Q0).continuous).prodMk continuous_const)⟩



theorem hamiltonZeroTargetPhaseRetraction_coordinates (theta : ℝ) (y : X0) :
    Q0 (hamiltonZeroTargetPhaseRetraction theta y) = ((Q0 y).1, (theta : C0)) :=
  (Q0).apply_symm_apply _



theorem hamiltonZeroTargetPhaseRetraction_fixed (theta : ℝ) (y : X0)
    (hy : (Q0 y).2 = (theta : C0)) :
    hamiltonZeroTargetPhaseRetraction theta y = y := by
  apply (Q0).injective
  rw [hamiltonZeroTargetPhaseRetraction_coordinates, ← hy]



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




theorem hamiltonZeroTargetPhaseRetraction_mk (theta : ℝ)
    (x : Fin 0 → ℝ) (v : Fin 3 → ℝ) :
    hamiltonZeroTargetPhaseRetraction theta (x, QuotientAddGroup.mk v) =
      (x, QuotientAddGroup.mk ![v 0, v 1, theta]) := by
  apply (Q0).injective
  rw [hamiltonZeroTargetPhaseRetraction_coordinates]
  rfl

end PoincareConjecture.M76
