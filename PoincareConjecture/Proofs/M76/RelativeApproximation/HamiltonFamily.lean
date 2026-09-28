import PoincareConjecture.Proofs.M76.RelativeApproximation.BoundaryProperApproximation
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerCasesNamedInputs

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "V0" => (Fin 0 → ℝ)
local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "L2" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "X1" => LatticeHandleAmbient (Fin 1) (Fin 2) L1
local notation "X2" => LatticeHandleAmbient (Fin 2) (Fin 1) L2
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "R1" => latticeHandleDomain (Fin 1) (Fin 2) L1
local notation "R2" => latticeHandleDomain (Fin 2) (Fin 1) L2

theorem hasHamiltonRelativeApproximationFamily :
    (∀ (charts : Set (OpenPartialHomeomorph X0 V3))
      (d : (V0 × V3) → OpenPartialHomeomorph X0 V3),
      HasRelativeBoundaryProperPLApproximation
        (fun c : charts => (c : OpenPartialHomeomorph X0 V3)) d R0) ∧
    (∀ (charts : Set (OpenPartialHomeomorph X1 V3))
      (d : (V1 × V2) → OpenPartialHomeomorph X1 V3),
      HasRelativeBoundaryProperPLApproximation
        (fun c : charts => (c : OpenPartialHomeomorph X1 V3)) d R1) ∧
    (∀ (charts : Set (OpenPartialHomeomorph X2 V3))
      (d : (V2 × V1) → OpenPartialHomeomorph X2 V3),
      HasRelativeBoundaryProperPLApproximation
        (fun c : charts => (c : OpenPartialHomeomorph X2 V3)) d R2) := by
  exact ⟨fun charts d => hasRelativeBoundaryProperPLApproximation _ d R0,
    fun charts d => hasRelativeBoundaryProperPLApproximation _ d R1,
    fun charts d => hasRelativeBoundaryProperPLApproximation _ d R2⟩

end PoincareConjecture.M76
