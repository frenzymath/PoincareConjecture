import PoincareLib.Topology.Manifold.Smoothing.Dehn.Generalized
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLowerCasesFourInputs

/-!
# The generalized Dehn theorem in Hamilton's lower-handle chain

Apply the constructed Dehn predicate to the original four-input theorem.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

open HamiltonIndexOne

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
local notation "Y0" => ((Set.singleton hamiltonZeroHandlePuncture)ᶜ : Set X0)

/-- The constructed generalized Dehn input discharges the Dehn premise of the
unchanged lower-handle consumer. The original wall, prime and rigidity families
remain as premises. See Hamilton 1976, pp. 64--68. -/
theorem lowerCases_of_wall_prime_rigidity
    (wall :
      (∀ e : Y0 → OpenPartialHomeomorph Y0 V3, HasWallCompactCore e) ∧
      (∀ (U : TopologicalSpace.Opens X1) (charts : Set (OpenPartialHomeomorph U V3)),
        HasWallCompactCore (fun c : charts => (c : OpenPartialHomeomorph U V3))) ∧
      (∀ (U : TopologicalSpace.Opens X2) (charts : Set (OpenPartialHomeomorph U V3)),
        HasWallCompactCore (fun c : charts => (c : OpenPartialHomeomorph U V3))))
    (prime :
      (∀ charts : Set (OpenPartialHomeomorph X0 V3),
        HasHamiltonProtectedIrreducibleReplacement (Fin 0) (Fin 3) L0
          (fun c : charts => (c : OpenPartialHomeomorph X0 V3))) ∧
      (∀ charts : Set (OpenPartialHomeomorph X1 V3),
        HasHamiltonProtectedIrreducibleReplacement (Fin 1) (Fin 2) L1
          (fun c : charts => (c : OpenPartialHomeomorph X1 V3))) ∧
      (∀ charts : Set (OpenPartialHomeomorph X2 V3),
        HasHamiltonProtectedIrreducibleReplacement (Fin 2) (Fin 1) L2
          (fun c : charts => (c : OpenPartialHomeomorph X2 V3))))
    (rigidity :
      (∀ (charts : Set (OpenPartialHomeomorph X0 V3))
        (d : (V0 × V3) → OpenPartialHomeomorph X0 V3),
        HasHamiltonRelativeTorusRigidity (Fin 0) (Fin 3) L0
          (fun c : charts => (c : OpenPartialHomeomorph X0 V3)) d) ∧
      (∀ (charts : Set (OpenPartialHomeomorph X1 V3))
        (d : (V1 × V2) → OpenPartialHomeomorph X1 V3),
        HasHamiltonRelativeTorusRigidity (Fin 1) (Fin 2) L1
          (fun c : charts => (c : OpenPartialHomeomorph X1 V3)) d) ∧
      (∀ (charts : Set (OpenPartialHomeomorph X2 V3))
        (d : (V2 × V1) → OpenPartialHomeomorph X2 V3),
        HasHamiltonRelativeTorusRigidity (Fin 2) (Fin 1) L2
          (fun c : charts => (c : OpenPartialHomeomorph X2 V3)) d)) :
    HasHamiltonChartHandleStraightening V3 ∅ ∧
      (∀ J : Finset (Fin 3), J.card = 1 → HasHamiltonChartHandleStraightening V3 J) ∧
      (∀ J : Finset (Fin 3), J.card = 2 → HasHamiltonChartHandleStraightening V3 J) := by
  exact lowerCases_of_four_inputs wall hasHamiltonGeneralizedDehnInput prime rigidity

end PoincareMT.M76
