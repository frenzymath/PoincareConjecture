import PoincareConjecture.Proofs.M76.Horizon.Rigidity.General.RelativePredicateClauses
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerCasesFourInputs







set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "L2" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "X1" => LatticeHandleAmbient (Fin 1) (Fin 2) L1
local notation "X2" => LatticeHandleAmbient (Fin 2) (Fin 1) L2
local notation "Y0" => ((Set.singleton hamiltonZeroHandlePuncture)ᶜ : Set X0)



theorem lowerCases_of_wall_dehn_prime
    (wall :
      (∀ e : Y0 → OpenPartialHomeomorph Y0 V3, HasWallCompactCore e) ∧
      (∀ (U : TopologicalSpace.Opens X1) (charts : Set (OpenPartialHomeomorph U V3)),
        HasWallCompactCore (fun c : charts => (c : OpenPartialHomeomorph U V3))) ∧
      (∀ (U : TopologicalSpace.Opens X2) (charts : Set (OpenPartialHomeomorph U V3)),
        HasWallCompactCore (fun c : charts => (c : OpenPartialHomeomorph U V3))))
    (dehn : HasHamiltonGeneralizedDehnInput)
    (prime :
      (∀ charts : Set (OpenPartialHomeomorph X0 V3),
        HasHamiltonProtectedIrreducibleReplacement (Fin 0) (Fin 3) L0
          (fun c : charts => (c : OpenPartialHomeomorph X0 V3))) ∧
      (∀ charts : Set (OpenPartialHomeomorph X1 V3),
        HasHamiltonProtectedIrreducibleReplacement (Fin 1) (Fin 2) L1
          (fun c : charts => (c : OpenPartialHomeomorph X1 V3))) ∧
      (∀ charts : Set (OpenPartialHomeomorph X2 V3),
        HasHamiltonProtectedIrreducibleReplacement (Fin 2) (Fin 1) L2
          (fun c : charts => (c : OpenPartialHomeomorph X2 V3)))) :
    HasHamiltonChartHandleStraightening V3 ∅ ∧
      (∀ J : Finset (Fin 3), J.card = 1 → HasHamiltonChartHandleStraightening V3 J) ∧
      (∀ J : Finset (Fin 3), J.card = 2 → HasHamiltonChartHandleStraightening V3 J) := by
  apply lowerCases_of_four_inputs wall dehn prime
  exact ⟨fun _ d => hasHamiltonRelativeTorusRigidity L0 _ d,
    fun _ d => hasHamiltonRelativeTorusRigidity L1 _ d,
    fun _ d => hasHamiltonRelativeTorusRigidity L2 _ d⟩

end PoincareConjecture.M76
