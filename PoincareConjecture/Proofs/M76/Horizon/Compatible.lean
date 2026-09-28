import PoincareConjecture.Statements.M76SmoothingBridge
import PoincareConjecture.Proofs.M76.Assembly
import PoincareConjecture.Proofs.M76.Smoothing.HamiltonLowerHandleBridge
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.WallCompactCore
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Generalized
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerCasesFourInputs
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.ProtectedIrreducibleReplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Applications.HamiltonLowerHandles

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

open Set Metric Geometry M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "L2" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "X1" => LatticeHandleAmbient (Fin 1) (Fin 2) L1
local notation "X2" => LatticeHandleAmbient (Fin 2) (Fin 1) L2
local notation "Y0" => ((Set.singleton hamiltonZeroHandlePuncture)ᶜ : Set X0)

theorem horizon_m76CompatibleSmoothing : M76SmoothingStatement.{u} := by
  intro M _ _ _ _ _ P
  have lowerCases :
      M76.HasHamiltonChartHandleStraightening (Fin 3 → ℝ) ∅ ∧
      (∀ J : Finset (Fin 3), J.card = 1 →
        M76.HasHamiltonChartHandleStraightening (Fin 3 → ℝ) J) ∧
      (∀ J : Finset (Fin 3), J.card = 2 →
        M76.HasHamiltonChartHandleStraightening (Fin 3 → ℝ) J) := by
    have wall :
        (∀ e : Y0 → OpenPartialHomeomorph Y0 V3, HasWallCompactCore e) ∧
        (∀ (U : TopologicalSpace.Opens X1)
          (charts : Set (OpenPartialHomeomorph U V3)),
          HasWallCompactCore (fun c : charts =>
            (c : OpenPartialHomeomorph U V3))) ∧
        (∀ (U : TopologicalSpace.Opens X2)
          (charts : Set (OpenPartialHomeomorph U V3)),
          HasWallCompactCore (fun c : charts =>
            (c : OpenPartialHomeomorph U V3))) := by
      refine ⟨?_, ?_, ?_⟩
      · intro e
        exact hasWallCompactCore e
      · intro U charts
        exact hasWallCompactCore (fun c : charts =>
          (c : OpenPartialHomeomorph U V3))
      · intro U charts
        exact hasWallCompactCore (fun c : charts =>
          (c : OpenPartialHomeomorph U V3))
    have primeZero :
        ∀ charts : Set (OpenPartialHomeomorph X0 V3),
          HasHamiltonProtectedIrreducibleReplacement (Fin 0) (Fin 3) L0
            (fun c : charts => (c : OpenPartialHomeomorph X0 V3)) := by
      intro charts
      exact hasHamiltonProtectedIrreducibleReplacement_of_card_eq_zero L0
        (fun c : charts => (c : OpenPartialHomeomorph X0 V3)) (Fintype.card_fin 0)
    have primeTwo :
        ∀ charts : Set (OpenPartialHomeomorph X2 V3),
          HasHamiltonProtectedIrreducibleReplacement (Fin 2) (Fin 1) L2
            (fun c : charts => (c : OpenPartialHomeomorph X2 V3)) := by
      intro charts
      exact hasHamiltonProtectedIrreducibleReplacement_of_card_eq_two L2
        (fun c : charts => (c : OpenPartialHomeomorph X2 V3)) (Fintype.card_fin 2)
    have primeOne :
        ∀ charts : Set (OpenPartialHomeomorph X1 V3),
          HasHamiltonProtectedIrreducibleReplacement (Fin 1) (Fin 2) L1
            (fun c : charts => (c : OpenPartialHomeomorph X1 V3)) := by
      intro charts
      exact hasHamiltonProtectedIrreducibleReplacement L1
        (fun c : charts => (c : OpenPartialHomeomorph X1 V3))
    exact lowerCases_of_wall_dehn_prime wall hasHamiltonGeneralizedDehnInput
      ⟨primeZero, primeOne, primeTwo⟩
  exact M76.smoothingConclusion_of_lower_handle_cases P
    lowerCases.1 lowerCases.2.1 lowerCases.2.2

end PoincareConjecture
