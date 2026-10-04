import PoincareLib.Topology.Manifold.Poincare.Smoothing.Service
import PoincareLib.Topology.Manifold.Smoothing.Assembly
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Handles.HamiltonLowerHandleBridge
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.WallCompactCore
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Applications.HamiltonLowerHandles
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Handles.ProtectedIrreducibleReplacement
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Applications.HamiltonLowerHandles

/-!
# M76 proof entry

The checked Hamilton--Cairns chain constructs the actual finite relative
handle assembly, finite triangulation and compatible smooth model.
Alexander supplies index three. The constructed Wall, Dehn, protected prime
replacement and relative rigidity inputs supply all lower indices;
see Hamilton 1976, pp. 64--69 and
M76 derivations 319--320 and 330.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

open Set Metric Geometry M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "L2" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "X1" => LatticeHandleAmbient (Fin 1) (Fin 2) L1
local notation "X2" => LatticeHandleAmbient (Fin 2) (Fin 1) L2
local notation "Y0" => ((Set.singleton hamiltonZeroHandlePuncture)ᶜ : Set X0)

/-- M76: Hamilton--Cairns compatible smoothing bridge. -/
theorem m76CompatibleSmoothing : M76SmoothingStatement.{u} := by
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

end PoincareMT
