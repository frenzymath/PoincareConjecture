import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.Elimination

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem HamiltonZeroSecondPhaseGeometry.of_secondCircleMap_eq
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {R : Set X0} {phi psi : C(H0, H0)} {a b : ℝ}
    (geometry : HamiltonZeroSecondPhaseGeometry e R phi a b)
    (hsecond : hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi)
    (F : (ContinuousMap.id H0).HomotopyRel psi B0)
    {cut alpha beta : ℝ} (halpha : cut < alpha) (hab : alpha ≤ beta)
    (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) :
    HamiltonZeroSecondPhaseGeometry e R psi a b := by
  refine ⟨?_, ?_⟩
  · intro side
    rw [hsecond]
    exact geometry.slabs side
  · intro theta htheta x
    have hinj : ∀ y : ↥(R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}),
        Function.Injective (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}), X0)) y) := by
      rw [hsecond]
      exact fun y => (geometry.groups theta htheta y).1
    exact ⟨hinj x, hamiltonZeroSecondPhaseCircleMap_pi1_injective psi F
      halpha hab hbeta hR theta x (hinj x)⟩

end PoincareConjecture.M76
