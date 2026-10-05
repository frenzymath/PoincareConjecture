import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.StandardHierarchyCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonMarkedApproximation

/-!
# The literal ambient space of the closed original handle

The bounded Fin0 coordinate imposes no restriction. Its actual
domain therefore is the whole original ambient space, with the
canonical marked-handle comparison retained. See Hamilton1976
p.65 and rigidity052, sections4--5.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "V0" => (Fin 0 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0

/-- The original closed-handle domain is literally its entire
boundaryless ambient space. See rigidity052, section4. -/
theorem hamiltonZeroDomain_eq_univ : R0 = univ := by
  ext x
  change (dist x.1 0 ≤ 1 ∧ True) ↔ True
  rw [show x.1 = 0 from Subsingleton.elim _ _, dist_self]
  simp

/-- The original ambient-to-handle comparison inserts only the
unique bounded-coordinate proof. See rigidity052, section4. -/
def hamiltonZeroAmbientEquiv : X0 ≃ₜ H0 where
  toFun z := (⟨z.1, by
    rw [show z.1 = 0 from Subsingleton.elim _ _]
    exact mem_closedBall_self zero_le_one⟩, z.2)
  invFun z := ((z.1 : V0), z.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.subtype_mk (fun _ => _)).prodMk continuous_snd
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

/-- Restriction of the ambient comparison is the frozen canonical
domain comparison at every original point. See052, section4. -/
theorem hamiltonZeroAmbientEquiv_domain (x : R0) :
    hamiltonZeroAmbientEquiv (x : X0) =
      latticeHandleDomainEquiv (Fin 0) (Fin 3) L0 x := rfl

/-- The inverse ambient comparison is exactly the original domain
subtype value. See rigidity052, section4. -/
theorem hamiltonZeroAmbientEquiv_symm (z : H0) :
    hamiltonZeroAmbientEquiv.symm z =
      ((latticeHandleDomainEquiv (Fin 0) (Fin 3) L0).symm z : X0) := rfl

/-- Compactness holds on the whole original ambient space in the
closed case, using the same period lattice. See052, section4. -/
theorem isCompact_hamiltonZeroAmbient : IsCompact (univ : Set X0) := by
  simpa only [hamiltonZeroDomain_eq_univ] using
    isCompact_latticeHandleDomain (Fin 0) (Fin 3) L0

end PoincareMT.M76
