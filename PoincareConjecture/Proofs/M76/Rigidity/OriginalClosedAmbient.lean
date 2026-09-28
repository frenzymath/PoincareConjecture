import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchyCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedApproximation

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V0" => (Fin 0 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0

theorem hamiltonZeroDomain_eq_univ : R0 = univ := by
  ext x
  change (dist x.1 0 ≤ 1 ∧ True) ↔ True
  rw [show x.1 = 0 from Subsingleton.elim _ _, dist_self]
  simp

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

theorem hamiltonZeroAmbientEquiv_domain (x : R0) :
    hamiltonZeroAmbientEquiv (x : X0) =
      latticeHandleDomainEquiv (Fin 0) (Fin 3) L0 x := rfl

theorem hamiltonZeroAmbientEquiv_symm (z : H0) :
    hamiltonZeroAmbientEquiv.symm z =
      ((latticeHandleDomainEquiv (Fin 0) (Fin 3) L0).symm z : X0) := rfl

theorem isCompact_hamiltonZeroAmbient : IsCompact (univ : Set X0) := by
  simpa only [hamiltonZeroDomain_eq_univ] using
    isCompact_latticeHandleDomain (Fin 0) (Fin 3) L0

end PoincareConjecture.M76
