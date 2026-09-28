import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedAmbient
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleHomotopySurjective

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩

noncomputable def hamiltonZeroCircleMap (phi : C(H0, H0)) : C(X0, C0) :=
  ⟨fun x => (hamiltonZeroHierarchyCoordinates (phi (hamiltonZeroAmbientEquiv x))).2,
    continuous_snd.comp (hamiltonZeroHierarchyCoordinates.continuous.comp
      (phi.continuous.comp hamiltonZeroAmbientEquiv.continuous))⟩

theorem hamiltonZeroCircleMap_domain (phi : C(H0, H0)) (x : R0) :
    hamiltonZeroCircleMap phi (x : X0) =
      (hamiltonZeroHierarchyCoordinates (hamiltonZeroAmbientEquiv
        (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi x : X0))).2 := by
  let q := latticeHandleDomainEquiv (Fin 0) (Fin 3) L0
  change (hamiltonZeroHierarchyCoordinates (phi (hamiltonZeroAmbientEquiv x))).2 = _
  rw [hamiltonZeroAmbientEquiv_domain, hamiltonZeroAmbientEquiv_domain]
  change (hamiltonZeroHierarchyCoordinates (phi (q x))).2 =
    (hamiltonZeroHierarchyCoordinates (q (q.symm (phi (q x))))).2
  rw [q.apply_symm_apply]

theorem hamiltonZeroAmbientCircle_mk (x : Fin 0 → ℝ) (z : Fin 3 → ℝ) :
    (hamiltonZeroHierarchyCoordinates
      (hamiltonZeroAmbientEquiv (x, QuotientAddGroup.mk z))).2 = (z 2 : C0) := rfl

theorem surjective_hamiltonZeroCircleMap (phi : C(H0, H0))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    Function.Surjective (hamiltonZeroCircleMap phi) := by
  let Q := hamiltonZeroHierarchyCoordinates
  let j : C(C0, H0) :=
    ⟨fun c => Q.symm (((0, 0) : C0 × C0), c),
      Q.symm.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let h : C(C0, C0) :=
    ⟨fun c => (Q (phi (j c))).2,
      continuous_snd.comp (Q.continuous.comp (phi.continuous.comp j.continuous))⟩
  let H : (ContinuousMap.id C0).Homotopy h := {
    toFun := fun z => (Q (F (z.1, j z.2))).2
    continuous_toFun := continuous_snd.comp (Q.continuous.comp
      (F.continuous_toFun.comp (continuous_fst.prodMk
        (j.continuous.comp continuous_snd))))
    map_zero_left := by
      intro c
      change (Q (F.toFun (0, j c))).2 = c
      rw [F.map_zero_left]
      change (Q (Q.symm (((0, 0) : C0 × C0), c))).2 = c
      rw [Q.apply_symm_apply]
    map_one_left := by
      intro c
      change (Q (F.toFun (1, j c))).2 = (Q (phi (j c))).2
      rw [F.map_one_left]
  }
  intro c
  obtain ⟨z, hz⟩ := AddCircle.surjective_of_homotopy_id (4 * (16 : ℝ)) H c
  refine ⟨hamiltonZeroAmbientEquiv.symm (j z), ?_⟩
  change (Q (phi (hamiltonZeroAmbientEquiv
    (hamiltonZeroAmbientEquiv.symm (j z))))).2 = c
  rw [hamiltonZeroAmbientEquiv.apply_symm_apply]
  exact hz

end PoincareConjecture.M76
