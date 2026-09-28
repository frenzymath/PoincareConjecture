import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.MarkedGluing










set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "D1" => closedBall (0 : V1) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "E" => latticeHandleDomainEquiv (Fin 1) (Fin 2) L
local notation "Q" => hamiltonOneHierarchyCoordinates


noncomputable def originalIntervalCoordinates : Icc (-1 : ℝ) 1 ≃ₜ D1 where
  toFun t := ⟨fun _ => (t : ℝ), by
    simpa only [mem_closedBall_zero_iff, pi_norm_const, Real.norm_eq_abs, abs_le, mem_Icc] using t.property⟩
  invFun x := ⟨x.val 0, by
    have hn : |x.val 0| ≤ 1 := (norm_le_pi_norm x.val 0).trans
      (mem_closedBall_zero_iff.mp x.property)
    exact abs_le.mp hn⟩
  left_inv t := rfl
  right_inv x := Subtype.ext (by funext i; exact congrArg x.val (Subsingleton.elim 0 i))
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 0).comp continuous_subtype_val



noncomputable def standardPhaseCoordinates (theta : C) :
    (D1 × C) ≃ₜ sourceSurface (ContinuousMap.id H) theta where
  toFun z := ⟨(E).symm ((Q).symm (z, theta)), by
    apply (mem_sourceSurface_iff (ContinuousMap.id H) theta ((E).symm ((Q).symm (z, theta)))).mpr
    change (Q ((E) ((E).symm ((Q).symm (z, theta))))).2 = theta
    rw [(E).apply_symm_apply, (Q).apply_symm_apply]⟩
  invFun x := (Q ((E) ⟨x, sourceSurface_subset (ContinuousMap.id H) theta x.property⟩)).1
  left_inv z := by
    change (Q ((E) ((E).symm ((Q).symm (z, theta))))).1 = z
    rw [(E).apply_symm_apply, (Q).apply_symm_apply]
  right_inv x := by
    let xR : R := ⟨x, sourceSurface_subset (ContinuousMap.id H) theta x.property⟩
    have hx : (Q ((E) xR)).2 = theta :=
      (mem_sourceSurface_iff (ContinuousMap.id H) theta xR).mp x.property
    apply Subtype.ext
    change ((E).symm ((Q).symm ((Q ((E) xR)).1, theta)) : X) = x
    have hpair : ((Q ((E) xR)).1, theta) = Q ((E) xR) := Prod.ext rfl hx.symm
    rw [hpair, (Q).symm_apply_apply, (E).symm_apply_apply]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop


noncomputable def standardAnnulusCylinderCoordinates : (unitInterval × C32) ≃ₜ (D1 × C) :=
  ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm.trans originalIntervalCoordinates).prodCongr
    (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
      (by norm_num) (by norm_num))

theorem standardAnnulusCylinderCoordinates_rim (side : Bool) (z : C32) :
    standardAnnulusCylinderCoordinates ((if side then 1 else 0), z) =
      (originalIntervalEndpoint side,
        AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
          (by norm_num) (by norm_num) z) := by
  apply Prod.ext
  · apply Subtype.ext
    funext i
    cases side <;>
      simp [standardAnnulusCylinderCoordinates, originalIntervalCoordinates,
        originalIntervalEndpoint, iccHomeoI_symm_apply_coe]
  · rfl



noncomputable def standardTargetAnnulus (theta : C) :
    Ann ≃ₜ sourceSurface (ContinuousMap.id H) theta :=
  Dehn.annulusCylinderHomeomorph.symm.trans
    (standardAnnulusCylinderCoordinates.trans (standardPhaseCoordinates theta))

theorem standardTargetAnnulus_rim (theta : C) (side : Bool) (z : C32) :
    (standardTargetAnnulus theta (Dehn.annulusRimPoint side z) : X) =
      (sourceBoundaryCircle (ContinuousMap.id H) theta (.refl _ _)
        (originalIntervalEndpoint side) (originalIntervalEndpoint_norm side)
        (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
          (by norm_num) (by norm_num) z) : X) := by
  have hzero : Dehn.annulusCylinderHomeomorph.symm (Dehn.annulusRimPoint false z) = (0, z) := by
    rw [← Dehn.annulusCylinderHomeomorph_zero, Homeomorph.symm_apply_apply]
  have hone : Dehn.annulusCylinderHomeomorph.symm (Dehn.annulusRimPoint true z) = (1, z) := by
    rw [← Dehn.annulusCylinderHomeomorph_one, Homeomorph.symm_apply_apply]
  cases side
  · simp only [standardTargetAnnulus, Homeomorph.trans_apply]
    rw [hzero, show standardAnnulusCylinderCoordinates (0, z) = _ from
      standardAnnulusCylinderCoordinates_rim false z]
    rfl
  · simp only [standardTargetAnnulus, Homeomorph.trans_apply]
    rw [hone, show standardAnnulusCylinderCoordinates (1, z) = _ from
      standardAnnulusCylinderCoordinates_rim true z]
    rfl

end PoincareConjecture.M76.HamiltonIntervalTorus
