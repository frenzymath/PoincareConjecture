import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E3 := EuclideanSpace Real (Fin 3)


def shear : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun p := p - (p 0) ^ 2 • EuclideanSpace.single 2 1
  invFun p := p + (p 0) ^ 2 • EuclideanSpace.single 2 1
  left_inv p := by
    ext i
    simp
  right_inv p := by
    ext i
    simp
  contMDiff_toFun := (contDiff_id.sub
    (((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff.pow 2).smul
      contDiff_const)).contMDiff
  contMDiff_invFun := (contDiff_id.add
    (((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff.pow 2).smul
      contDiff_const)).contMDiff

theorem shear_apply (p : E3) :
    shear p = p - (p 0) ^ 2 • EuclideanSpace.single 2 1 := rfl

theorem shear_symm_apply (p : E3) :
    shear.symm p = p + (p 0) ^ 2 • EuclideanSpace.single 2 1 := rfl

@[simp] theorem shear_zero (p : E3) : shear p 0 = p 0 := by
  rw [shear_apply]
  simp

@[simp] theorem shear_one (p : E3) : shear p 1 = p 1 := by
  rw [shear_apply]
  simp

@[simp] theorem shear_two (p : E3) : shear p 2 = p 2 - (p 0) ^ 2 := by
  rw [shear_apply]
  simp

@[simp] theorem shear_symm_zero (p : E3) : shear.symm p 0 = p 0 := by
  rw [shear_symm_apply]
  simp

@[simp] theorem shear_symm_one (p : E3) : shear.symm p 1 = p 1 := by
  rw [shear_symm_apply]
  simp

@[simp] theorem shear_symm_two (p : E3) : shear.symm p 2 = p 2 + (p 0) ^ 2 := by
  rw [shear_symm_apply]
  simp


def polynomial (p : E3) : Real := (p 0) ^ 2 + (p 1) ^ 2 + (p 2 + (p 0) ^ 2) ^ 2

theorem norm_shear_symm_sq (p : E3) : ‖shear.symm p‖ ^ 2 = polynomial p := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, polynomial,
    Real.norm_eq_abs, sq_abs]

private theorem mem_shear_image (p : E3) (K : Set E3) :
    p ∈ shear '' K ↔ shear.symm p ∈ K := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [Diffeomorph.symm_apply_apply] using hq
  · intro hp
    exact ⟨shear.symm p, hp, shear.apply_symm_apply p⟩


theorem shear_image_closedBall :
    shear '' closedBall (0 : E3) 1 = {p | polynomial p ≤ 1} := by
  ext p
  rw [mem_shear_image, mem_closedBall_zero_iff]
  change ‖shear.symm p‖ ≤ 1 ↔ polynomial p ≤ 1
  rw [← norm_shear_symm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg (shear.symm p)]


theorem shear_image_ball :
    shear '' ball (0 : E3) 1 = {p | polynomial p < 1} := by
  ext p
  rw [mem_shear_image, mem_ball_zero_iff]
  change ‖shear.symm p‖ < 1 ↔ polynomial p < 1
  rw [← norm_shear_symm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg (shear.symm p)]


theorem shear_image_sphere :
    shear '' sphere (0 : E3) 1 = {p | polynomial p = 1} := by
  ext p
  rw [mem_shear_image, mem_sphere_zero_iff_norm]
  change ‖shear.symm p‖ = 1 ↔ polynomial p = 1
  rw [← norm_shear_symm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg (shear.symm p)]

theorem frontier_shear_image_closedBall :
    frontier (shear '' closedBall (0 : E3) 1) = {p | polynomial p = 1} := by
  rw [← shear_image_sphere]
  exact (shear.toHomeomorph.image_frontier _).symm.trans
    (congrArg (fun K => shear '' K) (frontier_closedBall (0 : E3)
      (by norm_num : (1 : Real) ≠ 0)))

end Poincare.Manifold.Schoenflies.Saddle
