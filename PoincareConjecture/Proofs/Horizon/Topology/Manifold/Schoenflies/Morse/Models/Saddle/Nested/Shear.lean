import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Shear







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)

def shear (b : Real) : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun p := p + ((p 0)^2 + (p 1)^2 + b * p 0) • EuclideanSpace.single 2 1
  invFun p := p - ((p 0)^2 + (p 1)^2 + b * p 0) • EuclideanSpace.single 2 1
  left_inv p := by ext i; simp
  right_inv p := by ext i; simp
  contMDiff_toFun := (contDiff_id.add
    ((by fun_prop : ContDiff Real ∞ (fun p : E3 => (p 0)^2 + (p 1)^2 + b * p 0)).smul
      contDiff_const)).contMDiff
  contMDiff_invFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun p : E3 => p - ((p 0)^2 + (p 1)^2 + b * p 0) • EuclideanSpace.single 2 1)
    exact (contDiff_id.sub
      ((by fun_prop : ContDiff Real ∞ (fun p : E3 => (p 0)^2 + (p 1)^2 + b * p 0)).smul
        contDiff_const)).contMDiff

theorem shear_apply (b : Real) (p : E3) :
    shear b p = p + ((p 0)^2 + (p 1)^2 + b * p 0) • EuclideanSpace.single 2 1 := rfl

theorem shear_symm_apply (b : Real) (p : E3) :
    (shear b).symm p = p - ((p 0)^2 + (p 1)^2 + b * p 0) •
      EuclideanSpace.single 2 1 := rfl

@[simp] theorem shear_zero (b : Real) (p : E3) : shear b p 0 = p 0 := by
  rw [shear_apply]
  simp

@[simp] theorem shear_one (b : Real) (p : E3) : shear b p 1 = p 1 := by
  rw [shear_apply]
  simp

@[simp] theorem shear_two (b : Real) (p : E3) :
    shear b p 2 = p 2 + (p 0)^2 + (p 1)^2 + b * p 0 := by
  rw [shear_apply]
  simp
  ring

@[simp] theorem shear_symm_zero (b : Real) (p : E3) : (shear b).symm p 0 = p 0 := by
  rw [shear_symm_apply]
  simp

@[simp] theorem shear_symm_one (b : Real) (p : E3) : (shear b).symm p 1 = p 1 := by
  rw [shear_symm_apply]
  simp

@[simp] theorem shear_symm_two (b : Real) (p : E3) :
    (shear b).symm p 2 = p 2 - ((p 0)^2 + (p 1)^2 + b * p 0) := by
  rw [shear_symm_apply]
  simp

def polynomial (b : Real) (p : E3) : Real :=
  (p 0)^2 + (p 1)^2 + (p 2 - ((p 0)^2 + (p 1)^2 + b * p 0))^2

theorem norm_shear_symm_sq (b : Real) (p : E3) :
    ‖(shear b).symm p‖^2 = polynomial b p := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, polynomial,
    Real.norm_eq_abs, sq_abs]

private theorem mem_shear_image (b : Real) (p : E3) (K : Set E3) :
    p ∈ shear b '' K ↔ (shear b).symm p ∈ K := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [Diffeomorph.symm_apply_apply] using hq
  · intro hp
    exact ⟨(shear b).symm p, hp, (shear b).apply_symm_apply p⟩

theorem shear_image_closedBall (b : Real) :
    shear b '' closedBall (0 : E3) 1 = {p | polynomial b p ≤ 1} := by
  ext p
  rw [mem_shear_image, mem_closedBall_zero_iff]
  change ‖(shear b).symm p‖ ≤ 1 ↔ polynomial b p ≤ 1
  rw [← norm_shear_symm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg ((shear b).symm p)]

theorem shear_image_ball (b : Real) :
    shear b '' ball (0 : E3) 1 = {p | polynomial b p < 1} := by
  ext p
  rw [mem_shear_image, mem_ball_zero_iff]
  change ‖(shear b).symm p‖ < 1 ↔ polynomial b p < 1
  rw [← norm_shear_symm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg ((shear b).symm p)]

theorem shear_image_sphere (b : Real) :
    shear b '' sphere (0 : E3) 1 = {p | polynomial b p = 1} := by
  ext p
  rw [mem_shear_image, mem_sphere_zero_iff_norm]
  change ‖(shear b).symm p‖ = 1 ↔ polynomial b p = 1
  rw [← norm_shear_symm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg ((shear b).symm p)]

end Poincare.Manifold.Schoenflies.Saddle.Nested
