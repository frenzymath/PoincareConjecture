import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open Set Metric
open scoped Manifold

namespace PoincareConjecture.M25.Topology3D

noncomputable def heightCoordinates :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) × ℝ :=
  (EuclideanSpace.finAddEquivProd (n := 2) (m := 1)).trans
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)))

@[simp] theorem heightCoordinates_fst_apply (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 2) :
    (heightCoordinates x).1 i = x i.castSucc := rfl

@[simp] theorem heightCoordinates_snd_apply (x : EuclideanSpace ℝ (Fin 3)) :
    (heightCoordinates x).2 = x 2 := rfl

theorem heightCoordinates_symm_apply (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    heightCoordinates.symm p = !₂[p.1 0, p.1 1, p.2] := by
  ext i
  fin_cases i <;> rfl

theorem heightCoordinates_norm_sq (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = ‖(heightCoordinates x).1‖ ^ 2 + (heightCoordinates x).2 ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  rfl

theorem heightCoordinates_symm_norm_sq (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    ‖heightCoordinates.symm p‖ ^ 2 = ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  simpa only [heightCoordinates.apply_symm_apply] using
    heightCoordinates_norm_sq (heightCoordinates.symm p)

theorem heightCoordinates_image_ball :
    heightCoordinates '' ball 0 1 =
      {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 < 1} := by
  ext p
  rw [heightCoordinates.image_eq_preimage_symm, mem_preimage, mem_ball_zero_iff,
    mem_ofPred_eq, ← heightCoordinates_symm_norm_sq]
  constructor <;> intro hp <;> nlinarith [norm_nonneg (heightCoordinates.symm p)]

theorem heightCoordinates_image_closedBall :
    heightCoordinates '' closedBall 0 1 =
      {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1} := by
  ext p
  rw [heightCoordinates.image_eq_preimage_symm, mem_preimage, mem_closedBall_zero_iff,
    mem_ofPred_eq, ← heightCoordinates_symm_norm_sq]
  constructor <;> intro hp <;> nlinarith [norm_nonneg (heightCoordinates.symm p)]

theorem heightCoordinates_image_sphere :
    heightCoordinates '' sphere 0 1 =
      {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = 1} := by
  ext p
  rw [heightCoordinates.image_eq_preimage_symm, mem_preimage, mem_sphere_zero_iff_norm,
    mem_ofPred_eq, ← heightCoordinates_symm_norm_sq]
  constructor <;> intro hp <;> nlinarith [norm_nonneg (heightCoordinates.symm p)]

end PoincareConjecture.M25.Topology3D
