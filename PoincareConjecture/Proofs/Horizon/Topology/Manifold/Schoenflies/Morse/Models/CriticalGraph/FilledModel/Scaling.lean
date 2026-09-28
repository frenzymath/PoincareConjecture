import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.ProfileGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Pointwise

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem quadraticMinimumCapPoint_dilation {v : E3} (hv : ‖v‖ = 1)
    (c : Real) {r : Real} (hr : 0 < r)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (hA : ∀ x, A x = r • x) (x : Hemisphere.Plane v) :
    liftPlaneDiffeomorph hv (c + 2 * r ^ 2) (r ^ 2) (sq_pos_of_pos hr).ne' A
      (quadraticMinimumCapPoint v (-2) 1 x) =
        quadraticMinimumCapPoint v c r (r • x) := by
  have hn : ‖r • x‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
  have hu : r ^ 2 * ‖x‖ ^ 2 / r ^ 2 = ‖x‖ ^ 2 := by field_simp
  rw [liftPlaneDiffeomorph_apply, inner_quadraticMinimumCapPoint hv,
    projection_quadraticMinimumCapPoint, hA, quadraticMinimumCapPoint, hn, hu]
  simp only [one_pow, div_one, Submodule.coe_smul]
  module

theorem image_quadraticMinimumCap_of_dilation {v : E3} (hv : ‖v‖ = 1)
    (c : Real) {r : Real} (hr : 0 < r)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (hA : ∀ x, A x = r • x) :
    liftPlaneDiffeomorph hv (c + 2 * r ^ 2) (r ^ 2) (sq_pos_of_pos hr).ne' A ''
      quadraticMinimumCap v (-2) 1 = quadraticMinimumCap v c r := by
  have hball : (fun x : Hemisphere.Plane v => r • x) '' closedBall 0 (7 / 8 : Real) =
      closedBall 0 (7 * r / 8) := by
    change r • closedBall (0 : Hemisphere.Plane v) (7 / 8 : Real) = _
    rw [smul_closedBall' hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr]
    congr 1
    ring
  unfold quadraticMinimumCap
  simp only [mul_one]
  rw [← hball, image_image, image_image]
  apply image_congr
  intro x _
  exact quadraticMinimumCapPoint_dilation hv c hr A hA x

end Poincare.Manifold.Schoenflies
