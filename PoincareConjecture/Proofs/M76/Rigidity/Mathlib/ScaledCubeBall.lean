import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

open Set Metric Geometry
open scoped Pointwise

namespace Set

theorem isFinitePLBallPair_coordinate_cube {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : 0 < r) :
    IsFinitePLBallPair (ι → ℝ) (closedBall (0 : ι → ℝ) r)
      (sphere (0 : ι → ℝ) r) := by
  let A : (ι → ℝ) →ᴬ[ℝ] (ι → ℝ) :=
    (r • ContinuousLinearMap.id ℝ (ι → ℝ)).toContinuousAffineMap
  have hA : Function.Injective A := smul_right_injective (ι → ℝ) hr.ne'
  have h := (isFinitePLBallPair_unit_cube (ι := ι)).affine_image A hA.injOn
  have hball : A '' closedBall (0 : ι → ℝ) 1 = closedBall (0 : ι → ℝ) r := by
    change r • closedBall (0 : ι → ℝ) 1 = _
    rw [smul_closedBall' hr.ne']
    simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hsphere : A '' sphere (0 : ι → ℝ) 1 = sphere (0 : ι → ℝ) r := by
    change r • sphere (0 : ι → ℝ) 1 = _
    rw [smul_sphere' hr.ne']
    simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  rwa [hball, hsphere] at h

end Set
