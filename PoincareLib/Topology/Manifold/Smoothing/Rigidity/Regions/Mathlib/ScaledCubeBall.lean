import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Positive coordinate cubes with their complete boundaries

The actual positive scalar image of the unit cube retains its full
norm sphere. This supplies the inner cube in the finite PL collar
attachment. See Hudson1969, pp.15--19 and rigidity047, section3.
-/

set_option autoImplicit false

open Set Metric Geometry
open scoped Pointwise

namespace Set

/-- Every positive-radius finite coordinate cube is a finite PL
ball pair with its whole norm sphere. See rigidity047, section3. -/
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
