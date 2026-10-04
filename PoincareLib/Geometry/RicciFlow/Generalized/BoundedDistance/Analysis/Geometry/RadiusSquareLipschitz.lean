import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The half-square of a bounded Lipschitz radius

A bounded 1-Lipschitz real radius has a Lipschitz half-square potential.
This is the scalar estimate used for Morgan--Tian's finite cone annulus,
pp. 263-265; M28 derivation 150.
-/

set_option autoImplicit false

open scoped NNReal

/-- The half-square of a 1-Lipschitz real function bounded in absolute
value by B is B-Lipschitz. Source: M28 derivation 150. -/
theorem LipschitzWith.half_sq_of_abs_le
    {X : Type*} [PseudoMetricSpace X] {r : X → ℝ}
    (hr : LipschitzWith 1 r) {B : ℝ≥0}
    (hB : ∀ x, |r x| ≤ (B : ℝ)) :
    LipschitzWith B (fun x => r x ^ 2 / 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdiff : |r x - r y| ≤ dist x y := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hr.dist_le_mul x y
  have hsum : |r x + r y| ≤ 2 * (B : ℝ) := by
    calc
      _ ≤ |r x| + |r y| := abs_add_le _ _
      _ ≤ (B : ℝ) + B := add_le_add (hB x) (hB y)
      _ = _ := by ring
  rw [Real.dist_eq]
  calc
    |r x ^ 2 / 2 - r y ^ 2 / 2| = |r x - r y| * |r x + r y| / 2 := by
      rw [show r x ^ 2 / 2 - r y ^ 2 / 2 =
        (r x - r y) * (r x + r y) / 2 by ring, abs_div, abs_mul]
      norm_num
    _ ≤ dist x y * (2 * (B : ℝ)) / 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul hdiff hsum (abs_nonneg _) dist_nonneg) (by norm_num)
    _ = (B : ℝ) * dist x y := by ring
