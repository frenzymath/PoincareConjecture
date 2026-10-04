import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Cylinders.SeedCurvature
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scale-relative full curvature on a low-scalar cylinder

Morgan--Tian Lemma 11.2 and Corollary 4.33, pp. 268-269 and 80,
used in Proposition 16.1 on pp. 391-393. The small canonical radius
absorbs the absolute Hamilton--Ivey constant. This pointwise estimate
works for both the old-prefix seed and a small-radius test center.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.Proofs.M46

/-- The absolute pinching constant is smaller than the scalar scale
at any of the controlled radii, Corollary 4.33, p. 80. -/
theorem exp_four_le_four_inv_sq {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 200) :
    Real.exp 4 ≤ 4 * r⁻¹ ^ 2 := by
  have hexp : Real.exp 4 < 81 := by
    have hpow := pow_lt_pow_left₀ (Real.exp_one_lt_three) (Real.exp_pos 1).le
      (by norm_num : (4 : ℕ) ≠ 0)
    have heq : Real.exp 4 = (Real.exp 1) ^ (4 : ℕ) := by
      calc
        Real.exp 4 = Real.exp ((4 : ℝ) * 1) := by norm_num
        _ = _ := Real.exp_nat_mul 1 4
    rw [heq]
    norm_num at hpow ⊢
    exact hpow
  have hinv : (200 : ℝ) ≤ r⁻¹ := by
    have h := one_div_le_one_div_of_le hr hrsmall
    norm_num at h
    exact h
  nlinarith [sq_nonneg (r⁻¹ - 200)]

/-- A scalar ceiling at four times a controlled scale gives full
curvature at most fifty-two times that scale, Corollary 4.33, p. 80. -/
theorem low_scalar_curvature_le_fifty_two (P : M46Predecessors.{u})
    {F : SurgeryFlowData.{u}} {t r : ℝ}
    (hpinch : SurgeryPinchedAt (F.connection t) t)
    (hr : 0 < r) (hrsmall : r ≤ 1 / 200)
    (x : (F.slice t).carrier)
    (hscalar : (F.connection t).scalarCurvature x ≤ 4 * r⁻¹ ^ 2) :
    (F.connection t).curvatureTensorNorm x ≤ 52 * r⁻¹ ^ 2 := by
  have h := pinched_curvature_norm_le P hpinch (Set.mem_univ x)
  have hmax : max ((F.connection t).scalarCurvature x) (Real.exp 4) ≤ 4 * r⁻¹ ^ 2 :=
    max_le hscalar (exp_four_le_four_inv_sq hr hrsmall)
  nlinarith

end PoincareMT.Proofs.M46
