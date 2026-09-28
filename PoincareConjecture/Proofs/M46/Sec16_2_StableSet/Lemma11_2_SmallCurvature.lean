import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_SeedCurvature
import Mathlib.Analysis.Complex.ExponentialBounds










set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46



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

end PoincareConjecture.Proofs.M46
