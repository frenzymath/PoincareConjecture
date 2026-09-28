import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal



set_option autoImplicit false

open Filter
open scoped Topology

namespace Poincare.Analysis

theorem summable_gaussian_shells (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun m : ℕ => Real.exp (-a * (m : ℝ) ^ 2) * ((m : ℝ) + 1) ^ n) := by
  have hs := ((summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul n ha)).mul_right (Real.exp a)
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro m
  simp only [Nat.cast_add, Nat.cast_one]
  have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    exact_mod_cast (show m ≤ m ^ 2 by simpa only [pow_two] using Nat.le_mul_self m)
  calc
    Real.exp (-a * (m : ℝ) ^ 2) * ((m : ℝ) + 1) ^ n ≤
        Real.exp (-a * (m : ℝ)) * ((m : ℝ) + 1) ^ n := by
      apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
      exact mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr ha.le)
    _ = (((m : ℝ) + 1) ^ n * Real.exp (-a * ((m : ℝ) + 1))) * Real.exp a := by
      rw [mul_assoc, ← Real.exp_add]
      rw [mul_comm (Real.exp (-a * (m : ℝ)))]
      congr 2
      ring

noncomputable def gaussianShellSum (n : ℕ) (a : ℝ) : ℝ :=
  ∑' m : ℕ, Real.exp (-a * (m : ℝ) ^ 2) * ((m : ℝ) + 1) ^ n

theorem gaussianShellSum_nonneg (n : ℕ) (a : ℝ) : 0 ≤ gaussianShellSum n a :=
  tsum_nonneg (fun _ => by positivity)

theorem exists_pos_radius_gaussian_small {a C ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ C * Real.exp (-a * R ^ 2) < ε := by
  have hlim : Tendsto (fun R : ℝ => C * Real.exp (-a * R ^ 2)) atTop (𝓝 0) := by
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop ha)
    simpa only [Function.comp_def, neg_mul, mul_zero] using hexp.const_mul C
  exact ((eventually_gt_atTop (0 : ℝ)).and (hlim.eventually (gt_mem_nhds hε))).exists

end Poincare.Analysis
