import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace Poincare.Analysis



theorem quadratic_upper_bound_of_hasDerivAt2_le
    {f f' f'' : ℝ → ℝ} {T H : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo 0 T, HasDerivAt f' (f'' t) t)
    (hH : ∀ t ∈ Ioo 0 T, f'' t ≤ H) :
    f T ≤ f 0 + T * f' 0 + H * T ^ 2 / 2 := by
  rcases hT.eq_or_lt with hT | hT
  · simp [← hT]
  let F : ℝ → ℝ := fun t => f t - H * t ^ 2 / 2
  let F' : ℝ → ℝ := fun t => f' t - H * t
  have hF : ∀ t ∈ Icc 0 T, HasDerivAt F (F' t) t := by
    intro t ht
    convert! (hf t ht).sub ((((hasDerivAt_id t).pow 2).const_mul H).div_const 2)
      using 1
    dsimp [F, F']
    ring
  have hF' : ∀ t ∈ Ioo 0 T, HasDerivAt F' (f'' t - H) t := by
    intro t ht
    convert! (hf' t ht).sub ((hasDerivAt_id t).const_mul H) using 1
    simp
  have hconc : ConcaveOn ℝ (Icc 0 T) F := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 T)
      (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
      (f' := F') (f'' := fun t => f'' t - H)
    · intro t ht
      exact (hF t (Ioo_subset_Icc_self (by simpa only [interior_Icc] using ht))).hasDerivWithinAt
    · intro t ht
      exact (hF' t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact sub_nonpos.mpr (hH t (by simpa only [interior_Icc] using ht))
  have hslope := hconc.slope_le_of_hasDerivAt (left_mem_Icc.mpr hT.le)
    (right_mem_Icc.mpr hT.le) hT (hF 0 (left_mem_Icc.mpr hT.le))
  rw [slope_def_field, sub_zero] at hslope
  have hbound := (div_le_iff₀ hT).mp hslope
  dsimp [F, F'] at hbound
  nlinarith



theorem deriv_lower_bound_of_endpoint_approx
    {f f' f'' d : ℝ → ℝ} {T H ε E : ℝ} (hT : 0 < T)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo 0 T, HasDerivAt f' (f'' t) t)
    (hH : ∀ t ∈ Ioo 0 T, f'' t ≤ H)
    (h0 : |f 0 - d 0| ≤ ε) (hTerror : |f T - d T| ≤ ε)
    (hincrement : T - E ≤ d T - d 0) :
    1 - (E + 2 * ε) / T - H * T / 2 ≤ f' 0 := by
  have hquad := quadratic_upper_bound_of_hasDerivAt2_le hT.le hf hf' hH
  have hleft := (abs_le.mp h0).2
  have hright := (abs_le.mp hTerror).1
  have hbound : T - (E + 2 * ε) - H * T ^ 2 / 2 ≤ f' 0 * T := by
    nlinarith
  have hdiv := (div_le_iff₀ hT).mpr hbound
  have heq : 1 - (E + 2 * ε) / T - H * T / 2 =
      (T - (E + 2 * ε) - H * T ^ 2 / 2) / T := by
    field_simp
  rw [heq]
  exact hdiv

end Poincare.Analysis
