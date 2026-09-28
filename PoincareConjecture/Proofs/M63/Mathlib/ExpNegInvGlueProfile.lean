import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open scoped ContDiff

namespace expNegInvGlue

theorem iteratedDeriv_zero (i : ℕ) : iteratedDeriv i expNegInvGlue 0 = 0 := by
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic 0)
    expNegInvGlue.contDiff.contDiffAt (show (0 : ℝ) ∈ Set.Iic 0 by simp)]
  have hzero : Set.EqOn expNegInvGlue (fun _ : ℝ => (0 : ℝ)) (Set.Iic 0) :=
    fun _ hx => expNegInvGlue.zero_of_nonpos hx
  rw [iteratedDerivWithin_congr hzero (show (0 : ℝ) ∈ Set.Iic 0 by simp)]
  exact iteratedDerivWithin_fun_const_zero

theorem iteratedDeriv_comp_zero {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hx : f x = 0) (i : ℕ) :
    iteratedDeriv i (expNegInvGlue ∘ f) x = 0 := by
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    expNegInvGlue.contDiff.contDiffAt hf (by exact_mod_cast le_top (a := (i : ℕ∞)))]
  simp only [hx, iteratedDeriv_zero, zero_mul, Finset.sum_const_zero]

end expNegInvGlue
