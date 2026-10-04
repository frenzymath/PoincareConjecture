import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Flatness of the smooth glue function

The fixed profile in Morgan--Tian, pp. 451-452, must vanish to every order at
each polygon vertex. These real-analysis lemmas supply flatness of the exact
Mathlib glue function and preserve it under smooth composition.
-/

set_option autoImplicit false

open scoped ContDiff

namespace expNegInvGlue

/-- Every derivative of the glue function vanishes at zero, as required by
the flattening profile in Morgan--Tian, p. 451, property (1). -/
theorem iteratedDeriv_zero (i : ℕ) : iteratedDeriv i expNegInvGlue 0 = 0 := by
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic 0)
    expNegInvGlue.contDiff.contDiffAt (show (0 : ℝ) ∈ Set.Iic 0 by simp)]
  have hzero : Set.EqOn expNegInvGlue (fun _ : ℝ => (0 : ℝ)) (Set.Iic 0) :=
    fun _ hx => expNegInvGlue.zero_of_nonpos hx
  rw [iteratedDerivWithin_congr hzero (show (0 : ℝ) ∈ Set.Iic 0 by simp)]
  exact iteratedDerivWithin_fun_const_zero

/-- A smooth inner function taking value zero gives a flat composite;
Morgan--Tian, p. 451, property (1), for the specified profile formula. -/
theorem iteratedDeriv_comp_zero {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hx : f x = 0) (i : ℕ) :
    iteratedDeriv i (expNegInvGlue ∘ f) x = 0 := by
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    expNegInvGlue.contDiff.contDiffAt hf (by exact_mod_cast le_top (a := (i : ℕ∞)))]
  simp only [hx, iteratedDeriv_zero, zero_mul, Finset.sum_const_zero]

end expNegInvGlue
