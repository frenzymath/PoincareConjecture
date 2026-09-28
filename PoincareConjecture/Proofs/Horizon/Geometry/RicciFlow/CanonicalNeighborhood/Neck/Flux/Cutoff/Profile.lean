import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture

def axialTransitionProfile (L s : ℝ) : ℝ :=
  Real.smoothTransition ((s + L) / (2 * L))

theorem contDiff_axialTransitionProfile (L : ℝ) :
    ContDiff ℝ ∞ (axialTransitionProfile L) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem axialTransitionProfile_zero {L s : ℝ} (hL : 0 < L) (hs : s ≤ -L) :
    axialTransitionProfile L s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem axialTransitionProfile_one {L s : ℝ} (hL : 0 < L) (hs : L ≤ s) :
    axialTransitionProfile L s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (one_le_div (by positivity)).mpr (by linarith)

theorem axialTransitionProfile_mem_Icc (L s : ℝ) :
    axialTransitionProfile L s ∈ Icc 0 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem monotone_axialTransitionProfile {L : ℝ} (hL : 0 < L) :
    Monotone (axialTransitionProfile L) := by
  intro s t hst
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem deriv_axialTransitionProfile_nonneg {L : ℝ} (hL : 0 < L) (s : ℝ) :
    0 ≤ deriv (axialTransitionProfile L) s :=
  (monotone_axialTransitionProfile hL).deriv_nonneg

theorem integral_deriv_axialTransitionProfile {L : ℝ} (hL : 0 < L) :
    (∫ s in -L..L, deriv (axialTransitionProfile L) s) = 1 := by
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun s _ => (contDiff_axialTransitionProfile L).differentiable (by simp) s)
    (((contDiff_axialTransitionProfile L).continuous_deriv (by simp)).intervalIntegrable _ _),
    axialTransitionProfile_one hL le_rfl, axialTransitionProfile_zero hL le_rfl]
  norm_num




theorem lintegral_ofReal_mul_deriv_axialTransitionProfile
    {L κ : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ) :
    ∫⁻ s in Ioo (-L) L,
      ENNReal.ofReal (κ * deriv (axialTransitionProfile L) s) =
      ENNReal.ofReal κ := by
  let f : ℝ → ℝ := fun s => κ * deriv (axialTransitionProfile L) s
  have hf_cont : Continuous f := by
    exact continuous_const.mul
      ((contDiff_axialTransitionProfile L).continuous_deriv (by simp))
  have hf_cc : IntegrableOn f (Icc (-L) L) := hf_cont.integrableOn_Icc
  have hf_oo : IntegrableOn f (Ioo (-L) L) :=
    (integrableOn_Icc_iff_integrableOn_Ioo).mp hf_cc
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Ioo (-L) L)] f := by
    filter_upwards [] with s
    exact mul_nonneg hκ (deriv_axialTransitionProfile_nonneg hL s)
  have hreal : (∫ s in Ioo (-L) L, f s) = κ := by
    calc
      (∫ s in Ioo (-L) L, f s) = ∫ s in Icc (-L) L, f s :=
        integral_Icc_eq_integral_Ioo.symm
      _ = ∫ s in Ioc (-L) L, f s := integral_Icc_eq_integral_Ioc
      _ = ∫ s in -L..L, f s :=
        (intervalIntegral.integral_of_le (by linarith)).symm
      _ = κ := by
        change (∫ s in -L..L, κ * deriv (axialTransitionProfile L) s) = κ
        rw [intervalIntegral.integral_const_mul,
          integral_deriv_axialTransitionProfile hL]
        simp
  have hconvert := ofReal_integral_eq_lintegral_ofReal hf_oo hf_nonneg
  calc
    (∫⁻ s in Ioo (-L) L, ENNReal.ofReal (κ * deriv (axialTransitionProfile L) s)) =
        ∫⁻ s in Ioo (-L) L, ENNReal.ofReal (f s) := by rfl
    _ = ENNReal.ofReal (∫ s in Ioo (-L) L, f s) := hconvert.symm
    _ = ENNReal.ofReal κ := by rw [hreal]

end PoincareConjecture
