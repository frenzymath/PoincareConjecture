import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set

theorem le_gronwallBound_of_interior_deriv_le
    {f : ℝ → ℝ} {a b C ε δ : ℝ} (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hfa : f a ≤ δ)
    (hr : ∀ t ∈ Ioo a b, deriv f t ≤ C * f t + ε) :
    ∀ t ∈ Icc a b, f t ≤ gronwallBound δ C ε (t - a) := by
  let g : ℝ → ℝ := fun t => gronwallBound δ C ε (t - a)
  have hgd (t : ℝ) : HasDerivAt g (C * g t + ε) t :=
    hasDerivAt_gronwallBound_shift δ C ε t a
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hgd t).continuousAt)
  let H : ℝ → ℝ := fun t => Real.exp (-C * (t - a)) * (f t - g t)
  have hH : ContinuousOn H (Icc a b) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.mul
      (hf.sub hg.continuousOn)
  have hHd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt H (Real.exp (-C * (t - a)) * (deriv f t - C * f t - ε)) t := by
    convert! (((hasDerivAt_id t).sub_const a).const_mul (-C)).exp.mul
      ((hd t ht).hasDerivAt.sub (hgd t)) using 1
    simp only [id_eq, Pi.sub_apply]
    ring
  have hanti : AntitoneOn H (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hH
    · intro t ht
      rw [interior_Icc] at ht
      exact (hHd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hHd t ht).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hr t ht])
  intro t ht
  have hle := hanti (show a ∈ Icc a b from ⟨le_rfl, ht.1.trans ht.2⟩) ht ht.1
  have hHa : H a ≤ 0 := by
    simpa only [H, g, sub_self, gronwallBound_x0, mul_zero, Real.exp_zero, one_mul]
      using sub_nonpos.mpr hfa
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right (hle.trans hHa) (Real.exp_pos _))
