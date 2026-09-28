import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false

open Set

namespace PoincareConjecture.Proofs.M03

theorem eq_zero_on_interval_of_deriv_le_mul
    {a b C : ℝ} {E : ℝ → ℝ}
    (hE : ContinuousOn E (Icc a b))
    (hEd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ E t)
    (hE0 : E a = 0)
    (hEn : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hE' : ∀ t ∈ Ioo a b, deriv E t ≤ C * E t) :
    EqOn E (fun _ => 0) (Icc a b) := by
  let H : ℝ → ℝ := fun t => Real.exp (-C * (t - a)) * E t
  have hH : ContinuousOn H (Icc a b) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.mul hE
  have hHd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt H (Real.exp (-C * (t - a)) * (deriv E t - C * E t)) t := by
    convert! (((hasDerivAt_id t).sub_const a).const_mul (-C)).exp.mul
      (hEd t ht).hasDerivAt using 1
    simp only [id_eq]
    ring
  have hanti : AntitoneOn H (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hH
    · intro t ht
      rw [interior_Icc] at ht
      exact (hHd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hHd t ht).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hE' t ht))
  intro t ht
  have hle := hanti (show a ∈ Icc a b from ⟨le_rfl, ht.1.trans ht.2⟩) ht ht.1
  have hHa : H a = 0 := by simp only [H, hE0, mul_zero]
  rw [hHa] at hle
  have hzero : Real.exp (-C * (t - a)) * E t = 0 :=
    le_antisymm hle (mul_nonneg (Real.exp_pos _).le (hEn t ht))
  exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (Real.exp_pos _))

end PoincareConjecture.Proofs.M03
