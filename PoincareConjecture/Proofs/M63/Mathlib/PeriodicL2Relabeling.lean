import PoincareConjecture.Proofs.M63.Mathlib.PeriodicChangeOfVariables









set_option autoImplicit false

open MeasureTheory
open scoped intervalIntegral

namespace Function.Periodic




theorem integral_norm_sq_comp_le {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {P : ℝ} (hper : Function.Periodic f P) (hf : Continuous f)
    (hP : 0 < P) {phi : ℝ → ℝ} (hphi : ContDiff ℝ 1 phi)
    (hshift : ∀ x, phi (x + P) = phi x + P)
    {ell : ℝ} (hell : 0 < ell) (hderiv : ∀ x, ell ≤ deriv phi x) :
    (∫ x in (0 : ℝ)..P, ‖f (phi x)‖ ^ 2) ≤
      ell⁻¹ * ∫ x in (0 : ℝ)..P, ‖f x‖ ^ 2 := by
  have hg : Continuous (fun x => ‖f x‖ ^ 2) := hf.norm.pow 2
  have hgp : Function.Periodic (fun x => ‖f x‖ ^ 2) P := by
    intro x
    change ‖f (x + P)‖ ^ 2 = ‖f x‖ ^ 2
    rw [hper x]
  have hcomp : Continuous (fun x => ‖f (phi x)‖ ^ 2) := hg.comp hphi.continuous
  have hsub := hgp.integral_deriv_smul_comp_eq hg hphi hshift 0
  simp only [zero_add, smul_eq_mul] at hsub
  have hbound : ell * (∫ x in (0 : ℝ)..P, ‖f (phi x)‖ ^ 2) ≤
      ∫ x in (0 : ℝ)..P, ‖f x‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← hsub]
    exact intervalIntegral.integral_mono_on hP.le
      ((hcomp.const_mul ell).intervalIntegrable 0 P)
      ((hphi.continuous_deriv_one.mul hcomp).intervalIntegrable 0 P)
      (fun x _ => mul_le_mul_of_nonneg_right (hderiv x) (sq_nonneg _))
  calc
    _ = ell⁻¹ * (ell * (∫ x in (0 : ℝ)..P, ‖f (phi x)‖ ^ 2)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hell.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hell.le)

end Function.Periodic
