import PoincareConjecture.Proofs.Horizon.Analysis.Convex.Semiconcavity.Derivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_le_of_approx_of_backward_increment
    {u F : E → ℝ} (hu : ContDiff ℝ 2 u) {y v : E} {T ε c Cf Cu : ℝ}
    (hT : 0 < T)
    (herr : ∀ t ∈ Icc (0 : ℝ) T, |u (y - t • v) - F (y - t • v)| ≤ ε)
    (hH : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ (fderiv ℝ u) (y - t • v) v v ≤ Cu * ‖v‖ ^ 2)
    (hinc : F y - F (y - T • v) ≤ c * T + Cf * T ^ 2 * ‖v‖ ^ 2 / 2) :
    fderiv ℝ u y v ≤ c + 2 * ε / T + (Cf + Cu) * T * ‖v‖ ^ 2 / 2 := by
  let q : ℝ → E := fun t => y - t • v
  let f : ℝ → ℝ := fun t => u (q t)
  let f' : ℝ → ℝ := fun t => -fderiv ℝ u (q t) v
  let f'' : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (q t) v v
  have hq (t : ℝ) : HasDerivAt q (-v) t := by
    simpa only [q, id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_sub y
  have hfirst (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt f (f' t) t := by
    simpa only [f, f', Function.comp_def, map_neg] using
      ((hu.differentiable (by norm_num) (q t)).hasFDerivAt.comp_hasDerivAt t (hq t))
  have hsecond (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) T) : HasDerivAt f' (f'' t) t := by
    have hdu : DifferentiableAt ℝ (fderiv ℝ u) (q t) :=
      ((hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    have h := ((hdu.hasFDerivAt.comp_hasDerivAt t (hq t)).clm_apply
      (hasDerivAt_const t v)).neg
    convert! h using 1
    simp only [f'', map_neg, neg_apply, map_zero, add_zero, neg_neg]
  have htaylor := quadratic_upper_bound_of_hasDerivAt2_le hT.le hfirst hsecond
    (fun t ht => hH t ⟨ht.1.le, ht.2.le⟩)
  have hzero := (abs_le.mp (herr 0 ⟨le_rfl, hT.le⟩)).2
  have hlast := (abs_le.mp (herr T ⟨hT.le, le_rfl⟩)).1
  simp only [f, f', q, zero_smul, sub_zero] at htaylor hzero
  have hbound : fderiv ℝ u y v * T ≤
      c * T + 2 * ε + (Cf + Cu) * T ^ 2 * ‖v‖ ^ 2 / 2 := by
    nlinarith [htaylor, hzero, hlast, hinc]
  have hdiv := (le_div_iff₀ hT).mpr hbound
  convert! hdiv using 1
  field_simp

end Poincare.Analysis
