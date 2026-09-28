import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M65StrictTrace



def boundaryCoordinate (p z : ℂ) : ℂ := p * exp (I * z)



def boundaryInverse (p w : ℂ) : ℂ := -I * log (w / p)



theorem contDiff_boundaryCoordinate (p : ℂ) :
    ContDiff ℂ ∞ (boundaryCoordinate p) :=
  contDiff_const.mul (contDiff_exp.comp (contDiff_const.mul contDiff_id))



theorem hasDerivAt_boundaryCoordinate (p z : ℂ) :
    HasDerivAt (boundaryCoordinate p) (I * boundaryCoordinate p z) z := by
  have h : HasDerivAt (fun w : ℂ => p * exp (I * w))
      (p * (exp (I * z) * I)) z := by
    exact (hasDerivAt_const_mul p).comp z
      ((hasDerivAt_exp (I * z)).comp z (hasDerivAt_const_mul I))
  have hder : I * boundaryCoordinate p z = p * (exp (I * z) * I) := by
    dsimp only [boundaryCoordinate]
    ring
  rw [hder]
  exact h



theorem norm_boundaryCoordinate {p : ℂ} (hp : ‖p‖ = 1) (z : ℂ) :
    ‖boundaryCoordinate p z‖ = Real.exp (-z.im) := by
  simp [boundaryCoordinate, hp, norm_exp, mul_re]



theorem deriv_boundaryCoordinate_ne_zero {p : ℂ} (hp : p ≠ 0) (z : ℂ) :
    deriv (boundaryCoordinate p) z ≠ 0 := by
  rw [(hasDerivAt_boundaryCoordinate p z).deriv]
  exact mul_ne_zero I_ne_zero (mul_ne_zero hp (exp_ne_zero _))



theorem boundaryCoordinate_disk_iff {p : ℂ} (hp : ‖p‖ = 1) (z : ℂ) :
    ‖boundaryCoordinate p z‖ ≤ 1 ↔ 0 ≤ z.im := by
  rw [norm_boundaryCoordinate hp, Real.exp_le_one_iff]
  exact neg_nonpos



theorem boundaryCoordinate_interior_iff {p : ℂ} (hp : ‖p‖ = 1) (z : ℂ) :
    ‖boundaryCoordinate p z‖ < 1 ↔ 0 < z.im := by
  rw [norm_boundaryCoordinate hp, Real.exp_lt_one_iff]
  exact neg_neg_iff_pos



theorem contDiffAt_boundaryInverse {p : ℂ} (hp : p ≠ 0) :
    ContDiffAt ℂ ∞ (boundaryInverse p) p := by
  have hlog : ContDiffAt ℂ ∞ log (p / p) := by
    simpa only [div_self hp] using (contDiffAt_log one_mem_slitPlane : ContDiffAt ℂ ∞ log 1)
  have hdiv : ContDiffAt ℂ ∞ (fun w : ℂ => w / p) p := contDiffAt_id.div_const p
  exact contDiffAt_const.mul (hlog.comp (f := fun w : ℂ => w / p) p hdiv)



theorem boundaryCoordinate_inverse {p w : ℂ} (hp : p ≠ 0) (hw : w ≠ 0) :
    boundaryCoordinate p (boundaryInverse p w) = w := by
  have hI (z : ℂ) : I * (-I * z) = z := by
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  rw [boundaryCoordinate, boundaryInverse, hI, exp_log (div_ne_zero hw hp)]
  exact mul_div_cancel₀ w hp



theorem boundaryInverse_coordinate_eventually {p : ℂ} (hp : p ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), boundaryInverse p (boundaryCoordinate p z) = z := by
  have hstrip : ∀ᶠ z in 𝓝 (0 : ℂ), -Real.pi < z.re ∧ z.re < Real.pi :=
    (continuous_re.continuousAt.eventually
      (Ioo_mem_nhds (by simpa using neg_lt_zero.mpr Real.pi_pos) Real.pi_pos))
  filter_upwards [hstrip] with z hz
  have heq : p * exp (I * z) / p = exp (I * z) := by field_simp
  rw [boundaryInverse, boundaryCoordinate, heq,
    log_exp (by simpa using hz.1) (by simpa using hz.2.le)]
  simp [← mul_assoc]



theorem boundaryInverse_im_nonneg {p w : ℂ} (hp : ‖p‖ = 1) (hw : ‖w‖ ≤ 1) :
    0 ≤ (boundaryInverse p w).im := by
  simp only [boundaryInverse, mul_im, neg_re, I_re, neg_zero, zero_mul,
    neg_im, I_im, neg_one_mul, zero_add, log_re, norm_div, hp, div_one]
  exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hw)




theorem boundaryInverse_tendstoWithin {p : ℂ} (hp : ‖p‖ = 1) :
    Tendsto (boundaryInverse p) (𝓝[closedBall (0 : ℂ) 1] p)
      (𝓝[{z : ℂ | 0 ≤ z.im}] 0) := by
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := (contDiffAt_boundaryInverse hp0).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := closedBall (0 : ℂ) 1))
    simpa only [boundaryInverse, div_self hp0, log_one, mul_zero] using h
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact boundaryInverse_im_nonneg hp (mem_closedBall_zero_iff.mp hw)

end PoincareConjecture.M65StrictTrace
