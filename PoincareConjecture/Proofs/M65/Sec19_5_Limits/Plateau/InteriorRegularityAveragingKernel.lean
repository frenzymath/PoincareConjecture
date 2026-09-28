import PoincareConjecture.Proofs.M03.Existence.EuclideanMollificationNative
import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations











set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Interior



noncomputable abbrev averagingProfile : LoopPlane → ℝ :=
  EuclideanMollificationNative.mollifier (by norm_num : (0 : ℝ) < 1)




noncomputable def averagingKernel (r : ℝ) (z : LoopPlane) : ℝ :=
  r⁻¹ ^ 2 * averagingProfile (r⁻¹ • z)



theorem averagingKernel_nonneg (r : ℝ) (z : LoopPlane) : 0 ≤ averagingKernel r z := by
  exact mul_nonneg (sq_nonneg _) (EuclideanMollificationNative.mollifier_nonneg _ _)



theorem averagingKernel_contDiff (r : ℝ) : ContDiff ℝ ∞ (averagingKernel r) := by
  exact contDiff_const.mul ((EuclideanMollificationNative.mollifier_contDiff _).comp
    (by fun_prop))



theorem averagingKernel_support {r : ℝ} (hr : 0 < r) :
    Function.support (averagingKernel r) ⊆ closedBall 0 r := by
  intro z hz
  have hρ : averagingProfile (r⁻¹ • z) ≠ 0 := (mul_ne_zero_iff.mp hz).2
  have h := EuclideanMollificationNative.norm_le_of_mollifier_ne_zero
    (by norm_num : (0 : ℝ) < 1) hρ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at h
  have hh := mul_le_mul_of_nonneg_left h hr.le
  rw [mem_closedBall_zero_iff]
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_one] using hh



theorem averagingKernel_hasCompactSupport {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (averagingKernel r) :=
  (isCompact_closedBall (0 : LoopPlane) r).of_isClosed_subset isClosed_closure
    (closure_minimal (averagingKernel_support hr) isClosed_closedBall)



theorem averagingKernel_integral {r : ℝ} (hr : 0 < r) :
    (∫ z, averagingKernel r z) = 1 := by
  have hscale : (∫ z : LoopPlane, averagingProfile (r⁻¹ • z)) = (r⁻¹ ^ 2)⁻¹ := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
      EuclideanMollificationNative.mollifier_integral, mul_one] using
      (Measure.integral_comp_smul_of_nonneg volume averagingProfile r⁻¹
        (hR := inv_nonneg.mpr hr.le))
  simp only [averagingKernel, integral_const_mul, hscale]
  exact mul_inv_cancel₀ (pow_ne_zero 2 (inv_ne_zero hr.ne'))



theorem averagingKernel_integral_sq {r : ℝ} (hr : 0 < r) :
    (∫ z, averagingKernel r z ^ 2) = r⁻¹ ^ 2 * ∫ z, averagingProfile z ^ 2 := by
  have hscale : (∫ z : LoopPlane, averagingProfile (r⁻¹ • z) ^ 2) =
      (r⁻¹ ^ 2)⁻¹ * ∫ z, averagingProfile z ^ 2 := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
      (Measure.integral_comp_smul_of_nonneg volume (fun z => averagingProfile z ^ 2) r⁻¹
        (hR := inv_nonneg.mpr hr.le))
  simp only [averagingKernel, mul_pow, integral_const_mul, hscale]
  field_simp



theorem averagingKernel_joint_contDiffAt {p : ℝ × LoopPlane} (hp : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane => averagingKernel q.1 q.2) p := by
  have hInv : ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane => q.1⁻¹) p :=
    contDiffAt_fst.inv hp
  exact (hInv.pow 2).mul ((EuclideanMollificationNative.mollifier_contDiff _).contDiffAt.comp p
    (hInv.smul contDiffAt_snd))

end PoincareConjecture.M65Interior
