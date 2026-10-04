import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Analysis.Parabolic.Quasilinear.Euclidean.Mollification
import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.MetricBounds
import PoincareLib.Geometry.Riemannian.LoopSpace.Width
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Literal two-dimensional scaled averaging kernels

A fixed genuine normalized smooth bump is scaled using the actual
Euclidean dilation. Its support, unit mass, and L2 scaling are proved
from that formula. Morrey ICM 1950, printed pp. 183-185, for
Morgan--Tian Lemma 19.2, pp. 437-438; M65 derivation 38, actual Holder
representative from the weak fields.
-/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT.M65Interior

/-- The actual closed-M03 normalized bump at radius one, fixed before
all centers and scales. Morrey ICM pp. 183-185; derivation 38. -/
noncomputable abbrev averagingProfile : LoopPlane → ℝ :=
  EuclideanMollificationNative.mollifier (by norm_num : (0 : ℝ) < 1)

/-- The literal positive-radius kernel uses the actual two-dimensional
normalization and one fixed smooth unit-mass profile. Morrey ICM
pp. 183-185; MT Lemma 19.2, pp. 437-438; derivation 38. -/
noncomputable def averagingKernel (r : ℝ) (z : LoopPlane) : ℝ :=
  r⁻¹ ^ 2 * averagingProfile (r⁻¹ • z)

/-- The actual scaled kernel is nonnegative. Morrey ICM pp. 183-185;
derivation 38, scaled averages. -/
theorem averagingKernel_nonneg (r : ℝ) (z : LoopPlane) : 0 ≤ averagingKernel r z := by
  exact mul_nonneg (sq_nonneg _) (EuclideanMollificationNative.mollifier_nonneg _ _)

/-- Every fixed-radius kernel is genuinely smooth. Morrey ICM
pp. 183-185; derivation 38, scaled averages. -/
theorem averagingKernel_contDiff (r : ℝ) : ContDiff ℝ ∞ (averagingKernel r) := by
  exact contDiff_const.mul ((EuclideanMollificationNative.mollifier_contDiff _).comp
    (by fun_prop))

/-- The actual kernel has support in the literal radius-r disk.
Morrey ICM pp. 183-185; derivation 38, scaled averages. -/
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

/-- The literal kernel has genuine compact support. Morrey ICM
pp. 183-185; derivation 38, scaled averages. -/
theorem averagingKernel_hasCompactSupport {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (averagingKernel r) :=
  (isCompact_closedBall (0 : LoopPlane) r).of_isClosed_subset isClosed_closure
    (closure_minimal (averagingKernel_support hr) isClosed_closedBall)

/-- Actual Haar scaling proves the kernel has unit integral.
Morrey ICM pp. 183-185; derivation 38, scaled averages. -/
theorem averagingKernel_integral {r : ℝ} (hr : 0 < r) :
    (∫ z, averagingKernel r z) = 1 := by
  have hscale : (∫ z : LoopPlane, averagingProfile (r⁻¹ • z)) = (r⁻¹ ^ 2)⁻¹ := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
      EuclideanMollificationNative.mollifier_integral, mul_one] using
      (Measure.integral_comp_smul_of_nonneg volume averagingProfile r⁻¹
        (hR := inv_nonneg.mpr hr.le))
  simp only [averagingKernel, integral_const_mul, hscale]
  exact mul_inv_cancel₀ (pow_ne_zero 2 (inv_ne_zero hr.ne'))

/-- The actual squared-kernel integral has its true inverse-square
scaling. Morrey ICM pp. 183-185; derivation 38, scaled averages. -/
theorem averagingKernel_integral_sq {r : ℝ} (hr : 0 < r) :
    (∫ z, averagingKernel r z ^ 2) = r⁻¹ ^ 2 * ∫ z, averagingProfile z ^ 2 := by
  have hscale : (∫ z : LoopPlane, averagingProfile (r⁻¹ • z) ^ 2) =
      (r⁻¹ ^ 2)⁻¹ * ∫ z, averagingProfile z ^ 2 := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
      (Measure.integral_comp_smul_of_nonneg volume (fun z => averagingProfile z ^ 2) r⁻¹
        (hR := inv_nonneg.mpr hr.le))
  simp only [averagingKernel, mul_pow, integral_const_mul, hscale]
  field_simp

/-- The actual joint kernel is smooth at every nonzero radius.
Morrey ICM pp. 183-185; derivation 38, scaled averages. -/
theorem averagingKernel_joint_contDiffAt {p : ℝ × LoopPlane} (hp : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane => averagingKernel q.1 q.2) p := by
  have hInv : ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane => q.1⁻¹) p :=
    contDiffAt_fst.inv hp
  exact (hInv.pow 2).mul ((EuclideanMollificationNative.mollifier_contDiff _).contDiffAt.comp p
    (hInv.smul contDiffAt_snd))

end PoincareMT.M65Interior
