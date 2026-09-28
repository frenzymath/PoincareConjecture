import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.Convolution
import Mathlib.Analysis.Convex.Deriv








set_option autoImplicit false

open Set MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff NNReal

namespace Poincare

private noncomputable def absoluteValueBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ℝ) :=
  ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩


noncomputable def regularizedAbs (δ : ℝ) (hδ : 0 < δ) : ℝ → ℝ :=
  (absoluteValueBump δ hδ).normed volume ⋆[lsmul ℝ ℝ, volume] (fun t : ℝ => |t|)

private theorem abs_lipschitz : LipschitzWith 1 (fun t : ℝ => |t|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y

theorem contDiff_regularizedAbs (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (regularizedAbs δ hδ) :=
  (absoluteValueBump δ hδ).hasCompactSupport_normed.contDiff_convolution_left _
    (absoluteValueBump δ hδ).contDiff_normed abs_lipschitz.continuous.locallyIntegrable

theorem lipschitzWith_regularizedAbs (δ : ℝ) (hδ : 0 < δ) :
    LipschitzWith 1 (regularizedAbs δ hδ) :=
  lipschitzWith_normed_convolution volume abs_lipschitz (absoluteValueBump δ hδ)

private theorem integral_bump_mul_id (φ : ContDiffBump (0 : ℝ)) :
    ∫ t : ℝ, φ.normed volume t * t = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => φ.normed volume t * t) volume
  simp only [φ.normed_neg, mul_neg, integral_neg] at h
  linarith

private theorem integrable_bump_mul_id (φ : ContDiffBump (0 : ℝ)) :
    Integrable (fun t : ℝ => φ.normed volume t * t) :=
  ((φ.contDiff_normed (n := 0)).continuous.mul continuous_id).integrable_of_hasCompactSupport
    φ.hasCompactSupport_normed.mul_right

private theorem integrable_bump_mul_abs_sub (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    Integrable (fun t : ℝ => φ.normed volume t * |x - t|) := by
  exact φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) (φ.contDiff_normed (n := 0)).continuous.locallyIntegrable
    abs_lipschitz.continuous x

theorem regularizedAbs_neg (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    regularizedAbs δ hδ (-x) = regularizedAbs δ hδ x := by
  let φ := absoluteValueBump δ hδ
  change (∫ t : ℝ, φ.normed volume t * |-x - t|) =
    ∫ t : ℝ, φ.normed volume t * |x - t|
  rw [← integral_neg_eq_self (fun t : ℝ => φ.normed volume t * |-x - t|) volume]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [φ.normed_neg]
    congr 1
    rw [show -x - -t = -(x - t) by ring, abs_neg]

theorem regularizedAbs_eq_abs (δ : ℝ) (hδ : 0 < δ) {x : ℝ}
    (hx : δ ≤ |x|) : regularizedAbs δ hδ x = |x| := by
  have hpos (x : ℝ) (hx : δ ≤ x) : regularizedAbs δ hδ x = x := by
    let φ := absoluteValueBump δ hδ
    change (∫ t : ℝ, φ.normed volume t * |x - t|) = x
    have heq : (fun t : ℝ => φ.normed volume t * |x - t|) =
        fun t : ℝ => φ.normed volume t * x - φ.normed volume t * t := by
      funext t
      by_cases ht : φ.normed volume t = 0
      · simp [ht]
      · have ht' : |t| < δ := by
          have hmem : t ∈ Function.support (φ.normed volume) := ht
          rw [φ.support_normed_eq] at hmem
          simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, φ, absoluteValueBump] using hmem
        rw [abs_of_nonneg (by linarith [le_abs_self t])]
        ring
    rw [heq, integral_sub (φ.integrable_normed.mul_const _) (integrable_bump_mul_id φ),
      integral_mul_const, φ.integral_normed, integral_bump_mul_id, one_mul, sub_zero]
  rcases le_total 0 x with hx0 | hx0
  · simpa only [abs_of_nonneg hx0] using hpos x (by simpa [abs_of_nonneg hx0] using hx)
  · rw [← regularizedAbs_neg δ hδ x, hpos (-x) (by simpa [abs_of_nonpos hx0] using hx),
      abs_of_nonpos hx0]

theorem abs_le_regularizedAbs (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    |x| ≤ regularizedAbs δ hδ x := by
  let φ := absoluteValueBump δ hδ
  have heq : (∫ t : ℝ, φ.normed volume t * (x - t)) = x := by
    simp_rw [mul_sub]
    rw [integral_sub (φ.integrable_normed.mul_const _) (integrable_bump_mul_id φ),
      integral_mul_const, φ.integral_normed, integral_bump_mul_id, one_mul, sub_zero]
  calc
    |x| = |∫ t : ℝ, φ.normed volume t * (x - t)| := congrArg abs heq.symm
    _ ≤
        ∫ t : ℝ, |φ.normed volume t * (x - t)| := abs_integral_le_integral_abs
    _ = regularizedAbs δ hδ x := by
      simp only [abs_mul, abs_of_nonneg (φ.nonneg_normed _)]
      rfl

theorem regularizedAbs_le_abs_add (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    regularizedAbs δ hδ x ≤ |x| + δ := by
  have h := dist_normed_convolution_le_radius volume abs_lipschitz
    (absoluteValueBump δ hδ) x
  change abs (regularizedAbs δ hδ x - abs x) ≤ (1 : ℝ) * δ at h
  linarith [le_abs_self (regularizedAbs δ hδ x - |x|)]

theorem convexOn_regularizedAbs (δ : ℝ) (hδ : 0 < δ) :
    ConvexOn ℝ univ (regularizedAbs δ hδ) := by
  let φ := absoluteValueBump δ hδ
  change ConvexOn ℝ univ (fun x => ∫ t : ℝ, φ.normed volume t * |x - t|)
  apply integral_convexOn_of_integrand_ae convex_univ
  · apply Filter.Eventually.of_forall
    intro t
    have hc : ConvexOn ℝ (univ : Set ℝ) (fun x => |x - t|) := by
      simpa only [Real.norm_eq_abs, preimage_univ, Function.comp_def, sub_eq_add_neg] using
        (convexOn_norm (E := ℝ) convex_univ).translate_left (-t)
    simpa only [smul_eq_mul] using hc.smul (φ.nonneg_normed t)
  · exact fun x _ => integrable_bump_mul_abs_sub φ x

theorem abs_deriv_regularizedAbs_le_one (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    |deriv (regularizedAbs δ hδ) x| ≤ 1 := by
  simpa only [Real.norm_eq_abs, NNReal.coe_one] using
    norm_deriv_le_of_lipschitz (x₀ := x) (lipschitzWith_regularizedAbs δ hδ)

theorem deriv2_regularizedAbs_nonneg (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    0 ≤ deriv (deriv (regularizedAbs δ hδ)) x := by
  have hm := (convexOn_regularizedAbs δ hδ).monotoneOn_deriv
    (fun x _ => (contDiff_regularizedAbs δ hδ).differentiable (by simp) x)
  exact (show Monotone (deriv (regularizedAbs δ hδ)) from fun x y hxy =>
    hm (mem_univ x) (mem_univ y) hxy).deriv_nonneg

end Poincare
