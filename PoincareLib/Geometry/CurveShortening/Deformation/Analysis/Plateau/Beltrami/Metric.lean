import PoincareLib.Geometry.CurveShortening.Deformation.Analysis.Plateau.Beltrami.Disk
import Mathlib.Analysis.Matrix.PosDef

/-!
# The Beltrami coefficient of the actual positive Gram metric

The explicit two-dimensional coefficient is strictly subunit and its
real-linear coefficient form recovers the original quadratic metric.
This identity connects the actual Beltrami coordinates to the energy
change of variables. Source: derivation 30, Fitzi--Wenger Theorem 4.1,
for Morrey's epsilon-conformality and MT Lemma 19.2, printed p. 438.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Topology ContDiff ComplexConjugate

namespace Complex

/-- The literal Beltrami coefficient of a real two-by-two positive
metric. Source: derivation 30, the disk isothermal coordinate formula. -/
def positiveMetricBeltrami (K : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((K 0 0 - K 1 1 : ℝ) + (2 * K 0 1 : ℝ) * I) /
    (K 0 0 + K 1 1 + 2 * Real.sqrt K.det : ℝ)

private theorem positive_metric_data (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) :
    0 < K 0 0 + K 1 1 + 2 * Real.sqrt K.det ∧
      (Real.sqrt K.det) ^ 2 = K 0 0 * K 1 1 - (K 0 1) ^ 2 := by
  have hs : K 1 0 = K 0 1 := hK.isHermitian.apply 0 1
  have hdet : K.det = K 0 0 * K 1 1 - (K 0 1) ^ 2 := by
    rw [Matrix.det_fin_two, hs]
    ring
  refine ⟨?_, ?_⟩
  · linarith [hK.diag_pos (i := 0), hK.diag_pos (i := 1), Real.sqrt_nonneg K.det]
  · rw [Real.sq_sqrt hK.det_pos.le, hdet]

/-- The actual coefficient of a positive real metric has modulus less
than one, including isotropic metrics where it is zero. Source:
derivation 30, the genuine smooth Beltrami input for MT Lemma 19.2. -/
theorem norm_positiveMetricBeltrami_lt_one
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) :
    ‖positiveMetricBeltrami K‖ < 1 := by
  let d := K 0 0 + K 1 1 + 2 * Real.sqrt K.det
  let N : ℂ := (K 0 0 - K 1 1 : ℝ) + (2 * K 0 1 : ℝ) * I
  have hd : 0 < d := (positive_metric_data K hK).1
  have hNsq : ‖N‖ ^ 2 = (K 0 0 - K 1 1) ^ 2 + 4 * (K 0 1) ^ 2 := by
    simp only [N, Complex.sq_norm, normSq_apply, add_re, add_im,
      ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
    ring
  have htrace : 0 < K 0 0 + K 1 1 := add_pos hK.diag_pos hK.diag_pos
  have hsqrt : 0 < Real.sqrt K.det := Real.sqrt_pos.mpr hK.det_pos
  have hnorm : ‖N‖ < d := by
    have hs := (positive_metric_data K hK).2
    dsimp only [d]
    nlinarith [norm_nonneg N, Real.sqrt_nonneg K.det]
  change ‖N / (d : ℂ)‖ < 1
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hd]
  exact (div_lt_one hd).mpr hnorm

/-- The standard Beltrami real-linear form exactly represents the
supplied positive metric, with its actual determinant and entries.
Source: derivation 30, the isothermal energy calculation for MT 19.2. -/
theorem positiveMetricBeltrami_quadratic
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) (v : ℂ) :
    K 0 0 * v.re ^ 2 + 2 * K 0 1 * v.re * v.im + K 1 1 * v.im ^ 2 =
      ((K 0 0 + K 1 1 + 2 * Real.sqrt K.det) / 4) *
        ‖v + positiveMetricBeltrami K * conj v‖ ^ 2 := by
  let d := K 0 0 + K 1 1 + 2 * Real.sqrt K.det
  let p := (K 0 0 - K 1 1) / d
  let q := (2 * K 0 1) / d
  have hd : d ≠ 0 := (positive_metric_data K hK).1.ne'
  have hs := (positive_metric_data K hK).2
  have h0 : (d / 4) * ((1 + p) ^ 2 + q ^ 2) = K 0 0 := by
    apply mul_right_cancel₀ hd
    calc
      _ = ((d + (K 0 0 - K 1 1)) ^ 2 + (2 * K 0 1) ^ 2) / 4 := by
        dsimp only [p, q]
        field_simp
      _ = K 0 0 * d := by dsimp only [d]; nlinarith
  have h1 : (d / 4) * ((1 - p) ^ 2 + q ^ 2) = K 1 1 := by
    apply mul_right_cancel₀ hd
    calc
      _ = ((d - (K 0 0 - K 1 1)) ^ 2 + (2 * K 0 1) ^ 2) / 4 := by
        dsimp only [p, q]
        field_simp
      _ = K 1 1 * d := by dsimp only [d]; nlinarith
  have h01 : (d / 4) * (2 * q) = K 0 1 := by dsimp only [q]; field_simp; ring
  have hp : (positiveMetricBeltrami K).re = p := by
    simp only [positiveMetricBeltrami, div_ofReal_re, add_re, ofReal_re,
      mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rfl
  have hq : (positiveMetricBeltrami K).im = q := by
    simp only [positiveMetricBeltrami, div_ofReal_im, add_im, ofReal_im,
      mul_im, ofReal_re, I_re, I_im, mul_one, zero_mul, add_zero, zero_add]
    rfl
  simp only [Complex.sq_norm, normSq_apply, add_re, add_im,
    mul_re, mul_im, conj_re, conj_im, hp, hq]
  change _ = (d / 4) * _
  linear_combination -v.re ^ 2 * h0 - v.im ^ 2 * h1 - (2 * v.re * v.im) * h01

end Complex
