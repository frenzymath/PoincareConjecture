import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

def modelS (κ t : ℝ) : ℝ :=
  if κ = 0 then t else Real.sinh (Real.sqrt κ * t) / Real.sqrt κ

def euclideanUnitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

def modelVolume (n : ℕ) (κ r : ℝ) : ℝ :=
  n * euclideanUnitBallVolume n *
    ∫ t in (0 : ℝ)..r, modelS κ t ^ (n - 1)

@[simp] theorem modelS_zero_curvature (t : ℝ) : modelS 0 t = t := by
  simp [modelS]

@[simp] theorem modelS_zero (κ : ℝ) : modelS κ 0 = 0 := by
  simp [modelS]

theorem continuous_modelS (κ : ℝ) : Continuous (modelS κ) := by
  change Continuous (fun t => modelS κ t)
  by_cases hκ : κ = 0
  · simp only [modelS, hκ]
    exact continuous_id
  · simp only [modelS, if_neg hκ]
    exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div_const _

theorem modelS_nonneg {κ t : ℝ} (_hκ : 0 ≤ κ) (ht : 0 ≤ t) :
    0 ≤ modelS κ t := by
  by_cases hκ0 : κ = 0
  · simpa [hκ0] using ht
  · simp only [modelS, if_neg hκ0]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg (Real.sqrt_nonneg κ) ht))
      (Real.sqrt_nonneg κ)

theorem modelS_pos {κ t : ℝ} (hκ : 0 ≤ κ) (ht : 0 < t) :
    0 < modelS κ t := by
  by_cases hκ0 : κ = 0
  · simpa [hκ0] using ht
  · have hsqrt : 0 < Real.sqrt κ := Real.sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hκ0))
    simpa only [modelS, if_neg hκ0] using
      div_pos (Real.sinh_pos_iff.mpr (mul_pos hsqrt ht)) hsqrt

theorem euclideanUnitBallVolume_pos (n : ℕ) : 0 < euclideanUnitBallVolume n := by
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne'
    measure_ball_lt_top.ne

theorem euclideanUnitBallVolume_nonneg (n : ℕ) : 0 ≤ euclideanUnitBallVolume n :=
  (euclideanUnitBallVolume_pos n).le

theorem intervalIntegrable_modelS_pow (n : ℕ) (κ a b : ℝ) :
    IntervalIntegrable (fun t => modelS κ t ^ (n - 1)) volume a b :=
  ((continuous_modelS κ).pow (n - 1)).intervalIntegrable a b

@[simp] theorem modelVolume_zero_radius (n : ℕ) (κ : ℝ) : modelVolume n κ 0 = 0 := by
  simp [modelVolume]

theorem modelVolume_nonneg (n : ℕ) {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r) :
    0 ≤ modelVolume n κ r := by
  apply mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_nonneg n))
  exact intervalIntegral.integral_nonneg hr fun t ht => pow_nonneg (modelS_nonneg hκ ht.1) _

theorem modelVolume_pos {n : ℕ} (hn : 1 ≤ n) {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r) :
    0 < modelVolume n κ r := by
  apply mul_pos (mul_pos (Nat.cast_pos.mpr hn) (euclideanUnitBallVolume_pos n))
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_modelS_pow n κ 0 r)
    (fun t ht => pow_pos (modelS_pos hκ ht.1) _) hr

theorem continuous_modelVolume (n : ℕ) (κ : ℝ) : Continuous (modelVolume n κ) := by
  apply continuous_const.mul
  exact (intervalIntegral.differentiable_integral_of_continuous
    ((continuous_modelS κ).pow (n - 1))).continuous

theorem modelVolume_zero_curvature {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    modelVolume n 0 r = euclideanUnitBallVolume n * r ^ n := by
  simp only [modelVolume, modelS_zero_curvature, integral_pow, Nat.sub_add_cancel hn,
    zero_pow (by omega : n ≠ 0), sub_zero]
  rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

theorem hasDerivAt_modelS_zero {κ : ℝ} (hκ : 0 ≤ κ) :
    HasDerivAt (modelS κ) 1 0 := by
  by_cases hκ0 : κ = 0
  · subst κ
    change HasDerivAt (fun t => modelS 0 t) 1 0
    simp only [modelS_zero_curvature]
    exact hasDerivAt_id 0
  · have hsqrt : Real.sqrt κ ≠ 0 :=
      (Real.sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hκ0))).ne'
    change HasDerivAt (fun t => modelS κ t) 1 0
    simp only [modelS, if_neg hκ0]
    simpa [hsqrt] using (((hasDerivAt_id (0 : ℝ)).const_mul (Real.sqrt κ)).sinh).div_const
      (Real.sqrt κ)

theorem tendsto_modelS_div {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun t => modelS κ t / t) (𝓝[>] 0) (𝓝 1) := by
  simpa only [zero_add, modelS_zero, sub_zero, smul_eq_mul, ← div_eq_inv_mul] using
    (hasDerivAt_modelS_zero hκ).tendsto_slope_zero_right

theorem hasDerivAt_modelVolume (n : ℕ) (κ r : ℝ) :
    HasDerivAt (modelVolume n κ)
      (n * euclideanUnitBallVolume n * modelS κ r ^ (n - 1)) r := by
  exact (intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_modelS_pow n κ 0 r)
    ((continuous_modelS κ).pow (n - 1)).aestronglyMeasurable.stronglyMeasurableAtFilter
    ((continuous_modelS κ).pow (n - 1)).continuousAt).const_mul _

theorem tendsto_modelVolume_div_euclidean {n : ℕ} (hn : 1 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun r => modelVolume n κ r / (euclideanUnitBallVolume n * r ^ n))
      (𝓝[>] 0) (𝓝 1) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hv0 := (euclideanUnitBallVolume_pos n).ne'
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := fun r => n * euclideanUnitBallVolume n * modelS κ r ^ (n - 1))
    (g' := fun r => n * euclideanUnitBallVolume n * r ^ (n - 1))
  · exact Filter.Eventually.of_forall (hasDerivAt_modelVolume n κ)
  · filter_upwards with r
    simpa only [mul_left_comm, mul_assoc] using
      (hasDerivAt_pow n r).const_mul (euclideanUnitBallVolume n)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_ne_zero (mul_ne_zero hn0 hv0) (pow_ne_zero _ (ne_of_gt hr))
  · simpa only [modelVolume_zero_radius] using
      ((continuous_modelVolume n κ).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · have h : Continuous (fun r : ℝ => euclideanUnitBallVolume n * r ^ n) :=
      continuous_const.mul (continuous_id.pow n)
    simpa only [zero_pow (by omega : n ≠ 0), mul_zero] using
      (h.tendsto 0).mono_left nhdsWithin_le_nhds
  · simpa only [mul_div_mul_left _ _ (mul_ne_zero hn0 hv0), ← div_pow, one_pow] using
      (tendsto_modelS_div hκ).pow (n - 1)

end PoincareConjecture.RiemannianMetric
