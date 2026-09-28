import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TimeDependentSpectralResponse
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M63.TimeDependentSpectralResidual

open SpectralHeatNative

variable {iota : Type*} [Countable iota] [MeasurableSpace (State iota)]
  {lambda : iota → NNReal} {T0 T : ℝ}
  (N : TimeDependentSpectralResidual lambda T0)

def restrict (hT : T ≤ T0) : TimeDependentSpectralResidual lambda T where
  toFun := N.toFun
  measurable := N.measurable
  zero_memLp := N.zero_memLp.mono_measure
    (Measure.restrict_mono (Ioc_subset_Ioc le_rfl hT) le_rfl)
  perturbationConstant := N.perturbationConstant
  principalConstant := N.principalConstant
  lowerConstant := N.lowerConstant
  mixed := ae_mono (Measure.restrict_mono (Ioc_subset_Ioc le_rfl hT) le_rfl) N.mixed

theorem exists_positive_interval (hT0 : 0 < T0)
    (heps : (N.perturbationConstant : ℝ) < 1 / 2) :
    ∃ r : ℝ, 0 < r ∧ ∃ T : ℝ, 0 < T ∧ ∃ hTT0 : T ≤ T0,
      T ≤ 1 ∧
      2 * N.perturbationConstant + 8 * N.principalConstant * r +
        2 * N.lowerConstant * Real.sqrt T < 1 ∧
      ‖(N.restrict hTT0).zero_memLp.toLp (fun t => N.toFun t 0)‖ ≤
        (1 - (2 * N.perturbationConstant + 8 * N.principalConstant * r +
          2 * N.lowerConstant * Real.sqrt T)) * r := by
  let d : ℝ := 1 - 2 * N.perturbationConstant
  have hd : 0 < d := by dsimp [d]; linarith
  let r : ℝ := d / (32 * (N.principalConstant + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrEq : r * (32 * (N.principalConstant + 1)) = d :=
    div_mul_cancel₀ d (by positivity)
  have hprincipal : 8 * N.principalConstant * r ≤ d / 4 := by nlinarith
  let q : ℝ := d / (8 * (N.lowerConstant + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqEq : q * (8 * (N.lowerConstant + 1)) = d :=
    div_mul_cancel₀ d (by positivity)
  have hlower : 2 * N.lowerConstant * q ≤ d / 4 := by nlinarith
  let f : ℝ → ℝ := fun t => ‖N.toFun t 0‖ ^ 2
  have hf : IntervalIntegrable f volume 0 T0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le).mpr
      ((memLp_two_iff_integrable_sq_norm N.zero_memLp.aestronglyMeasurable).mp
        N.zero_memLp)
  have hcont : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, f s) (Icc 0 T0) := by
    simpa only [uIcc_of_le hT0.le] using
      intervalIntegral.continuousOn_primitive_interval' hf (left_mem_uIcc : 0 ∈ uIcc 0 T0)
  have hmargin : 0 < d * r / 2 := by positivity
  obtain ⟨eta, heta, hnear⟩ := Metric.continuousWithinAt_iff.mp
    (hcont 0 ⟨le_rfl, hT0.le⟩) ((d * r / 2) ^ 2) (sq_pos_of_pos hmargin)
  let t : ℝ := min T0 (min 1 (min (q ^ 2) (eta / 2)))
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min hT0 (lt_min zero_lt_one (lt_min (sq_pos_of_pos hq) (by positivity)))
  have htT0 : t ≤ T0 := min_le_left _ _
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have htq : t ≤ q ^ 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hteta : t < eta := by
    have hle : t ≤ eta / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hsqrt : Real.sqrt t ≤ q := by
    nlinarith [Real.sq_sqrt ht.le, Real.sqrt_nonneg t]
  have htrace : 2 * N.lowerConstant * Real.sqrt t ≤ d / 4 :=
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)).trans hlower
  have hkappa : 2 * N.perturbationConstant + 8 * N.principalConstant * r +
      2 * N.lowerConstant * Real.sqrt t ≤ 1 - d / 2 := by
    dsimp [d] at *
    linarith
  have hintegral : (∫ s in (0 : ℝ)..t, f s) < (d * r / 2) ^ 2 := by
    have hdist := hnear ⟨ht.le, htT0⟩
      (by simpa [Real.dist_eq, abs_of_nonneg ht.le] using hteta)
    simp only [intervalIntegral.integral_same, dist_zero_right, Real.norm_eq_abs] at hdist
    exact (le_abs_self (∫ s in (0 : ℝ)..t, f s)).trans_lt hdist
  have hnormsq : ‖(N.restrict htT0).zero_memLp.toLp (fun s => N.toFun s 0)‖ ^ 2 =
      ∫ s in (0 : ℝ)..t, f s := by
    calc
      _ = ∫ s, ‖(N.restrict htT0).toFun s 0‖ ^ 2 ∂timeMeasure t :=
        norm_toLp_sq (N.restrict htT0).zero_memLp
      _ = _ := by rw [intervalIntegral.integral_of_le ht.le]; rfl
  have hnorm : ‖(N.restrict htT0).zero_memLp.toLp (fun s => N.toFun s 0)‖ ≤
      d * r / 2 := by
    have hsq := hnormsq.trans_lt hintegral
    nlinarith [norm_nonneg ((N.restrict htT0).zero_memLp.toLp (fun s => N.toFun s 0))]
  refine ⟨r, hr, t, ht, htT0, ht1, by linarith, hnorm.trans ?_⟩
  nlinarith

end PoincareConjecture.M63.TimeDependentSpectralResidual
