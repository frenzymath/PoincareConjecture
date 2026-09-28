import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PositiveCenteredInterval

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M63.CenteredSpectralResidual

open SpectralHeatNative

variable {iota : Type*} [Countable iota]
  [MeasurableSpace (State iota)]
  {lambda : iota → NNReal} {w : State iota} {T0 T : ℝ}

theorem exists_strict_positive_interval (N : CenteredSpectralResidual lambda w T0)
    (hT0 : 0 < T0) (heps : (N.perturbationConstant : ℝ) < 1 / 2)
    {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r0 ∧ ∃ T : ℝ, ∃ hT : 0 < T, ∃ hTT0 : T ≤ T0,
      T ≤ 1 ∧
      let P := (initialHeatHigh_memLp_energy lambda w hT.le).1.toLp (initialHeatHigh lambda w)
      2 * N.perturbationConstant + 8 * N.principalConstant * r +
        2 * N.principalConstant * ‖P‖ + 2 * N.lowerConstant * Real.sqrt T < 1 ∧
      ‖(N.restrict hTT0).zero_memLp.toLp (fun t => N.toFun t 0)‖ <
        (1 - (2 * N.perturbationConstant + 8 * N.principalConstant * r +
          2 * N.principalConstant * ‖P‖ + 2 * N.lowerConstant * Real.sqrt T)) * r / 2 := by
  let d : ℝ := 1 - 2 * N.perturbationConstant
  have hd : 0 < d := by dsimp [d]; linarith only [heps]
  let r : ℝ := min r0 (d / (32 * (N.principalConstant + 1)))
  have hr : 0 < r := by dsimp [r]; exact lt_min hr0 (by positivity)
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hrbound : r * (32 * (N.principalConstant + 1)) ≤ d :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hprincipal : 8 * N.principalConstant * r ≤ d / 4 := by
    nlinarith only [hrbound, hr.le]
  let q : ℝ := d / (16 * (N.lowerConstant + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqEq : q * (16 * (N.lowerConstant + 1)) = d :=
    div_mul_cancel₀ d (by positivity)
  have hlower : 2 * N.lowerConstant * q ≤ d / 8 := by
    nlinarith only [hqEq, hq.le]
  let a : ℝ := d / (16 * (N.principalConstant + 1))
  let b : ℝ := d * r / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  let Q : ℝ → ℝ := fun t => ‖initialHeatHigh lambda w t‖ ^ 2 + ‖N.toFun t 0‖ ^ 2
  have hP0 := (initialHeatHigh_memLp_energy lambda w hT0.le).1
  have hQ : IntervalIntegrable Q volume 0 T0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le).mpr
      (((memLp_two_iff_integrable_sq_norm hP0.aestronglyMeasurable).mp hP0).add
        ((memLp_two_iff_integrable_sq_norm N.zero_memLp.aestronglyMeasurable).mp N.zero_memLp))
  have hcont : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, Q s) (Icc 0 T0) := by
    simpa only [uIcc_of_le hT0.le] using
      intervalIntegral.continuousOn_primitive_interval' hQ (left_mem_uIcc : 0 ∈ uIcc 0 T0)
  obtain ⟨eta, heta, hnear⟩ := Metric.continuousWithinAt_iff.mp
    (hcont 0 ⟨le_rfl, hT0.le⟩) (min (a ^ 2) (b ^ 2))
      (lt_min (sq_pos_of_pos ha) (sq_pos_of_pos hb))
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
    linarith only [hle, heta]
  have hsqrt : Real.sqrt t ≤ q := by
    nlinarith only [htq, hq.le, Real.sq_sqrt ht.le, Real.sqrt_nonneg t]
  have htrace : 2 * N.lowerConstant * Real.sqrt t ≤ d / 8 :=
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)).trans hlower
  have hintegral : (∫ s in (0 : ℝ)..t, Q s) < min (a ^ 2) (b ^ 2) := by
    have hdist := hnear ⟨ht.le, htT0⟩
      (by simpa [Real.dist_eq, abs_of_nonneg ht.le] using hteta)
    simp only [intervalIntegral.integral_same, dist_zero_right, Real.norm_eq_abs] at hdist
    exact (le_abs_self (∫ s in (0 : ℝ)..t, Q s)).trans_lt hdist
  let P := (initialHeatHigh_memLp_energy lambda w ht.le).1.toLp (initialHeatHigh lambda w)
  let Z := (N.restrict htT0).zero_memLp.toLp (fun s => N.toFun s 0)
  have hPnormsq : ‖P‖ ^ 2 = ∫ s, ‖initialHeatHigh lambda w s‖ ^ 2 ∂timeMeasure t :=
    norm_toLp_sq (initialHeatHigh_memLp_energy lambda w ht.le).1
  have hZnormsq : ‖Z‖ ^ 2 = ∫ s, ‖N.toFun s 0‖ ^ 2 ∂timeMeasure t :=
    norm_toLp_sq (N.restrict htT0).zero_memLp
  have hparts : (∫ s, ‖initialHeatHigh lambda w s‖ ^ 2 ∂timeMeasure t) +
      (∫ s, ‖N.toFun s 0‖ ^ 2 ∂timeMeasure t) = ∫ s in (0 : ℝ)..t, Q s := by
    have hp := (initialHeatHigh_memLp_energy lambda w ht.le).1
    have hz := (N.restrict htT0).zero_memLp
    rw [intervalIntegral.integral_of_le ht.le]
    exact (integral_add ((memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp)
      ((memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).mp hz)).symm
  have hnorms : ‖P‖ ^ 2 + ‖Z‖ ^ 2 < min (a ^ 2) (b ^ 2) := by
    rw [hPnormsq, hZnormsq, hparts]
    exact hintegral
  have hPa : ‖P‖ ≤ a :=
    (sq_le_sq₀ (norm_nonneg P) ha.le).mp
      ((le_add_of_nonneg_right (sq_nonneg ‖Z‖)).trans (lt_min_iff.mp hnorms).1.le)
  have hZb : ‖Z‖ < b :=
    (sq_lt_sq₀ (norm_nonneg Z) hb.le).mp
      ((le_add_of_nonneg_left (sq_nonneg ‖P‖)).trans_lt (lt_min_iff.mp hnorms).2)
  have hPsmall : 2 * N.principalConstant * ‖P‖ ≤ d / 8 := by
    have heq : a * (16 * (N.principalConstant + 1)) = d := div_mul_cancel₀ d (by positivity)
    have hp := mul_le_mul_of_nonneg_left hPa N.principalConstant.coe_nonneg
    nlinarith only [heq, hp, hPa, norm_nonneg P]
  have hkappa : 2 * N.perturbationConstant + 8 * N.principalConstant * r +
      2 * N.principalConstant * ‖P‖ + 2 * N.lowerConstant * Real.sqrt t ≤ 1 - d / 2 := by
    have hdEq : d = 1 - 2 * N.perturbationConstant := rfl
    linarith only [hdEq, hprincipal, hPsmall, htrace]
  refine ⟨r, hr, hrr0, t, ht, htT0, ht1, by linarith only [hkappa, hd], ?_⟩
  change ‖Z‖ < _
  dsimp only [b] at hZb
  nlinarith only [hZb, hkappa, hr.le]

theorem norm_fixedPoint_lt_half [BorelSpace (State iota)]
    (N : CenteredSpectralResidual lambda w T) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    {r : ℝ} (hr : 0 < r)
    (hkappa : 2 * N.perturbationConstant + 8 * N.principalConstant * r +
      2 * N.principalConstant *
        ‖(initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)‖ +
      2 * N.lowerConstant * Real.sqrt T < 1)
    (hzero : ‖N.zero_memLp.toLp (fun t => N.toFun t 0)‖ <
      (1 - (2 * N.perturbationConstant + 8 * N.principalConstant * r +
        2 * N.principalConstant *
          ‖(initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)‖ +
        2 * N.lowerConstant * Real.sqrt T)) * r / 2)
    (F : ForcingSpace iota T) (hF : ‖F‖ ≤ r) (hfixed : N.forcingResidual hT F = F) :
    ‖F‖ < r / 2 := by
  have hdiff := N.norm_forcingResidual_sub_le hT hT1 hr.le F 0 hF
    (by simpa only [norm_zero] using hr.le)
  dsimp only at hdiff
  rw [hfixed, N.forcingResidual_zero hT, sub_zero] at hdiff
  have htri := norm_le_norm_sub_add F (N.zero_memLp.toLp (fun t => N.toFun t 0))
  nlinarith only [hdiff, htri, hzero, hkappa]

end PoincareConjecture.M63.CenteredSpectralResidual
