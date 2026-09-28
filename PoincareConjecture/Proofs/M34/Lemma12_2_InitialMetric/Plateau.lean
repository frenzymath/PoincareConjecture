import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.RadialProfile











set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M34



theorem capProfile_eq_round {a r : ℝ} (ha : 0 ≤ a) (hr : r ≤ a) :
    capProfile a r = 2 * Real.sin (r / 2) := by
  have hd (x : ℝ) : HasDerivAt (fun s : ℝ => 2 * Real.sin (s / 2))
      (Real.cos (x / 2)) x := by
    exact (((hasDerivAt_id' x).div_const 2).sin.const_mul 2).congr_deriv (by ring)
  calc
    capProfile a r = ∫ s in 0..r, Real.cos (s / 2) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact capSlope_eq_cos (hs.2.trans (max_le ha hr))
    _ = 2 * Real.sin (r / 2) := by
      simpa only [zero_div, Real.sin_zero, mul_zero, sub_zero] using
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
          ((Real.continuous_cos.comp (continuous_id.div_const 2)).intervalIntegrable 0 r)


theorem capProfile_eq_of_ge {a r s : ℝ}
    (hr : a + 1 / 2 ≤ r) (hs : a + 1 / 2 ≤ s) :
    capProfile a r = capProfile a s := by
  have hc := (capSlope_contDiff_right a).continuous
  have hz : (∫ x in r..s, capSlope a x) = 0 := by
    calc
      (∫ x in r..s, capSlope a x) = ∫ _ in r..s, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact capSlope_eq_zero ((le_min hr hs).trans hx.1)
      _ = 0 := by simp
  simpa only [capProfile, hz, add_zero] using
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 r) (hc.intervalIntegrable r s)



theorem capProfile_zero_parameter_le : capProfile 0 Real.pi ≤ 1 / 2 := by
  rw [capProfile_eq_of_ge (s := (1 / 2 : ℝ)) (by linarith [Real.pi_gt_three])
    (by norm_num)]
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1 / 2)
    (by norm_num) ((capSlope_contDiff_right 0).continuous.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) (fun x _ => capSlope_le_one 0 x)
  simpa only [capProfile, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_one] using h



theorem sqrt_two_lt_capProfile_half_pi :
    Real.sqrt 2 < capProfile (Real.pi / 2) Real.pi := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hbase : capProfile (Real.pi / 2) (Real.pi / 2) = Real.sqrt 2 := by
    rw [capProfile_eq_round (by positivity) le_rfl]
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four]
    ring
  have htail : 0 < ∫ x in (Real.pi / 2)..Real.pi, capSlope (Real.pi / 2) x := by
    apply intervalIntegral.integral_pos (by linarith)
      (capSlope_contDiff_right (Real.pi / 2)).continuous.continuousOn
    · intro x hx
      exact capSlope_nonneg le_rfl (by linarith [hx.1])
    · refine ⟨Real.pi / 2, ⟨le_rfl, by linarith⟩, ?_⟩
      rw [capSlope_eq_cos le_rfl]
      exact Real.cos_pos_of_mem_Ioo (by constructor <;> linarith)
  have hc := (capSlope_contDiff_right (Real.pi / 2)).continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (Real.pi / 2))
    (hc.intervalIntegrable (Real.pi / 2) Real.pi)
  change capProfile (Real.pi / 2) (Real.pi / 2) + _ =
    capProfile (Real.pi / 2) Real.pi at hadd
  rw [hbase] at hadd
  linarith



theorem exists_capProfile_normalized :
    ∃ a ∈ Ioo (0 : ℝ) (Real.pi / 2), capProfile a Real.pi = Real.sqrt 2 := by
  have hlo : capProfile 0 Real.pi < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith [capProfile_zero_parameter_le]
  have hhi := sqrt_two_lt_capProfile_half_pi
  obtain ⟨a, ha, heq⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    (capProfile_continuous_parameter Real.pi).continuousOn ⟨hlo.le, hhi.le⟩
  refine ⟨a, ⟨?_, ?_⟩, heq⟩
  · by_contra h
    have he : a = 0 := le_antisymm (not_lt.mp h) ha.1
    subst a
    exact (ne_of_lt hlo) heq
  · by_contra h
    have he : a = Real.pi / 2 := le_antisymm ha.2 (not_lt.mp h)
    subst a
    exact (ne_of_gt hhi) heq

end PoincareConjecture.M34
