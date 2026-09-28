import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialForcingAgreement
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.StrictCenteredInterval










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M63.CenteredSpectralResidual

open SpectralHeatNative QuasilinearDeTurckNative DeTurckMetricProducerNative




theorem exists_initial_parameter_branch
    {iota E : Type*} [Countable iota] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace (State iota)] [BorelSpace (State iota)]
    {lambda : iota → NNReal} {w : State iota} {T0 r0 : ℝ} {k : ℕ∞}
    (N : CenteredSpectralResidual lambda w T0) (hT0 : 0 < T0) (hr0 : 0 < r0)
    (heps : (N.perturbationConstant : ℝ) < 1 / 2) (hk : k ≠ 0)
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (G : ℝ × State iota → E) (Q : ℝ × State iota → State iota)
    (hG : ContDiff ℝ k G) (hQ : ContDiff ℝ k Q)
    (hsource : ∀ᵐ t ∂timeMeasure T0, ∀ x,
      ‖shiftedBaseMultiplier lambda x‖ ≤ r0 →
      N.toFun t x =
        M (G (t, heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x))
          (initialHeatHigh lambda w t + x) +
        Q (t, heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x) -
        M (G (t, heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x))
          (shiftedBaseMultiplier lambda
            (heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x))) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ T0 ∧ T ≤ 1 ∧
      ∃ (F : ForcingSpace iota T) (u : State iota → ForcingSpace iota T),
        ‖F‖ < r0 / 2 ∧ u w = F ∧ ContDiffAt ℝ k u w ∧
        ContDiffAt ℝ k (fun w' => initialResponseTrace lambda w' hT.le (u w')) w ∧
        (∀ᶠ w' in 𝓝 w, ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          u w' t =
            M (G (t, initialResponseTrace lambda w' hT.le (u w') ⟨t, ht⟩))
              (initialHeatHigh lambda w' t + shiftedHighOperator hT.le lambda (u w') t -
                shiftedBaseMultiplier lambda
                  (initialResponseTrace lambda w' hT.le (u w') ⟨t, ht⟩)) +
              Q (t, initialResponseTrace lambda w' hT.le (u w') ⟨t, ht⟩)) ∧
        ∀ t : Icc (0 : ℝ) T,
          ‖initialResponseTrace lambda w hT.le F t - heat lambda (t : ℝ).toNNReal w‖ < r0 := by
  obtain ⟨r, hr, hrr0, T, hT, hTT0, hT1, hkappa, hzero⟩ :=
    N.exists_strict_positive_interval hT0 heps (show 0 < r0 / 2 by positivity)
  let Nt := N.restrict hTT0
  let kappa : ℝ := 2 * Nt.perturbationConstant + 8 * Nt.principalConstant * r +
    2 * Nt.principalConstant *
      ‖(initialHeatHigh_memLp_energy lambda w hT.le).1.toLp (initialHeatHigh lambda w)‖ +
    2 * Nt.lowerConstant * Real.sqrt T
  have hkappa0 : 0 ≤ kappa := by dsimp [kappa]; positivity
  have hkappa1 : kappa < 1 := hkappa
  have hz : ‖Nt.zero_memLp.toLp (fun t => Nt.toFun t 0)‖ < (1 - kappa) * r / 2 := hzero
  have hweak : ‖Nt.zero_memLp.toLp (fun t => Nt.toFun t 0)‖ ≤ (1 - kappa) * r := by
    have hpos := mul_pos (sub_pos.mpr hkappa1) hr
    linarith only [hz, hpos]
  obtain ⟨F, _U, _D, _E, hF, _hU, _hD, _hE, hfix, _hrest⟩ :=
    Nt.exists_initial_spectral_response hT.le hT1 hr.le hkappa1 hweak
  have hFhalf := Nt.norm_fixedPoint_lt_half hT.le hT1 hr hkappa1 hz F hF hfix
  have hFcap : ‖F‖ < r0 / 2 := by linarith only [hFhalf, hrr0, hr]
  have hsourceT := ae_mono
    (Measure.restrict_mono (Ioc_subset_Ioc le_rfl hTT0) le_rfl) hsource
  obtain ⟨R, hR, hrep, hagree⟩ := Nt.exists_contDiff_forcingResidual hT.le hT1 hr.le
    (show 2 * r ≤ r0 by linarith only [hrr0]) M G Q hG hQ hsourceT
  have hRfix : R (w, F) = F := (hagree F hF).trans hfix
  have hFinterior : ‖F‖ < r := by linarith only [hFhalf, hr]
  have hLip (A B : ForcingSpace iota T) (hA : ‖A‖ ≤ r) (hB : ‖B‖ ≤ r) :
      ‖R (w, A) - R (w, B)‖ ≤ kappa * ‖A - B‖ := by
    rw [hagree A hA, hagree B hB]
    exact Nt.norm_forcingResidual_sub_le hT.le hT1 hr.le A B hA hB
  have hk' : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast hk
  obtain ⟨u, huw, hu, hueq, _hunique⟩ :=
    exists_contDiffAt_fixedPoint_of_contraction R hk' hR.contDiffAt hRfix
      hFinterior hkappa0 hkappa1 hLip
  refine ⟨T, hT, hTT0, hT1, F, u, hFcap, huw, hu, ?_, ?_, ?_⟩
  · obtain ⟨V0, _, hV0⟩ := exists_initialHeatPath_operator lambda hT.le
    have hpath : (fun w' => initialResponseTrace lambda w' hT.le (u w')) =
        fun w' => V0 w' + shiftedTraceOperator hT.le lambda (u w') := by
      funext w'
      apply ContinuousMap.ext
      intro t
      change heat lambda (t : ℝ).toNNReal w' + shiftedTracePath hT.le lambda (u w') t = _
      rw [ContinuousMap.add_apply, hV0]
      rfl
    rw [hpath]
    exact V0.contDiff.contDiffAt.add
      ((shiftedTraceOperator hT.le lambda).contDiff.contDiffAt.comp w hu)
  · filter_upwards [hueq] with w' hw'
    have h := hrep w' (u w')
    rw [hw'] at h
    exact h
  · intro t
    have hsqrt : Real.sqrt T ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT1
    apply ((initialResponseTrace_spec lambda w hT.le F).2.2.1 t).trans_lt
    calc
      (Real.sqrt T + 1) * ‖F‖ ≤ 2 * ‖F‖ := by gcongr; linarith only [hsqrt]
      _ < r0 := by linarith only [hFcap]

end PoincareConjecture.M63.CenteredSpectralResidual
