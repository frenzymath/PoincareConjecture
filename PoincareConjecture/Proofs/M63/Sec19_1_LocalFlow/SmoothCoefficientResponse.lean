import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CoefficientParameterResponse
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialForcingLocalAgreement
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialTraceNeighborhood










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M63

open SpectralHeatNative QuasilinearDeTurckNative DeTurckMetricProducerNative






theorem exists_smooth_coefficient_parameter_response
    {iota E : Type*} [Countable iota]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    [MeasurableSpace (State iota)] [BorelSpace (State iota)]
    (lambda : iota → NNReal) (w : State iota) {Tcap rcap : ℝ}
    (hTcap : 0 < Tcap) (hrcap : 0 < rcap)
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (G : ℝ × State iota → E) (Q : ℝ × State iota → State iota)
    (hG : ContDiff ℝ 1 G) (hQ : ContDiff ℝ 1 Q) (hzero : G (0, w) = 0)
    (hLip : ∀ R : ℝ, 0 ≤ R → ∃ KG KQ : NNReal, ∀ t u v,
      ‖u‖ ≤ R → ‖v‖ ≤ R →
        ‖G (t, u) - G (t, v)‖ ≤ KG * ‖u - v‖ ∧
        ‖Q (t, u) - Q (t, v)‖ ≤ KQ * ‖u - v‖)
    {O : Set (ℝ × State iota)} (hO : IsOpen O) (hw : (0, w) ∈ O)
    (hext : ∀ k : ℕ, ∃ (Gk : ℝ × State iota → E) (Qk : ℝ × State iota → State iota),
      ContDiff ℝ k Gk ∧ ContDiff ℝ k Qk ∧
      ∀ t u, 0 ≤ t → (t, u) ∈ O → G (t, u) = Gk (t, u) ∧ Q (t, u) = Qk (t, u)) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ Tcap ∧ T ≤ 1 ∧
      ∃ (F : ForcingSpace iota T) (u : State iota → ForcingSpace iota T),
        ‖F‖ < rcap / 2 ∧ u w = F ∧ ContDiffAt ℝ ∞ u w ∧
        ContDiffAt ℝ ∞ (fun w' => initialResponseTrace lambda w' hT.le (u w')) w ∧
        (∀ᶠ w' in 𝓝 w, ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          u w' t =
            M (G (t, initialResponseTrace lambda w' hT.le (u w') ⟨t, ht⟩))
              (initialHeatHigh lambda w' t + shiftedHighOperator hT.le lambda (u w') t -
                shiftedBaseMultiplier lambda
                  (initialResponseTrace lambda w' hT.le (u w') ⟨t, ht⟩)) +
              Q (t, initialResponseTrace lambda w' hT.le (u w') ⟨t, ht⟩)) ∧
        (∀ᶠ z : State iota × ForcingSpace iota T in 𝓝 (w, F),
          (∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
            z.2 t =
              M (G (t, initialResponseTrace lambda z.1 hT.le z.2 ⟨t, ht⟩))
                (initialHeatHigh lambda z.1 t + shiftedHighOperator hT.le lambda z.2 t -
                  shiftedBaseMultiplier lambda
                    (initialResponseTrace lambda z.1 hT.le z.2 ⟨t, ht⟩)) +
                Q (t, initialResponseTrace lambda z.1 hT.le z.2 ⟨t, ht⟩)) ↔ u z.1 = z.2) ∧
        (∀ t : Icc (0 : ℝ) T,
          ((t : ℝ), initialResponseTrace lambda w hT.le F t) ∈ O) ∧
        ∀ t : Icc (0 : ℝ) T,
          ‖initialResponseTrace lambda w hT.le F t - heat lambda (t : ℝ).toNNReal w‖ < rcap := by
  obtain ⟨rdom, hrdom, Tdom, hTdom, hTdomcap, _hTdom1, hdomain⟩ :=
    exists_initialResponseTrace_neighborhood lambda w
      (ContinuousMap.const Unit) ContinuousMap.continuous_const' hO (fun _ => hw) hTcap
  let r0 := min rcap rdom
  have hr0 : 0 < r0 := lt_min hrcap hrdom
  have hr0cap : r0 ≤ rcap := min_le_left _ _
  have hr0dom : r0 ≤ rdom := min_le_right _ _
  obtain ⟨KG, KQ, hcoeff⟩ := hLip (‖w‖ + r0) (by positivity)
  obtain ⟨T1, hT1, hT1dom, N, _hepsEq, _hprincipal, _hlower, heps, hsource⟩ :=
    exists_centeredRealCoefficientSource lambda w hTdom hr0 M
      (fun t u => G (t, u)) (fun t u => Q (t, u)) hG.continuous hQ.continuous KG KQ
      (fun t _ u v hu hv => (hcoeff t u v hu hv).1)
      (fun t _ u v hu hv => (hcoeff t u v hu hv).2) hzero
  have huncut := hsource.mono (fun _ ht x hx => (ht x).2 hx)
  obtain ⟨r, hr, hrr0, T, hT, hTT1, hTle1, hkappa, hzeroSource⟩ :=
    N.exists_strict_positive_interval hT1 heps (show 0 < r0 / 2 by positivity)
  let Nt := N.restrict hTT1
  let kappa : ℝ := 2 * Nt.perturbationConstant + 8 * Nt.principalConstant * r +
    2 * Nt.principalConstant *
      ‖(initialHeatHigh_memLp_energy lambda w hT.le).1.toLp (initialHeatHigh lambda w)‖ +
    2 * Nt.lowerConstant * Real.sqrt T
  have hkappa0 : 0 ≤ kappa := by dsimp [kappa]; positivity
  have hkappa1 : kappa < 1 := hkappa
  have hz : ‖Nt.zero_memLp.toLp (fun t => Nt.toFun t 0)‖ < (1 - kappa) * r / 2 :=
    hzeroSource
  have hweak : ‖Nt.zero_memLp.toLp (fun t => Nt.toFun t 0)‖ ≤ (1 - kappa) * r := by
    have hpos := mul_pos (sub_pos.mpr hkappa1) hr
    linarith only [hz, hpos]
  obtain ⟨F, _U, _D, _E, hF, _hU, _hD, _hE, hfix, _hrest⟩ :=
    Nt.exists_initial_spectral_response hT.le hTle1 hr.le hkappa1 hweak
  have hFhalf := Nt.norm_fixedPoint_lt_half hT.le hTle1 hr hkappa1 hz F hF hfix
  have hFcap : ‖F‖ < r0 / 2 := by linarith only [hFhalf, hrr0, hr]
  have hinside (t : Icc (0 : ℝ) T) :
      ((t : ℝ), initialResponseTrace lambda w hT.le F t) ∈ O :=
    hdomain T hT.le (hTT1.trans hT1dom) F
      (hFcap.trans_le (by gcongr)) t ()
  have hsourceT := ae_mono
    (Measure.restrict_mono (Ioc_subset_Ioc le_rfl hTT1) le_rfl) huncut
  obtain ⟨R, _hR, hrep, hagree⟩ := Nt.exists_contDiff_forcingResidual hT.le hTle1 hr.le
    (show 2 * r ≤ r0 by linarith only [hrr0]) M G Q hG hQ hsourceT
  have hRinf : ContDiffAt ℝ ∞ R (w, F) :=
    contDiffAt_initialForcing_of_local_extensions lambda hT.le M G Q R hrep w F hO hinside hext
  have hRfix : R (w, F) = F := (hagree F hF).trans hfix
  have hFinterior : ‖F‖ < r := by linarith only [hFhalf, hr]
  have hRLip (A B : ForcingSpace iota T) (hA : ‖A‖ ≤ r) (hB : ‖B‖ ≤ r) :
      ‖R (w, A) - R (w, B)‖ ≤ kappa * ‖A - B‖ := by
    rw [hagree A hA, hagree B hB]
    exact Nt.norm_forcingResidual_sub_le hT.le hTle1 hr.le A B hA hB
  obtain ⟨u, huw, hu, hueq, hunique⟩ :=
    exists_contDiffAt_fixedPoint_of_contraction R (k := ∞) (by simp) hRinf hRfix
      hFinterior hkappa0 hkappa1 hRLip
  refine ⟨T, hT, hTT1.trans (hT1dom.trans hTdomcap), hTle1, F, u,
    hFcap.trans_le (by gcongr), huw, hu, ?_, ?_, ?_, hinside, ?_⟩
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
  · filter_upwards [hunique] with z hz
    refine Iff.trans ⟨?_, ?_⟩ hz
    · intro heq
      apply Lp.ext
      filter_upwards [hrep z.1 z.2, heq, ae_restrict_mem measurableSet_Ioc] with t h1 h2 ht
      exact (h1 ⟨ht.1.le, ht.2⟩).trans (h2 ⟨ht.1.le, ht.2⟩).symm
    · intro heq
      have h := hrep z.1 z.2
      rw [heq] at h
      exact h
  · intro t
    have hsqrt : Real.sqrt T ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hTle1
    apply ((initialResponseTrace_spec lambda w hT.le F).2.2.1 t).trans_lt
    calc
      (Real.sqrt T + 1) * ‖F‖ ≤ 2 * ‖F‖ := by gcongr; linarith only [hsqrt]
      _ < rcap := by linarith only [hFcap, hr0cap]

end PoincareConjecture.M63
