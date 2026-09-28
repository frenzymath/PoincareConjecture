import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialResponseTrace
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.StrictCenteredInterval










set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture.M63.CenteredSpectralResidual

open SpectralHeatNative QuasilinearDeTurckNative





theorem exists_uncut_response {iota E : Type*} [Countable iota]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace (State iota)] [BorelSpace (State iota)]
    {lambda : iota → NNReal} {w : State iota} {T0 r0 : ℝ}
    (N : CenteredSpectralResidual lambda w T0) (hT0 : 0 < T0) (hr0 : 0 < r0)
    (heps : (N.perturbationConstant : ℝ) < 1 / 2)
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (G : ℝ → State iota → E) (Q : ℝ → State iota → State iota)
    (hsource : ∀ᵐ t ∂timeMeasure T0, ∀ x,
      ‖shiftedBaseMultiplier lambda x‖ ≤ r0 →
      N.toFun t x =
        M (G t (heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x))
          (initialHeatHigh lambda w t + x) +
        Q t (heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x) -
        M (G t (heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x))
          (shiftedBaseMultiplier lambda
            (heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x))) :
    ∃ T : ℝ, ∃ hT : 0 < T, ∃ hTT0 : T ≤ T0, T ≤ 1 ∧
      ∃ F : ForcingSpace iota T,
        ‖F‖ < r0 / 2 ∧ (N.restrict hTT0).forcingResidual hT.le F = F ∧
        (∀ t : Icc (0 : ℝ) T,
          ‖initialResponseTrace lambda w hT.le F t - heat lambda (t : ℝ).toNNReal w‖ < r0) ∧
        ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          F t = M (G t (initialResponseTrace lambda w hT.le F ⟨t, ht⟩))
            (initialHeatHigh lambda w t + shiftedHighOperator hT.le lambda F t -
              shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT.le F ⟨t, ht⟩)) +
            Q t (initialResponseTrace lambda w hT.le F ⟨t, ht⟩) := by
  obtain ⟨r, hr, hrr0, T, hT, hTT0, hT1, hkappa, hzero⟩ :=
    N.exists_strict_positive_interval hT0 heps hr0
  let Nt := N.restrict hTT0
  let kappa : ℝ := 2 * Nt.perturbationConstant + 8 * Nt.principalConstant * r +
    2 * Nt.principalConstant *
      ‖(initialHeatHigh_memLp_energy lambda w hT.le).1.toLp (initialHeatHigh lambda w)‖ +
    2 * Nt.lowerConstant * Real.sqrt T
  have hk : kappa < 1 := hkappa
  have hz : ‖Nt.zero_memLp.toLp (fun t => Nt.toFun t 0)‖ < (1 - kappa) * r / 2 := hzero
  have hweak : ‖Nt.zero_memLp.toLp (fun t => Nt.toFun t 0)‖ ≤ (1 - kappa) * r := by
    have hpos := mul_pos (sub_pos.mpr hk) hr
    linarith only [hz, hpos]
  obtain ⟨F, _U, _D, _E, hF, _hU, _hD, _hE, hfix, _hrest⟩ :=
    Nt.exists_initial_spectral_response hT.le hT1 hr.le hk hweak
  have hFhalf := Nt.norm_fixedPoint_lt_half hT.le hT1 hr hk hz F hF hfix
  have hFcap : ‖F‖ < r0 / 2 := by linarith only [hFhalf, hrr0]
  have htwice : 2 * ‖F‖ < r0 := by linarith only [hFcap]
  refine ⟨T, hT, hTT0, hT1, F, hFcap, hfix, ?_, ?_⟩
  · intro t
    have hsqrt : Real.sqrt T ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT1
    have hb := (initialResponseTrace_spec lambda w hT.le F).2.2.1 t
    apply hb.trans_lt
    calc
      (Real.sqrt T + 1) * ‖F‖ ≤ 2 * ‖F‖ := by gcongr; linarith only [hsqrt]
      _ < r0 := htwice
  · have hsourceT := ae_mono
      (Measure.restrict_mono (Ioc_subset_Ioc le_rfl hTT0) le_rfl) hsource
    have hFsource := Nt.forcingResidual_coe hT.le F
    rw [hfix] at hFsource
    filter_upwards [hsourceT, hFsource, intermediate_high_eq_trace hT.le lambda F,
      intermediate_high_bound hT.le hT1 lambda F] with t hN hFs htrace hbound
    intro ht
    have hball : ‖shiftedBaseMultiplier lambda (shiftedHighOperator hT.le lambda F t)‖ ≤ r0 :=
      hbound.trans htwice.le
    have hV : heat lambda t.toNNReal w +
        shiftedBaseMultiplier lambda (shiftedHighOperator hT.le lambda F t) =
          initialResponseTrace lambda w hT.le F ⟨t, ht⟩ := by
      change heat lambda t.toNNReal w +
        shiftedBaseMultiplier lambda (shiftedHighOperator hT.le lambda F t) =
          heat lambda t.toNNReal w + shiftedTracePath hT.le lambda F ⟨t, ht⟩
      rw [htrace ht]
    have huncut := hN (shiftedHighOperator hT.le lambda F t) hball
    rw [hV] at huncut
    calc
      F t = N.toFun t (shiftedHighOperator hT.le lambda F t) := hFs
      _ = M (G t (initialResponseTrace lambda w hT.le F ⟨t, ht⟩))
          (initialHeatHigh lambda w t + shiftedHighOperator hT.le lambda F t) +
          Q t (initialResponseTrace lambda w hT.le F ⟨t, ht⟩) -
          M (G t (initialResponseTrace lambda w hT.le F ⟨t, ht⟩))
            (shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT.le F ⟨t, ht⟩)) :=
        huncut
      _ = _ := by rw [map_sub]; abel

end PoincareConjecture.M63.CenteredSpectralResidual
