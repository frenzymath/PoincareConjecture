import PoincareConjecture.Proofs.M63.Mathlib.CenteredBilinearCoefficients
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CenteredCoefficientResidual










set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture.M63

open SpectralHeatNative QuasilinearDeTurckNative





theorem exists_centeredRealCoefficientSource
    {iota E : Type*} [Countable iota]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    [MeasurableSpace (State iota)] [BorelSpace (State iota)]
    (lambda : iota → NNReal) (w : State iota) {T0 r0 : ℝ} (hT0 : 0 < T0) (hr0 : 0 < r0)
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (G : ℝ → State iota → E) (Q : ℝ → State iota → State iota)
    (hGcont : Continuous (Function.uncurry G)) (hQcont : Continuous (Function.uncurry Q))
    (KG KQ : NNReal)
    (hG : ∀ t ∈ Icc 0 T0, ∀ u v, ‖u‖ ≤ ‖w‖ + r0 → ‖v‖ ≤ ‖w‖ + r0 →
      ‖G t u - G t v‖ ≤ KG * ‖u - v‖)
    (hQ : ∀ t ∈ Icc 0 T0, ∀ u v, ‖u‖ ≤ ‖w‖ + r0 → ‖v‖ ≤ ‖w‖ + r0 →
      ‖Q t u - Q t v‖ ≤ KQ * ‖u - v‖)
    (hzero : G 0 w = 0) :
    let eps : ℝ := 1 / (4 * (‖M‖ + 1))
    let V := fun t : ℝ => heat lambda t.toNNReal w
    let J := shiftedBaseMultiplier lambda
    let C := traceCutoff lambda r0
    ∃ T : ℝ, 0 < T ∧ T ≤ T0 ∧ ∃ N : CenteredSpectralResidual lambda w T,
      (N.perturbationConstant : ℝ) = ‖M‖ * eps ∧
      (N.principalConstant : ℝ) = 2 * ‖M‖ * KG ∧
      (N.lowerConstant : ℝ) =
        2 * (KQ + ‖M‖ * (KG * (‖w‖ + r0) + eps + KG * r0)) ∧
      (N.perturbationConstant : ℝ) < 1 / 2 ∧
      ∀ᵐ t ∂timeMeasure T, ∀ x,
        N.toFun t x = M (G t (V t + J (C x))) (initialHeatHigh lambda w t + x) +
          Q t (V t + J (C x)) - M (G t (V t + J (C x))) (J (V t + J (C x))) ∧
        (‖J x‖ ≤ r0 →
          N.toFun t x = M (G t (V t + J x)) (initialHeatHigh lambda w t + x) +
            Q t (V t + J x) - M (G t (V t + J x)) (J (V t + J x))) := by
  let eps : ℝ := 1 / (4 * (‖M‖ + 1))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hMeps : ‖M‖ * eps < 1 / 2 := by
    dsimp only [eps]
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    linarith [norm_nonneg M]
  let V := fun t : ℝ => heat lambda t.toNNReal w
  let J := shiftedBaseMultiplier lambda
  let a := fun t z => G t (V t + z)
  let b := fun t z => Q t (V t + z) - M (a t z) (J (V t + z))
  have hV : Continuous V := (continuous_heat_apply lambda w).comp continuous_real_toNNReal
  have hV0 : V 0 = w := by simp [V]
  have hVnorm (t : ℝ) : ‖V t‖ ≤ ‖w‖ := norm_heat_apply_le lambda t.toNNReal w
  have hac : Continuous (Function.uncurry a) :=
    hGcont.comp (continuous_fst.prodMk ((hV.comp continuous_fst).add continuous_snd))
  have hbc : Continuous (Function.uncurry b) :=
    (hQcont.comp (continuous_fst.prodMk ((hV.comp continuous_fst).add continuous_snd))).sub
      (M.continuous₂.comp (hac.prodMk
        (J.continuous.comp ((hV.comp continuous_fst).add continuous_snd))))
  have ha0 : Continuous (fun t => G t (V t)) := hGcont.comp (continuous_id.prodMk hV)
  obtain ⟨delta, hdelta, hnear⟩ := Metric.continuousAt_iff.mp ha0.continuousAt eps heps
  let T := min T0 (delta / 2)
  have hT : 0 < T := lt_min hT0 (by positivity)
  have hTT0 : T ≤ T0 := min_le_left _ _
  have hTdelta : T < delta := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hbase (t : ℝ) (ht : t ∈ Icc 0 T) : ‖G t (V t)‖ ≤ eps := by
    have hdist : dist t 0 < delta := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact ht.2.trans_lt hTdelta
    have h := hnear hdist
    simpa only [hV0, hzero, dist_zero_right] using h.le
  let Kb : ℝ := KQ + ‖M‖ * (KG * (‖w‖ + r0) + eps + KG * r0)
  have hKb : 0 ≤ Kb := by dsimp [Kb]; positivity
  have hlocal : ∀ᵐ t ∂timeMeasure T,
      ‖a t 0‖ ≤ (⟨eps, heps.le⟩ : NNReal) ∧
      (∀ z z', ‖z‖ ≤ r0 → ‖z'‖ ≤ r0 → ‖a t z - a t z'‖ ≤ KG * ‖z - z'‖) ∧
      (∀ z z', ‖z‖ ≤ r0 → ‖z'‖ ≤ r0 → ‖b t z - b t z'‖ ≤
        (⟨Kb, hKb⟩ : NNReal) * ‖z - z'‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : t ∈ Icc 0 T0 := ⟨ht.1.le, ht.2.trans hTT0⟩
    have hbnd := hbase t ⟨ht.1.le, ht.2⟩
    have hboth (z z' : State iota) (hz : ‖z‖ ≤ r0) (hz' : ‖z'‖ ≤ r0) :=
      norm_centeredBilinearCoefficients_sub_le J (norm_shiftedBaseMultiplier_le lambda)
        M (G t) (Q t) (V t) (norm_nonneg w) hr0 heps.le KG.coe_nonneg KQ.coe_nonneg
        (hVnorm t) hbnd (hG t ht0) (hQ t ht0) z z' hz hz'
    refine ⟨by simpa only [a, add_zero] using hbnd,
      fun z z' hz hz' => (hboth z z' hz hz').1,
      fun z z' hz hz' => (hboth z z' hz hz').2⟩
  have hb0cont : Continuous (fun t => b t 0) := hbc.comp (continuous_id.prodMk continuous_const)
  have hb0 : MemLp (fun t => b t 0) 2 (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm hb0cont.aestronglyMeasurable).mpr
      ((hb0cont.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  obtain ⟨N, hNeps, hNA, hNB, hN⟩ := exists_centeredCoefficientResidual lambda w hT.le hr0
    M a b hac hbc ⟨eps, heps.le⟩ KG ⟨Kb, hKb⟩ hlocal hb0
  refine ⟨T, hT, hTT0, N, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hNeps]
    rfl
  · simp only [hNA, NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm]
  · rw [hNB]
    rfl
  · rw [hNeps]
    exact hMeps
  · filter_upwards [hN] with t ht
    intro x
    simpa only [a, b, add_sub_assoc] using ht x

end PoincareConjecture.M63
