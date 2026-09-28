import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialResponseTrace

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {iota : Type*} [Countable iota] (lambda : iota → NNReal)
  (w : State iota) {T : ℝ} (hT : 0 ≤ T) (F : ForcingSpace iota T)

theorem initialResponseTrace_integral :
    IntervalIntegrable
      (fun s => -initialHeatGenerator lambda w s + derivativeState lambda F s) volume 0 T ∧
      ∀ t : Icc (0 : ℝ) T,
        shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F t) =
          shiftedBaseMultiplier lambda w + ∫ s in (0 : ℝ)..(t : ℝ),
            -initialHeatGenerator lambda w s + derivativeState lambda F s := by
  have hG : IntervalIntegrable (initialHeatGenerator lambda w) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      ((initialHeatGenerator_memLp_energy lambda w hT).1.integrable (by norm_num))
  have hD := intervalIntegrable_derivativeState_of_memLp hT (Lp.memLp F) lambda
  refine ⟨hG.neg.add hD, ?_⟩
  intro t
  have hsub : uIcc (0 : ℝ) (t : ℝ) ⊆ uIcc (0 : ℝ) T := by
    simpa only [uIcc_of_le t.property.1, uIcc_of_le hT] using
      (Icc_subset_Icc le_rfl t.property.2)
  have hsum : (∫ s in (0 : ℝ)..(t : ℝ),
      -initialHeatGenerator lambda w s + derivativeState lambda F s) =
      -(∫ s in (0 : ℝ)..(t : ℝ), initialHeatGenerator lambda w s) +
        ∫ s in (0 : ℝ)..(t : ℝ), derivativeState lambda F s := by
    simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using
      intervalIntegral.integral_add ((hG.mono_set hsub).neg) (hD.mono_set hsub)
  rw [(initialResponseTrace_spec lambda w hT F).2.1 t,
    initialHeat_eq_sub_integral lambda w t.property.1, hsum]
  change shiftedBaseMultiplier lambda w -
      (∫ s in (0 : ℝ)..(t : ℝ), initialHeatGenerator lambda w s) +
      (∫ s in (0 : ℝ)..(t : ℝ), derivativeState lambda F s) = _
  abel

theorem initialResponseTrace_generator :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t -
          shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F ⟨t, ht⟩) =
        initialHeatGenerator lambda w t + generatorState lambda F t ∧
      (-initialHeatGenerator lambda w t + derivativeState lambda F t) +
          (initialHeatGenerator lambda w t + generatorState lambda F t) = F t := by
  have hG : generatorLp hT lambda F =ᵐ[timeMeasure T] generatorState lambda F :=
    (memLp_generatorState_of_memLp hT (Lp.memLp F) lambda).coeFn_toLp
  filter_upwards [Lp.coeFn_add (responseLp hT lambda F) (generatorLp hT lambda F),
    responseLp_coe hT lambda F, hG,
    derivativeState_add_generatorState_of_memLp hT (Lp.memLp F) lambda]
    with t hsum hresponse hgenerator heq
  intro ht
  have hhigh : shiftedHighOperator hT lambda F t =
      responseState lambda F t + generatorState lambda F t := by
    change (responseLp hT lambda F + generatorLp hT lambda F) t = _
    rw [hsum, Pi.add_apply, hresponse, hgenerator]
  constructor
  · rw [(initialResponseTrace_spec lambda w hT F).2.1 ⟨t, ht⟩, hhigh,
      initialHeatHigh]
    abel
  · calc
      _ = derivativeState lambda F t + generatorState lambda F t := by abel
      _ = F t := heq

theorem initialResponseTrace_integral_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : State iota →L[ℝ] E) (t : Icc (0 : ℝ) T) :
    A (shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F t)) =
      A (shiftedBaseMultiplier lambda w) + ∫ s in (0 : ℝ)..(t : ℝ),
        A (-initialHeatGenerator lambda w s + derivativeState lambda F s) := by
  obtain ⟨hD, hprimitive⟩ := initialResponseTrace_integral lambda w hT F
  have hsub : uIcc (0 : ℝ) (t : ℝ) ⊆ uIcc (0 : ℝ) T := by
    simpa only [uIcc_of_le t.property.1, uIcc_of_le hT] using
      (Icc_subset_Icc le_rfl t.property.2)
  rw [hprimitive t, map_add, A.intervalIntegral_comp_comm (hD.mono_set hsub)]

end PoincareConjecture.M63
