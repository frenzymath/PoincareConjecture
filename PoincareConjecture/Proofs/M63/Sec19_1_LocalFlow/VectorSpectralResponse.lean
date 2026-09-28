import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorSpectralTranslation
import PoincareConjecture.Proofs.M63.Mathlib.StrongL2Action
import PoincareConjecture.Proofs.M03.Existence.DeTurckPullbackResponseNative
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialSpectralTrace
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialResponseTrace

set_option autoImplicit false

open MeasureTheory Set Filter AddCircle
open scoped Topology

namespace PoincareConjecture.M63

open PoincareConjecture.SpectralHeatNative
open PoincareConjecture.DeTurckPullbackResponseNative
open PoincareConjecture.DeTurckParameterForcingNative

variable {L : ℝ} {ι : Type*} [Fintype ι]

private noncomputable def periodicVectorLambda (L : ℝ) :
    (ℤ × Fin 2) × ι → NNReal := fun p => periodicSpectrum L p.1

private theorem vector_weight_relation {ι : Type*} [Countable ι] (L : ℝ) (k : ℕ)
    (u : State ((ℤ × Fin 2) × ι)) :
    ∀ p, scaleDecode (periodicVectorLambda L) k u p =
      (scaleWeight (periodicVectorLambda L) k ((p.1.1, (0 : Fin 2)), p.2))⁻¹ * u p := by
  intro p
  rfl

theorem vectorPeriodicSpectralTranslation_scaleDecode (k : ℕ)
    (u : State ((ℤ × Fin 2) × ι)) (a : ℝ) :
    vectorPeriodicSpectralTranslation (L := L) a
        (scaleDecode (periodicVectorLambda L) k u) =
      scaleDecode (periodicVectorLambda L) k
        (vectorPeriodicSpectralTranslation (L := L) a u) := by
  have h := vectorPeriodicSpectralTranslation_real_weight (L := L)
    (m := fun q : ℤ × ι =>
      (scaleWeight (periodicVectorLambda L) k ((q.1, (0 : Fin 2)), q.2))⁻¹)
    u (scaleDecode (periodicVectorLambda L) k u)
    (vector_weight_relation L k u) a
  apply lp.ext
  funext p
  have hp := h p
  have hweight : scaleWeight (periodicVectorLambda L) k p =
      scaleWeight (periodicVectorLambda L) k ((p.1.1, (0 : Fin 2)), p.2) := by
    unfold scaleWeight periodicVectorLambda
    change (Real.sqrt (1 + (periodicSpectrum L p.1 : ℝ)) ^ k) =
      Real.sqrt (1 + (periodicSpectrum L (p.1.1, (0 : Fin 2)) : ℝ)) ^ k
    rfl
  rw [scaleDecode_apply]
  rw [hweight]
  exact hp

theorem vectorPeriodicSpectralTranslation_heat (t : NNReal)
    (u : State ((ℤ × Fin 2) × ι)) (a : ℝ) :
    vectorPeriodicSpectralTranslation (L := L) a
        (heat (periodicVectorLambda L) t u) =
      heat (periodicVectorLambda L) t
        (vectorPeriodicSpectralTranslation (L := L) a u) := by
  have h := vectorPeriodicSpectralTranslation_real_weight (L := L)
    (m := fun q : ℤ × ι =>
      Real.exp (-(t : ℝ) * periodicVectorLambda L ((q.1, (0 : Fin 2)), q.2)))
    u (heat (periodicVectorLambda L) t u) (by
      intro p
      rfl) a
  apply lp.ext
  funext p
  have hp := h p
  change _ = Real.exp (-(t : ℝ) * periodicVectorLambda L p) * _
  simpa only [periodicVectorLambda, periodicSpectrum] using hp

theorem vectorPeriodicSpectralTranslation_shiftedBaseMultiplier
    (u : State ((ℤ × Fin 2) × ι)) (a : ℝ) :
    vectorPeriodicSpectralTranslation (L := L) a
        (shiftedBaseMultiplier (periodicVectorLambda L) u) =
      shiftedBaseMultiplier (periodicVectorLambda L)
        (vectorPeriodicSpectralTranslation (L := L) a u) := by
  have h := vectorPeriodicSpectralTranslation_real_weight (L := L)
    (m := fun q : ℤ × ι =>
      (Real.sqrt (1 + periodicVectorLambda L ((q.1, (0 : Fin 2)), q.2)))⁻¹)
    u (shiftedBaseMultiplier (periodicVectorLambda L) u) (by
      intro p
      simp only [shiftedBaseMultiplier, multiplier_apply]
      simp [periodicVectorLambda, periodicSpectrum, one_div]) a
  apply lp.ext
  funext p
  have hp := h p
  calc
    vectorPeriodicSpectralTranslation (L := L) a
        (shiftedBaseMultiplier (periodicVectorLambda L) u) p =
        (Real.sqrt (1 + periodicVectorLambda L
          ((p.1.1, (0 : Fin 2)), p.2)))⁻¹ *
          vectorPeriodicSpectralTranslation (L := L) a u p := hp
    _ = shiftedBaseMultiplier (periodicVectorLambda L)
        (vectorPeriodicSpectralTranslation (L := L) a u) p := by
      simp [shiftedBaseMultiplier, multiplier_apply, periodicVectorLambda,
        periodicSpectrum, one_div]

theorem shiftedBaseMultiplier_injective
    {κ : Type*} [Countable κ] (lambda : κ → NNReal) :
    Function.Injective (shiftedBaseMultiplier lambda) := by
  intro u v h
  apply lp.ext
  funext i
  have hi := congrArg (fun z : State κ => z i) h
  change (1 / Real.sqrt (1 + (lambda i : ℝ))) * u i =
    (1 / Real.sqrt (1 + (lambda i : ℝ))) * v i at hi
  exact mul_left_cancel₀ (by positivity : (1 / Real.sqrt (1 + (lambda i : ℝ))) ≠ 0) hi

theorem continuous_vectorPeriodicSpectralTranslation_compLpL
    (μ : Measure ℝ) :
    Continuous (fun z : ℝ × Lp (State ((ℤ × Fin 2) × ι)) 2 μ =>
      (vectorPeriodicSpectralTranslation (L := L) z.1).compLpL 2 μ z.2) := by
  apply continuous_compLpL_of_strong
    (A := vectorPeriodicSpectralTranslation (L := L)) μ (K := 1) zero_le_one
  · intro a
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simpa only [(vectorPeriodicSpectralTranslation_spec a u).2,
      one_mul] using (le_refl (‖u‖))
  · exact continuous_vectorPeriodicSpectralTranslation (L := L)

theorem vectorPeriodicSpectralTranslation_compLpL_zero
    (μ : Measure ℝ) (F : Lp (State ((ℤ × Fin 2) × ι)) 2 μ) :
  (vectorPeriodicSpectralTranslation (L := L) 0).compLpL 2 μ F = F := by
  rw [vectorPeriodicSpectralTranslation_zero (L := L) (ι := ι)]
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.id ℝ
    (State ((ℤ × Fin 2) × ι))).coeFn_compLpL F] with t hact
  simpa using hact

private theorem vectorPeriodicSpectralTranslation_pullbackForcing
    {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace ((ℤ × Fin 2) × ι) T) (a : ℝ) :
    pullbackForcing (periodicVectorLambda L) hT
        (vectorPeriodicSpectralTranslation (L := L) a)
        (vectorPeriodicSpectralTranslation (L := L) a) F =
      (vectorPeriodicSpectralTranslation (L := L) a).compLpL
        2 (timeMeasure T) F := by
  let D := vectorPeriodicSpectralTranslation (L := L) (ι := ι) a
  have hcompat : ∀ z, D (scaleDecode (periodicVectorLambda L) 2 z) =
      scaleDecode (periodicVectorLambda L) 2 (D z) := by
    intro z
    exact vectorPeriodicSpectralTranslation_scaleDecode (L := L) 2 z a
  have hgen : (highGenerator (periodicVectorLambda L)).comp D =
      D.comp (highGenerator (periodicVectorLambda L)) := by
    apply ContinuousLinearMap.ext
    intro z
    change highGenerator (periodicVectorLambda L) (D z) =
      D (highGenerator (periodicVectorLambda L) z)
    simp only [highGenerator, sub_apply, map_sub,
      ContinuousLinearMap.id_apply]
    rw [hcompat]
  have hcomm : pullbackCommutator (periodicVectorLambda L) D D = 0 := by
    unfold pullbackCommutator
    rw [hgen]
    simp
  unfold pullbackForcing
  rw [hcomm]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      ((vectorPeriodicSpectralTranslation (L := L) a).compLpL
        2 (timeMeasure T) F)
      ((0 : State ((ℤ × Fin 2) × ι) →L[ℝ]
        State ((ℤ × Fin 2) × ι)).compLpL 2 (timeMeasure T)
        (shiftedHighOperator hT (periodicVectorLambda L) F)),
    (0 : State ((ℤ × Fin 2) × ι) →L[ℝ]
      State ((ℤ × Fin 2) × ι)).coeFn_compLpL
      (shiftedHighOperator hT (periodicVectorLambda L) F)] with t hadd hzero
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hzero]
  simp

theorem vectorPeriodicSpectralTranslation_responseState
    {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace ((ℤ × Fin 2) × ι) T) (a : ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    responseState (periodicVectorLambda L)
        ((vectorPeriodicSpectralTranslation (L := L) a).compLpL
          2 (timeMeasure T) F) t =
      vectorPeriodicSpectralTranslation (L := L) a
        (responseState (periodicVectorLambda L) F t) := by
  rw [← vectorPeriodicSpectralTranslation_pullbackForcing
    (L := L) hT F a]
  apply responseState_pullbackForcing
    (periodicVectorLambda L) hT _ _ _ F ht
  intro z
  exact vectorPeriodicSpectralTranslation_scaleDecode (L := L) 2 z a

theorem vectorPeriodicSpectralTranslation_shiftedHigh
    {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace ((ℤ × Fin 2) × ι) T) (a : ℝ) :
    shiftedHighOperator hT (periodicVectorLambda L)
        ((vectorPeriodicSpectralTranslation (L := L) a).compLpL
          2 (timeMeasure T) F) =ᵐ[timeMeasure T]
      fun t => vectorPeriodicSpectralTranslation (L := L) a
        (shiftedHighOperator hT (periodicVectorLambda L) F t) := by
  rw [← vectorPeriodicSpectralTranslation_pullbackForcing
    (L := L) hT F a]
  apply shiftedHigh_pullbackForcing_ae
    (periodicVectorLambda L) hT _ _ _ F
  intro z
  exact vectorPeriodicSpectralTranslation_scaleDecode (L := L) 2 z a

theorem vectorPeriodicSpectralTranslation_initialResponseTrace
    {T : ℝ} (hT : 0 ≤ T)
    (w : State ((ℤ × Fin 2) × ι))
    (F : ForcingSpace ((ℤ × Fin 2) × ι) T) (a : ℝ)
    (t : Icc (0 : ℝ) T) :
    initialResponseTrace (periodicVectorLambda L)
        (vectorPeriodicSpectralTranslation (L := L) a w) hT
        ((vectorPeriodicSpectralTranslation (L := L) a).compLpL
          2 (timeMeasure T) F) t =
      vectorPeriodicSpectralTranslation (L := L) a
        (initialResponseTrace (periodicVectorLambda L) w hT F t) := by
  let D := vectorPeriodicSpectralTranslation (L := L) (ι := ι) a
  let J := shiftedBaseMultiplier
    (periodicVectorLambda L : (ℤ × Fin 2) × ι → NNReal)
  have hleft := (initialResponseTrace_spec (periodicVectorLambda L)
    (D w) hT (D.compLpL 2 (timeMeasure T) F)).2.1 t
  have hright := (initialResponseTrace_spec (periodicVectorLambda L)
    w hT F).2.1 t
  have hJ : J (initialResponseTrace (periodicVectorLambda L) (D w) hT
      (D.compLpL 2 (timeMeasure T) F) t) =
      J (D (initialResponseTrace (periodicVectorLambda L) w hT F t)) := by
    calc
      J (initialResponseTrace (periodicVectorLambda L) (D w) hT
          (D.compLpL 2 (timeMeasure T) F) t) =
          heat (periodicVectorLambda L) (t : ℝ).toNNReal (J (D w)) +
            responseState (periodicVectorLambda L)
              (D.compLpL 2 (timeMeasure T) F) t := hleft
      _ = heat (periodicVectorLambda L) (t : ℝ).toNNReal
            (D (J w)) +
            D (responseState (periodicVectorLambda L) F t) := by
          rw [vectorPeriodicSpectralTranslation_shiftedBaseMultiplier
              (L := L) w a,
            vectorPeriodicSpectralTranslation_responseState
              (L := L) hT F a t.property]
      _ = D (heat (periodicVectorLambda L) (t : ℝ).toNNReal (J w) +
            responseState (periodicVectorLambda L) F t) := by
          rw [map_add, vectorPeriodicSpectralTranslation_heat
            (L := L) (t : ℝ).toNNReal (J w) a]
      _ = J (D (initialResponseTrace (periodicVectorLambda L) w hT F t)) := by
          rw [← hright]
          exact vectorPeriodicSpectralTranslation_shiftedBaseMultiplier
            (L := L) (initialResponseTrace (periodicVectorLambda L) w hT F t) a
  exact shiftedBaseMultiplier_injective (periodicVectorLambda L) hJ

theorem vectorPeriodicSpectralTranslation_initialHeatHigh
    (w : State ((ℤ × Fin 2) × ι)) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    initialHeatHigh (periodicVectorLambda L)
        (vectorPeriodicSpectralTranslation (L := L) a w) t =
      vectorPeriodicSpectralTranslation (L := L) a
        (initialHeatHigh (periodicVectorLambda L) w t) := by
  let D := vectorPeriodicSpectralTranslation (L := L) (ι := ι) a
  let J := shiftedBaseMultiplier
    (periodicVectorLambda L : (ℤ × Fin 2) × ι → NNReal)
  apply shiftedBaseMultiplier_injective (periodicVectorLambda L)
  calc
    J (initialHeatHigh (periodicVectorLambda L) (D w) t) =
        heat (periodicVectorLambda L) t.toNNReal (D w) :=
      (initialHeatHigh_trace (periodicVectorLambda L) (D w) ht).1
    _ = D (heat (periodicVectorLambda L) t.toNNReal w) := by
      rw [vectorPeriodicSpectralTranslation_heat
        (L := L) t.toNNReal w a]
    _ = D (J (initialHeatHigh (periodicVectorLambda L) w t)) := by
      rw [(initialHeatHigh_trace (periodicVectorLambda L) w ht).1]
    _ = J (D (initialHeatHigh (periodicVectorLambda L) w t)) := by
      exact vectorPeriodicSpectralTranslation_shiftedBaseMultiplier
        (L := L) (initialHeatHigh (periodicVectorLambda L) w t) a

end PoincareConjecture.M63
