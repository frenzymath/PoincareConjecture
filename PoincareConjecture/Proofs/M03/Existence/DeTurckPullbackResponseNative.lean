import PoincareConjecture.Proofs.M03.Existence.DeTurckParameterForcingNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckStatePullbackNative
import Mathlib.Analysis.ODE.Gronwall








set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.DeTurckPullbackResponseNative

open SpectralHeatNative QuasilinearDeTurckNative DeTurckParameterForcingNative

section LinearTransport

variable {iota : Type*} [Countable iota] {T : ℝ} (lambda : iota → NNReal)

def pullbackCommutator (PB PH : State iota →L[ℝ] State iota) :
    State iota →L[ℝ] State iota :=
  (highGenerator lambda).comp PH - PB.comp (highGenerator lambda)

def pullbackForcing (hT : 0 ≤ T) (PB PH : State iota →L[ℝ] State iota)
    (F : ForcingSpace iota T) : ForcingSpace iota T :=
  PB.compLpL 2 (timeMeasure T) F +
    (pullbackCommutator lambda PB PH).compLpL 2 (timeMeasure T)
      (shiftedHighOperator hT lambda F)

theorem pullbackForcing_coe (hT : 0 ≤ T) (PB PH : State iota →L[ℝ] State iota)
    (F : ForcingSpace iota T) :
    pullbackForcing lambda hT PB PH F =ᵐ[timeMeasure T] fun t =>
      PB (F t) + highGenerator lambda (PH (shiftedHighOperator hT lambda F t)) -
        PB (highGenerator lambda (shiftedHighOperator hT lambda F t)) := by
  filter_upwards [PB.coeFn_compLpL F,
    (pullbackCommutator lambda PB PH).coeFn_compLpL (shiftedHighOperator hT lambda F),
    Lp.coeFn_add (PB.compLpL 2 (timeMeasure T) F)
      ((pullbackCommutator lambda PB PH).compLpL 2 (timeMeasure T)
        (shiftedHighOperator hT lambda F))] with t hP hC hadd
  change (PB.compLpL 2 (timeMeasure T) F +
    (pullbackCommutator lambda PB PH).compLpL 2 (timeMeasure T)
      (shiftedHighOperator hT lambda F)) t = _
  rw [hadd, Pi.add_apply, hP, hC]
  change PB (F t) + (highGenerator lambda (PH (shiftedHighOperator hT lambda F t)) -
    PB (highGenerator lambda (shiftedHighOperator hT lambda F t))) = _
  abel

theorem highGenerator_eq_mul_decode (x : State iota) (i : iota) :
    highGenerator lambda x i = (lambda i : ℝ) * scaleDecode lambda 2 x i := by
  rw [highGenerator_apply, scaleDecode_apply, scaleWeight_two]
  simp only [div_eq_mul_inv, mul_assoc]

theorem highGenerator_shiftedHigh_ae (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    (fun t => highGenerator lambda (shiftedHighOperator hT lambda F t)) =ᵐ[timeMeasure T]
      generatorState lambda F := by
  filter_upwards [scaleDecode_shiftedHigh hT lambda F,
    ae_generatorState_apply_of_memLp hT (Lp.memLp F) lambda] with t hdecode hgen
  apply lp.ext
  funext i
  rw [highGenerator_eq_mul_decode, hdecode, hgen i]


theorem derivative_difference_ae (hT : 0 ≤ T)
    (PB PH : State iota →L[ℝ] State iota)
    (hcompat : ∀ z, PB (scaleDecode lambda 2 z) = scaleDecode lambda 2 (PH z))
    (F : ForcingSpace iota T) :
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      derivativeState lambda (pullbackForcing lambda hT PB PH F) t i -
        PB (derivativeState lambda F t) i =
      -(lambda i : ℝ) * (responseState lambda (pullbackForcing lambda hT PB PH F) t i -
        PB (responseState lambda F t) i) := by
  let G := pullbackForcing lambda hT PB PH F
  filter_upwards [pullbackForcing_coe lambda hT PB PH F,
    highGenerator_shiftedHigh_ae lambda hT F, scaleDecode_shiftedHigh hT lambda F,
    derivativeState_add_generatorState_of_memLp hT (Lp.memLp F) lambda,
    derivativeState_add_generatorState_of_memLp hT (Lp.memLp G) lambda,
    ae_generatorState_apply_of_memLp hT (Lp.memLp G) lambda]
      with t hforce hhigh hdecode hD hDG hGG
  have hforce' : G t = PB (derivativeState lambda F t) +
      highGenerator lambda (PH (shiftedHighOperator hT lambda F t)) := by
    change G t = _ at hforce
    rw [hhigh, ← hD, map_add] at hforce
    exact hforce.trans (by abel)
  have hdiff : derivativeState lambda G t - PB (derivativeState lambda F t) =
      highGenerator lambda (PH (shiftedHighOperator hT lambda F t)) - generatorState lambda G t := by
    rw [eq_sub_of_add_eq hDG, hforce']
    abel
  intro i
  have hscalar := congrArg (fun z : State iota => z i) hdiff
  change derivativeState lambda G t i - PB (derivativeState lambda F t) i =
    highGenerator lambda (PH (shiftedHighOperator hT lambda F t)) i -
      generatorState lambda G t i at hscalar
  rw [highGenerator_eq_mul_decode, ← hcompat, hdecode, hGG i] at hscalar
  exact hscalar.trans (by ring)

private theorem intervalIntegrable_derivative_prefix (hT : 0 ≤ T)
    (F : ForcingSpace iota T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (derivativeState lambda F) volume 0 t := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
    (intervalIntegrable_derivativeState_of_memLp hT (Lp.memLp F) lambda)).mono_set
      (Ioc_subset_Ioc le_rfl ht.2)

private theorem scalar_integral_unique_zero {f : ℝ → ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (c : ℝ)
    (hint : ∀ t ∈ Icc (0 : ℝ) T, f t = ∫ s in (0 : ℝ)..t, c * f s) :
    ∀ t ∈ Icc (0 : ℝ) T, f t = 0 := by
  have hsrc : ContinuousOn (fun t => c * f t) (Icc (0 : ℝ) T) :=
    continuousOn_const.mul hf
  have hvolterra : ∀ t ∈ Icc (0 : ℝ) T,
      f t = volterraPath (0 : ℝ) (fun s => c * f s) t := by
    simpa only [volterraPath, zero_add] using hint
  apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hf
  · intro t ht
    have hd := (hasDerivWithinAt_volterraPath_Icc (x₀ := (0 : ℝ)) hsrc
      (Ico_subset_Icc_self ht)).congr_of_mem hvolterra (Ico_subset_Icc_self ht)
    exact hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · simpa only [intervalIntegral.integral_same] using hint 0 ⟨le_rfl, hT⟩
  · intro t _
    exact le_of_eq (norm_mul c (f t))


theorem response_difference_integral (hT : 0 ≤ T)
    (PB PH : State iota →L[ℝ] State iota)
    (hcompat : ∀ z, PB (scaleDecode lambda 2 z) = scaleDecode lambda 2 (PH z))
    (F : ForcingSpace iota T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : iota) :
    responseState lambda (pullbackForcing lambda hT PB PH F) t i -
        PB (responseState lambda F t) i =
      ∫ s in (0 : ℝ)..t, -(lambda i : ℝ) *
        (responseState lambda (pullbackForcing lambda hT PB PH F) s i -
          PB (responseState lambda F s) i) := by
  let G := pullbackForcing lambda hT PB PH F
  let ev : State iota →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i
  have hDF := intervalIntegrable_derivative_prefix lambda hT F ht
  have hDG := intervalIntegrable_derivative_prefix lambda hT G ht
  have hFscalar : IntervalIntegrable (fun s => PB (derivativeState lambda F s) i) volume 0 t :=
    ⟨(ev.comp PB).integrable_comp hDF.1, (ev.comp PB).integrable_comp hDF.2⟩
  have hGscalar : IntervalIntegrable (fun s => derivativeState lambda G s i) volume 0 t :=
    ⟨ev.integrable_comp hDG.1, ev.integrable_comp hDG.2⟩
  have hFint : PB (responseState lambda F t) i =
      ∫ s in (0 : ℝ)..t, PB (derivativeState lambda F s) i :=
    ((ev.comp PB).intervalIntegral_comp_comm hDF).symm
  have hGint : responseState lambda G t i =
      ∫ s in (0 : ℝ)..t, derivativeState lambda G s i :=
    (ev.intervalIntegral_comp_comm hDG).symm
  rw [hGint, hFint, ← intervalIntegral.integral_sub hGscalar hFscalar]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc le_rfl ht.2) (derivative_difference_ae lambda hT PB PH hcompat F)]
      with s hs
  exact hs i


theorem responseState_pullbackForcing (hT : 0 ≤ T)
    (PB PH : State iota →L[ℝ] State iota)
    (hcompat : ∀ z, PB (scaleDecode lambda 2 z) = scaleDecode lambda 2 (PH z))
    (F : ForcingSpace iota T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    responseState lambda (pullbackForcing lambda hT PB PH F) t =
      PB (responseState lambda F t) := by
  let G := pullbackForcing lambda hT PB PH F
  have hF := continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda
  have hG := continuousOn_responseState_of_memLp hT (Lp.memLp G) lambda
  apply lp.ext
  funext i
  let ev : State iota →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i
  have hw : ContinuousOn (fun s => responseState lambda G s i -
      PB (responseState lambda F s) i) (Icc (0 : ℝ) T) :=
    (ev.continuous.comp_continuousOn hG).sub
      ((ev.comp PB).continuous.comp_continuousOn hF)
  exact sub_eq_zero.mp (scalar_integral_unique_zero hT hw (-(lambda i : ℝ))
    (fun s hs => response_difference_integral lambda hT PB PH hcompat F hs i) t ht)

theorem shiftedHigh_pullbackForcing_ae (hT : 0 ≤ T)
    (PB PH : State iota →L[ℝ] State iota)
    (hcompat : ∀ z, PB (scaleDecode lambda 2 z) = scaleDecode lambda 2 (PH z))
    (F : ForcingSpace iota T) :
    shiftedHighOperator hT lambda (pullbackForcing lambda hT PB PH F) =ᵐ[timeMeasure T]
      fun t => PH (shiftedHighOperator hT lambda F t) := by
  filter_upwards [scaleDecode_shiftedHigh hT lambda (pullbackForcing lambda hT PB PH F),
    scaleDecode_shiftedHigh hT lambda F, ae_restrict_mem measurableSet_Ioc]
      with t hnew hold ht
  apply scaleDecode_injective lambda 2
  rw [hnew, ← hcompat, hold]
  exact responseState_pullbackForcing lambda hT PB PH hcompat F (Ioc_subset_Icc_self ht)

theorem shiftedTrace_pullbackForcing_ae (hT : 0 ≤ T)
    (PB PH : State iota →L[ℝ] State iota)
    (hcompat : ∀ z, PB (scaleDecode lambda 2 z) = scaleDecode lambda 2 (PH z))
    (F : ForcingSpace iota T) :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      shiftedTracePath hT lambda (pullbackForcing lambda hT PB PH F) ⟨t, ht⟩ =
        shiftedBaseMultiplier lambda (PH (shiftedHighOperator hT lambda F t)) := by
  filter_upwards [intermediate_high_eq_trace hT lambda (pullbackForcing lambda hT PB PH F),
    shiftedHigh_pullbackForcing_ae lambda hT PB PH hcompat F] with t htrace hhigh
  intro ht
  exact (htrace ht).symm.trans (congrArg (shiftedBaseMultiplier lambda) hhigh)

end LinearTransport

section NativeTransport

open TensorHilbertNative NativeChartScalarLocalization DeTurckStatePullbackNative ChartMeasureNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0) (L : FiniteChartLocalizationData d.charts)
  (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) {C : ENNReal}
  (hC : C ≠ ⊤) (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure)

def nativePullbackForcing (r : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace d.SymmetricIndex T) : ForcingSpace d.SymmetricIndex T :=
  pullbackForcing d.symmetricParameters hT
    (evenPullback d Phi hC hdom L r) (evenPullback d Phi hC hdom L (r + 1)) F

theorem responseState_nativePullbackForcing (r : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace d.SymmetricIndex T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    responseState d.symmetricParameters (nativePullbackForcing d L Phi hC hdom r hT F) t =
      evenPullback d Phi hC hdom L r (responseState d.symmetricParameters F t) :=
  responseState_pullbackForcing d.symmetricParameters hT
    (evenPullback d Phi hC hdom L r) (evenPullback d Phi hC hdom L (r + 1))
    (evenPullback_scaleDecode_two d L Phi hC hdom r) F ht

theorem shiftedHigh_nativePullbackForcing_ae (r : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace d.SymmetricIndex T) :
    shiftedHighOperator hT d.symmetricParameters
        (nativePullbackForcing d L Phi hC hdom r hT F) =ᵐ[timeMeasure T]
      fun t => evenPullback d Phi hC hdom L (r + 1) (shiftedHighOperator hT d.symmetricParameters F t) :=
  shiftedHigh_pullbackForcing_ae d.symmetricParameters hT
    (evenPullback d Phi hC hdom L r) (evenPullback d Phi hC hdom L (r + 1))
    (evenPullback_scaleDecode_two d L Phi hC hdom r) F

theorem shiftedTrace_nativePullbackForcing_ae (r : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace d.SymmetricIndex T) :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      shiftedTracePath hT d.symmetricParameters
        (nativePullbackForcing d L Phi hC hdom r hT F) ⟨t, ht⟩ =
      shiftedBaseMultiplier d.symmetricParameters
        (evenPullback d Phi hC hdom L (r + 1) (shiftedHighOperator hT d.symmetricParameters F t)) :=
  shiftedTrace_pullbackForcing_ae d.symmetricParameters hT
    (evenPullback d Phi hC hdom L r) (evenPullback d Phi hC hdom L (r + 1))
    (evenPullback_scaleDecode_two d L Phi hC hdom r) F

end NativeTransport

end PoincareConjecture.DeTurckPullbackResponseNative

end
