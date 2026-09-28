import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialHeatParameterOperators
import PoincareConjecture.Proofs.M63.Mathlib.CompactPathComposition
import PoincareConjecture.Proofs.M03.Existence.DeTurckMixedForcingNative










set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture.M63

open SpectralHeatNative QuasilinearDeTurckNative TimeL2BilinearNative
  DeTurckMetricProducerNative





theorem exists_contDiff_initialForcing
    {iota E : Type*} [Countable iota] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lambda : iota → NNReal) {T : ℝ} (hT : 0 ≤ T) {k : ℕ∞}
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (G : ℝ × State iota → E) (Q : ℝ × State iota → State iota)
    (hG : ContDiff ℝ k G) (hQ : ContDiff ℝ k Q) :
    ∃ R : State iota × ForcingSpace iota T → ForcingSpace iota T,
      ContDiff ℝ k R ∧ ∀ w F, ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
        R (w, F) t =
          M (G (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
            (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t -
              shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F ⟨t, ht⟩)) +
            Q (t, initialResponseTrace lambda w hT F ⟨t, ht⟩) := by
  obtain ⟨V0, _, hV0⟩ := exists_initialHeatPath_operator lambda hT
  obtain ⟨P, _, hP⟩ := exists_initialHeatHigh_operator lambda hT
  let S := State iota
  let X := State iota × ForcingSpace iota T
  let V : X →L[ℝ] ResponsePath iota T :=
    V0.comp (ContinuousLinearMap.fst ℝ S (ForcingSpace iota T)) +
      (shiftedTraceOperator hT lambda).comp (ContinuousLinearMap.snd ℝ S (ForcingSpace iota T))
  let J := shiftedBaseMultiplier lambda
  let Jp := J.compLeftContinuous ℝ (Icc (0 : ℝ) T)
  let H : X →L[ℝ] ForcingSpace iota T :=
    P.comp (ContinuousLinearMap.fst ℝ S (ForcingSpace iota T)) +
      (shiftedHighOperator hT lambda).comp (ContinuousLinearMap.snd ℝ S (ForcingSpace iota T)) -
      (tracePathL2 hT).comp (Jp.comp V)
  let Z0 : C(Icc (0 : ℝ) T, ℝ × S) :=
    ⟨fun t => ((t : ℝ), 0), continuous_subtype_val.prodMk continuous_const⟩
  let I := (ContinuousLinearMap.inr ℝ ℝ S).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  let Z : X → C(Icc (0 : ℝ) T, ℝ × S) := fun z => Z0 + I (V z)
  have hZ : ContDiff ℝ k Z := contDiff_const.add (I.contDiff.comp V.contDiff)
  let G0 : C(ℝ × S, E) := ⟨G, hG.continuous⟩
  let Q0 : C(ℝ × S, S) := ⟨Q, hQ.continuous⟩
  let A : X → TimePath E T := fun z => G0.comp (Z z)
  let B : X → ResponsePath iota T := fun z => Q0.comp (Z z)
  have hA : ContDiff ℝ k A :=
    (contDiff_postcomp_independent_universes (Icc (0 : ℝ) T) G0 hG).comp hZ
  have hB : ContDiff ℝ k B :=
    (contDiff_postcomp_independent_universes (Icc (0 : ℝ) T) Q0 hQ).comp hZ
  let R : X → ForcingSpace iota T := fun z =>
    productOperator hT M (A z) (H z) + tracePathL2 hT (B z)
  have hR : ContDiff ℝ k R :=
    (((productOperator hT M).contDiff.comp hA).clm_apply H.contDiff).add
      ((tracePathL2 (E := S) hT).contDiff.comp hB)
  have hV (w : S) (F : ForcingSpace iota T) (t : Icc (0 : ℝ) T) :
      V (w, F) t = initialResponseTrace lambda w hT F t := by
    change V0 w t + shiftedTracePath hT lambda F t = _
    rw [hV0]
    rfl
  have hZval (z : X) (t : Icc (0 : ℝ) T) : Z z t = ((t : ℝ), V z t) := by
    change ((t : ℝ) + 0, 0 + V z t) = _
    simp only [add_zero, zero_add]
  refine ⟨R, hR, ?_⟩
  intro w F
  filter_upwards [product_ae_eq_on_interval hT M (A (w, F)) (H (w, F)),
    tracePathL2_ae_eq hT (B (w, F)),
    Lp.coeFn_add (product hT M (A (w, F)) (H (w, F))) (tracePathL2 hT (B (w, F))),
    Lp.coeFn_sub (P w + shiftedHighOperator hT lambda F) (tracePathL2 hT (Jp (V (w, F)))),
    Lp.coeFn_add (P w) (shiftedHighOperator hT lambda F), hP w,
    tracePathL2_ae_eq hT (Jp (V (w, F)))] with t hprod hBval hadd hsub hsum hp hJ
  intro ht
  have hH : H (w, F) t = initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t -
      J (V (w, F) ⟨t, ht⟩) := by
    change (P w + shiftedHighOperator hT lambda F - tracePathL2 hT (Jp (V (w, F)))) t = _
    rw [hsub, Pi.sub_apply, hsum, Pi.add_apply, hp, hJ ht]
    rfl
  change (product hT M (A (w, F)) (H (w, F)) + tracePathL2 hT (B (w, F))) t = _
  rw [hadd, Pi.add_apply, hprod ht, hBval ht, hH]
  change M (G (Z (w, F) ⟨t, ht⟩))
      (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t -
        J (V (w, F) ⟨t, ht⟩)) + Q (Z (w, F) ⟨t, ht⟩) = _
  rw [hZval, hV]

end PoincareConjecture.M63
