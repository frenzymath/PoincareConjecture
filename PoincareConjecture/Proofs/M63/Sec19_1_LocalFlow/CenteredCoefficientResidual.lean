import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CenteredCoefficientCutoff
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CenteredSpectralResidual
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas










set_option autoImplicit false

open MeasureTheory Filter

namespace PoincareConjecture.M63

open SpectralHeatNative QuasilinearDeTurckNative

variable {iota E : Type*} [Countable iota]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E]
  [MeasurableSpace (State iota)] [BorelSpace (State iota)]





theorem exists_centeredCoefficientResidual (lambda : iota → NNReal) (w : State iota)
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (a : ℝ → State iota → E) (b : ℝ → State iota → State iota)
    (ha : Continuous (Function.uncurry a)) (hb : Continuous (Function.uncurry b))
    (eps A B : NNReal)
    (hlocal : ∀ᵐ t ∂timeMeasure T,
      ‖a t 0‖ ≤ eps ∧
      (∀ z z', ‖z‖ ≤ r → ‖z'‖ ≤ r → ‖a t z - a t z'‖ ≤ A * ‖z - z'‖) ∧
      (∀ z z', ‖z‖ ≤ r → ‖z'‖ ≤ r → ‖b t z - b t z'‖ ≤ B * ‖z - z'‖))
    (hb0 : MemLp (fun t => b t 0) 2 (timeMeasure T)) :
    ∃ N : CenteredSpectralResidual lambda w T,
      N.perturbationConstant = ‖M‖₊ * eps ∧
      N.principalConstant = 2 * ‖M‖₊ * A ∧
      N.lowerConstant = 2 * B ∧
      ∀ᵐ t ∂timeMeasure T, ∀ x,
        N.toFun t x =
          M (a t (shiftedBaseMultiplier lambda (traceCutoff lambda r x)))
            (initialHeatHigh lambda w t + x) +
          b t (shiftedBaseMultiplier lambda (traceCutoff lambda r x)) ∧
        (‖shiftedBaseMultiplier lambda x‖ ≤ r →
          N.toFun t x = M (a t (shiftedBaseMultiplier lambda x))
            (initialHeatHigh lambda w t + x) + b t (shiftedBaseMultiplier lambda x)) := by
  let C := fun x => shiftedBaseMultiplier lambda (traceCutoff lambda r x)
  have hC : Continuous C :=
    (shiftedBaseMultiplier lambda).continuous.comp (continuous_traceCutoff lambda hr)
  have hP : MemLp (initialHeatHigh lambda w) 2 (timeMeasure T) :=
    (initialHeatHigh_memLp_energy lambda w hT).1
  let P := hP.aestronglyMeasurable.mk (initialHeatHigh lambda w)
  have hPs : StronglyMeasurable P := hP.aestronglyMeasurable.stronglyMeasurable_mk
  have hPeq : initialHeatHigh lambda w =ᵐ[timeMeasure T] P :=
    hP.aestronglyMeasurable.ae_eq_mk
  have hPm : MemLp P 2 (timeMeasure T) := (memLp_congr_ae hPeq).mp hP
  let N := fun t x => M (a t (C x)) (P t + x) + b t (C x)
  have hac : Continuous (fun z : ℝ × State iota => a z.1 (C z.2)) :=
    ha.comp (continuous_fst.prodMk (hC.comp continuous_snd))
  have hbc : Continuous (fun z : ℝ × State iota => b z.1 (C z.2)) :=
    hb.comp (continuous_fst.prodMk (hC.comp continuous_snd))
  have hrem : Continuous (fun z : ℝ × State iota => M (a z.1 (C z.2)) z.2 + b z.1 (C z.2)) :=
    (M.continuous₂.comp (hac.prodMk continuous_snd)).add hbc
  have hbase : StronglyMeasurable (fun z : ℝ × State iota => M (a z.1 (C z.2)) (P z.1)) :=
    M.continuous₂.comp_stronglyMeasurable
      (hac.stronglyMeasurable.prodMk (hPs.comp_measurable measurable_fst))
  have hNm : Measurable (Function.uncurry N) := by
    convert hrem.measurable.add_stronglyMeasurable hbase using 1
    funext z
    change M (a z.1 (C z.2)) (P z.1 + z.2) + b z.1 (C z.2) = _
    simp only [map_add, Pi.add_apply]
    abel
  have ha0 : Continuous (fun t => a t 0) :=
    ha.comp (continuous_id.prodMk continuous_const)
  have hzero : MemLp (fun t => M (a t 0) (P t)) 2 (timeMeasure T) := by
    apply hPm.of_le_mul (c := ‖M‖ * (eps : ℝ)) (M.aestronglyMeasurable_comp₂
      ha0.stronglyMeasurable.aestronglyMeasurable hPm.aestronglyMeasurable)
    filter_upwards [hlocal] with t ht
    calc
      _ ≤ ‖M‖ * ‖a t 0‖ * ‖P t‖ := M.le_opNorm₂ _ _
      _ ≤ (‖M‖ * (eps : ℝ)) * ‖P t‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht.1 (norm_nonneg M)) (norm_nonneg _)
  have hNzero : MemLp (fun t => N t 0) 2 (timeMeasure T) := by
    simp only [N, C, traceCutoff_zero, map_zero, add_zero]
    exact hzero.add hb0
  let R : CenteredSpectralResidual lambda w T := {
    toFun := N
    measurable := hNm
    zero_memLp := hNzero
    perturbationConstant := ‖M‖₊ * eps
    principalConstant := 2 * ‖M‖₊ * A
    lowerConstant := 2 * B
    mixed := by
      filter_upwards [hlocal, hPeq] with t ht hPt
      intro x y
      simpa only [N, C, hPt, NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm] using
        norm_centeredCoefficientCutoff_sub_le lambda hr M (a t) (b t)
          eps.coe_nonneg A.coe_nonneg B.coe_nonneg ht.1 ht.2.1 ht.2.2
          (P t) x y }
  refine ⟨R, rfl, rfl, rfl, ?_⟩
  filter_upwards [hPeq] with t ht
  intro x
  constructor
  · simp only [R, N, C, ht]
  · intro hx
    simp only [R, N, C, ht, traceCutoff_eq_self lambda hr hx]

end PoincareConjecture.M63
