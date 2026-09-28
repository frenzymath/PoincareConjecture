import PoincareConjecture.Proofs.M03.Existence.QuasilinearDeTurckNative

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M63

open SpectralHeatNative QuasilinearDeTurckNative

variable {iota : Type*} [Countable iota]
  [MeasurableSpace (State iota)] [BorelSpace (State iota)]

structure TimeDependentSpectralResidual (lambda : iota → NNReal) (T : ℝ) where

  toFun : ℝ → State iota → State iota

  measurable : Measurable (Function.uncurry toFun)

  zero_memLp : MemLp (fun t => toFun t 0) 2 (timeMeasure T)

  perturbationConstant : NNReal

  principalConstant : NNReal

  lowerConstant : NNReal

  mixed : ∀ᵐ t ∂timeMeasure T, ∀ x y,
    ‖toFun t x - toFun t y‖ ≤ (perturbationConstant : ℝ) * ‖x - y‖ +
      (principalConstant : ℝ) *
        (max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ * ‖x - y‖ +
          ‖shiftedBaseMultiplier lambda (x - y)‖ * ‖y‖) +
      (lowerConstant : ℝ) * ‖shiftedBaseMultiplier lambda (x - y)‖

namespace TimeDependentSpectralResidual

variable {lambda : iota → NNReal} {T : ℝ} (N : TimeDependentSpectralResidual lambda T)

omit [BorelSpace (State iota)] in

theorem ae_norm_le : ∀ᵐ t ∂timeMeasure T, ∀ x,
    ‖N.toFun t x‖ ≤
      ((N.perturbationConstant : ℝ) + N.principalConstant * ‖shiftedBaseMultiplier lambda x‖ +
        N.lowerConstant) * ‖x‖ + ‖N.toFun t 0‖ := by
  filter_upwards [N.mixed] with t ht
  intro x
  have h := ht x 0
  simp only [map_zero, norm_zero, max_eq_left (norm_nonneg _), sub_zero,
    mul_zero, add_zero] at h
  have hJ := mul_le_mul_of_nonneg_left (norm_shiftedBaseMultiplier_le lambda x)
    N.lowerConstant.coe_nonneg
  calc
    _ ≤ ‖N.toFun t x - N.toFun t 0‖ + ‖N.toFun t 0‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by nlinarith

theorem memLp_response_source (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    MemLp (fun t => N.toFun t (shiftedHighOperator hT lambda F t)) 2 (timeMeasure T) := by
  let H := shiftedHighOperator hT lambda F
  let C : ℝ := N.perturbationConstant +
    N.principalConstant * ((Real.sqrt T + 1) * ‖F‖) + N.lowerConstant
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmeas : AEMeasurable (fun t => N.toFun t (H t)) (timeMeasure T) :=
    N.measurable.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk (Lp.memLp H).aestronglyMeasurable.aemeasurable)
  have hcoords (i : iota) :
      AEStronglyMeasurable (fun t => N.toFun t (H t) i) (timeMeasure T) :=
    ((lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).continuous.measurable.comp_aemeasurable
      hmeas).aestronglyMeasurable
  have hsm := aestronglyMeasurable_stateOfCoeffs hcoords
    (Eventually.of_forall (fun t => lp.memℓp (N.toFun t (H t))))
  have heq : (fun t => stateOfCoeffs (fun i => N.toFun t (H t) i)) =
      (fun t => N.toFun t (H t)) := by
    funext t
    apply lp.ext
    funext i
    exact stateOfCoeffs_apply (lp.memℓp (N.toFun t (H t))) i
  rw [heq] at hsm
  have hmajor : MemLp (fun t => C * ‖H t‖ + ‖N.toFun t 0‖) 2 (timeMeasure T) :=
    ((Lp.memLp H).norm.const_mul C).add N.zero_memLp.norm
  apply hmajor.of_le hsm
  filter_upwards [N.ae_norm_le, intermediate_high_bound_general hT lambda F] with t hN ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (hN (H t)).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  dsimp only [C]
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left ht N.principalConstant.coe_nonneg)) le_rfl

noncomputable def forcingResidual (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    ForcingSpace iota T :=
  (N.memLp_response_source hT F).toLp (fun t => N.toFun t (shiftedHighOperator hT lambda F t))

theorem forcingResidual_coe (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    N.forcingResidual hT F =ᵐ[timeMeasure T]
      fun t => N.toFun t (shiftedHighOperator hT lambda F t) :=
  (N.memLp_response_source hT F).coeFn_toLp

theorem forcingResidual_zero (hT : 0 ≤ T) :
    N.forcingResidual hT 0 = N.zero_memLp.toLp (fun t => N.toFun t 0) := by
  apply Lp.ext
  have h := N.forcingResidual_coe hT 0
  simp only [map_zero] at h
  filter_upwards [h, N.zero_memLp.coeFn_toLp,
    Lp.coeFn_zero (State iota) 2 (timeMeasure T)] with t ht hzero hz
  simp only [ht, hzero, hz, Pi.zero_apply]

theorem norm_forcingResidual_sub_le (hT : 0 ≤ T) (hT1 : T ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) (F G : ForcingSpace iota T)
    (hF : ‖F‖ ≤ r) (hG : ‖G‖ ≤ r) :
    ‖N.forcingResidual hT F - N.forcingResidual hT G‖ ≤
      (2 * N.perturbationConstant + 8 * N.principalConstant * r +
        2 * N.lowerConstant * Real.sqrt T) * ‖F - G‖ := by
  have hb (U : ForcingSpace iota T) (hU : ‖U‖ ≤ r) :
      ∀ᵐ t ∂timeMeasure T,
        ‖shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda U t)‖ ≤ 2 * r :=
    (intermediate_high_bound hT hT1 lambda U).mono
      (fun _ ht => ht.trans (mul_le_mul_of_nonneg_left hU (by norm_num)))
  let H := shiftedHighOperator hT lambda
  let J := (shiftedBaseMultiplier lambda).compLpL 2 (timeMeasure T)
  have hmain : ‖N.forcingResidual hT F - N.forcingResidual hT G‖ ≤
      ((N.perturbationConstant : ℝ) + N.principalConstant * (2 * r)) * ‖H (F - G)‖ +
      (N.principalConstant : ℝ) * (2 * ‖F - G‖) * ‖H G‖ +
      (N.lowerConstant : ℝ) * ‖J (H (F - G))‖ := by
    apply norm_le_mixed _ _ _ _ (by positivity) (by positivity) N.lowerConstant.coe_nonneg
    filter_upwards [N.forcingResidual_coe hT F, N.forcingResidual_coe hT G,
      Lp.coeFn_sub (N.forcingResidual hT F) (N.forcingResidual hT G),
      Lp.coeFn_sub (H F) (H G), (shiftedBaseMultiplier lambda).coeFn_compLpL (H (F - G)),
      hb F hF, hb G hG, intermediate_high_bound hT hT1 lambda (F - G), N.mixed]
      with t hNF hNG hsubN hsubH hJ hFt hGt hdiff hN
    have hHt : H (F - G) t = H F t - H G t := by rw [map_sub, hsubH, Pi.sub_apply]
    rw [hsubN, Pi.sub_apply, hNF, hNG]
    change ‖N.toFun t (H F t) - N.toFun t (H G t)‖ ≤ _
    have h := hN (H F t) (H G t)
    rw [hHt] at hdiff
    have htop := mul_le_mul_of_nonneg_right (max_le hFt hGt)
      (norm_nonneg (H F t - H G t))
    have hcross := mul_le_mul_of_nonneg_right hdiff (norm_nonneg (H G t))
    apply h.trans
    change _ ≤ _ + _ + (N.lowerConstant : ℝ) * ‖J (H (F - G)) t‖
    rw [hJ, hHt]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add htop hcross)
      N.principalConstant.coe_nonneg]
  have hhigh : ‖H (F - G)‖ ≤ 2 * ‖F - G‖ :=
    (H.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((norm_shiftedHighOperator_le hT lambda).trans
        (by linarith)) (norm_nonneg _))
  have hGhigh : ‖H G‖ ≤ 2 * r :=
    ((H.le_opNorm G).trans (mul_le_mul_of_nonneg_right
      ((norm_shiftedHighOperator_le hT lambda).trans (by linarith)) (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left hG (by norm_num))
  calc
    _ ≤ ((N.perturbationConstant : ℝ) + N.principalConstant * (2 * r)) * ‖H (F - G)‖ +
        (N.principalConstant : ℝ) * (2 * ‖F - G‖) * ‖H G‖ +
        (N.lowerConstant : ℝ) * ‖J (H (F - G))‖ := hmain
    _ ≤ ((N.perturbationConstant : ℝ) + N.principalConstant * (2 * r)) *
          (2 * ‖F - G‖) +
        (N.principalConstant : ℝ) * (2 * ‖F - G‖) * (2 * r) +
        (N.lowerConstant : ℝ) * (2 * Real.sqrt T * ‖F - G‖) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hhigh (by positivity))
        (mul_le_mul_of_nonneg_left hGhigh (by positivity)))
        (mul_le_mul_of_nonneg_left (norm_intermediate_high_le hT hT1 lambda (F - G))
          N.lowerConstant.coe_nonneg)
    _ = _ := by ring

end TimeDependentSpectralResidual
end PoincareConjecture.M63
