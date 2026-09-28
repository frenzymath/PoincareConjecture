import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialSpectralTrace
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TimeDependentSpectralResidual










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M63.TimeDependentSpectralResidual

open SpectralHeatNative QuasilinearDeTurckNative

variable {iota : Type*} [Countable iota]
  [MeasurableSpace (State iota)] [BorelSpace (State iota)]
  {lambda : iota → NNReal} {T : ℝ}
  (N : TimeDependentSpectralResidual lambda T) (w : State iota)




theorem memLp_initial_response_source (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    MemLp (fun t => N.toFun t
      (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t)) 2 (timeMeasure T) := by
  let H := shiftedHighOperator hT lambda F
  let V := fun t => initialHeatHigh lambda w t + H t
  have hV : MemLp V 2 (timeMeasure T) :=
    (initialHeatHigh_memLp_energy lambda w hT).1.add (Lp.memLp H)
  let C : ℝ := N.perturbationConstant +
    N.principalConstant * (‖w‖ + (Real.sqrt T + 1) * ‖F‖) + N.lowerConstant
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmeas : AEMeasurable (fun t => N.toFun t (V t)) (timeMeasure T) :=
    N.measurable.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk hV.aestronglyMeasurable.aemeasurable)
  have hcoords (i : iota) :
      AEStronglyMeasurable (fun t => N.toFun t (V t) i) (timeMeasure T) :=
    ((lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).continuous.measurable.comp_aemeasurable
      hmeas).aestronglyMeasurable
  have hsm := aestronglyMeasurable_stateOfCoeffs hcoords
    (Eventually.of_forall (fun t => lp.memℓp (N.toFun t (V t))))
  have heq : (fun t => stateOfCoeffs (fun i => N.toFun t (V t) i)) =
      (fun t => N.toFun t (V t)) := by
    funext t
    apply lp.ext
    funext i
    exact stateOfCoeffs_apply (lp.memℓp (N.toFun t (V t))) i
  rw [heq] at hsm
  have hmajor : MemLp (fun t => C * ‖V t‖ + ‖N.toFun t 0‖) 2 (timeMeasure T) :=
    (hV.norm.const_mul C).add N.zero_memLp.norm
  apply hmajor.of_le hsm
  filter_upwards [N.ae_norm_le, intermediate_high_bound_general hT lambda F,
    ae_restrict_mem measurableSet_Ioc] with t hN ht hmem
  have htrace : ‖shiftedBaseMultiplier lambda (V t)‖ ≤ ‖w‖ + (Real.sqrt T + 1) * ‖F‖ := by
    rw [show V t = initialHeatHigh lambda w t + H t from rfl, map_add]
    exact (norm_add_le _ _).trans
      (add_le_add (initialHeatHigh_trace lambda w hmem.1).2 ht)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (hN (V t)).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  dsimp only [C]
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left htrace N.principalConstant.coe_nonneg)) le_rfl




noncomputable def initialForcingResidual (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    ForcingSpace iota T :=
  (N.memLp_initial_response_source w hT F).toLp (fun t => N.toFun t
    (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t))



theorem initialForcingResidual_coe (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    N.initialForcingResidual w hT F =ᵐ[timeMeasure T] fun t => N.toFun t
      (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t) :=
  (N.memLp_initial_response_source w hT F).coeFn_toLp




theorem initialForcingResidual_zero (hT : 0 ≤ T) :
    ∃ h : MemLp (fun t => N.toFun t (initialHeatHigh lambda w t)) 2 (timeMeasure T),
      N.initialForcingResidual w hT 0 =
        h.toLp (fun t => N.toFun t (initialHeatHigh lambda w t)) := by
  have heq : (fun t => N.toFun t
      (initialHeatHigh lambda w t + shiftedHighOperator hT lambda (0 : ForcingSpace iota T) t))
      =ᵐ[timeMeasure T] fun t => N.toFun t (initialHeatHigh lambda w t) := by
    simp only [map_zero]
    filter_upwards [Lp.coeFn_zero (State iota) 2 (timeMeasure T)] with t ht
    simp only [ht, Pi.zero_apply, add_zero]
  have hm := (memLp_congr_ae heq).mp (N.memLp_initial_response_source w hT 0)
  refine ⟨hm, Lp.ext ?_⟩
  exact (N.initialForcingResidual_coe w hT 0).trans (heq.trans hm.coeFn_toLp.symm)




theorem norm_initialForcingResidual_sub_le (hT : 0 ≤ T) (hT1 : T ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) (F G : ForcingSpace iota T)
    (hF : ‖F‖ ≤ r) (hG : ‖G‖ ≤ r) :
    let P := (initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)
    ‖N.initialForcingResidual w hT F - N.initialForcingResidual w hT G‖ ≤
      (2 * N.perturbationConstant + 2 * N.principalConstant * ‖w‖ +
        8 * N.principalConstant * r + 2 * N.principalConstant * ‖P‖ +
        2 * N.lowerConstant * Real.sqrt T) * ‖F - G‖ := by
  let P := (initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)
  let H := shiftedHighOperator hT lambda
  let J := (shiftedBaseMultiplier lambda).compLpL 2 (timeMeasure T)
  have hb (U : ForcingSpace iota T) (hU : ‖U‖ ≤ r) :
      ∀ᵐ t ∂timeMeasure T,
        ‖shiftedBaseMultiplier lambda (initialHeatHigh lambda w t + H U t)‖ ≤ ‖w‖ + 2 * r := by
    filter_upwards [intermediate_high_bound hT hT1 lambda U,
      ae_restrict_mem measurableSet_Ioc] with t ht hmem
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (initialHeatHigh_trace lambda w hmem.1).2
      (ht.trans (mul_le_mul_of_nonneg_left hU (by norm_num))))
  have hmain : ‖N.initialForcingResidual w hT F - N.initialForcingResidual w hT G‖ ≤
      ((N.perturbationConstant : ℝ) + N.principalConstant * (‖w‖ + 2 * r)) * ‖H (F - G)‖ +
      (N.principalConstant : ℝ) * (2 * ‖F - G‖) * ‖P + H G‖ +
      (N.lowerConstant : ℝ) * ‖J (H (F - G))‖ := by
    apply norm_le_mixed _ _ _ _ (by positivity) (by positivity) N.lowerConstant.coe_nonneg
    filter_upwards [N.initialForcingResidual_coe w hT F, N.initialForcingResidual_coe w hT G,
      Lp.coeFn_sub (N.initialForcingResidual w hT F) (N.initialForcingResidual w hT G),
      Lp.coeFn_sub (H F) (H G), (shiftedBaseMultiplier lambda).coeFn_compLpL (H (F - G)),
      hb F hF, hb G hG, intermediate_high_bound hT hT1 lambda (F - G), N.mixed,
      (initialHeatHigh_memLp_energy lambda w hT).1.coeFn_toLp, Lp.coeFn_add P (H G)]
      with t hNF hNG hsubN hsubH hJ hFt hGt hdiff hN hP hadd
    have hHt : H (F - G) t = H F t - H G t := by rw [map_sub, hsubH, Pi.sub_apply]
    have hPGt : (P + H G) t = initialHeatHigh lambda w t + H G t := by
      rw [hadd, Pi.add_apply, hP]
    have hVdiff : (initialHeatHigh lambda w t + H F t) -
        (initialHeatHigh lambda w t + H G t) = H F t - H G t := by abel
    rw [hsubN, Pi.sub_apply, hNF, hNG]
    change ‖N.toFun t (initialHeatHigh lambda w t + H F t) -
      N.toFun t (initialHeatHigh lambda w t + H G t)‖ ≤ _
    have h := hN (initialHeatHigh lambda w t + H F t) (initialHeatHigh lambda w t + H G t)
    rw [hVdiff] at h
    rw [hHt] at hdiff
    have htop := mul_le_mul_of_nonneg_right (max_le hFt hGt) (norm_nonneg (H F t - H G t))
    have hcross := mul_le_mul_of_nonneg_right hdiff
      (norm_nonneg (initialHeatHigh lambda w t + H G t))
    apply h.trans
    change _ ≤ _ + (N.principalConstant : ℝ) * (2 * ‖F - G‖) * ‖(P + H G) t‖ +
      (N.lowerConstant : ℝ) * ‖J (H (F - G)) t‖
    rw [hPGt, hJ, hHt]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add htop hcross)
      N.principalConstant.coe_nonneg]
  have hhigh : ‖H (F - G)‖ ≤ 2 * ‖F - G‖ :=
    (H.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((norm_shiftedHighOperator_le hT lambda).trans
        (by linarith)) (norm_nonneg _))
  have hGhigh : ‖P + H G‖ ≤ ‖P‖ + 2 * r := by
    apply (norm_add_le _ _).trans
    apply add_le_add le_rfl
    exact ((H.le_opNorm G).trans (mul_le_mul_of_nonneg_right
      ((norm_shiftedHighOperator_le hT lambda).trans (by linarith)) (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left hG (by norm_num))
  calc
    _ ≤ ((N.perturbationConstant : ℝ) + N.principalConstant * (‖w‖ + 2 * r)) * ‖H (F - G)‖ +
        (N.principalConstant : ℝ) * (2 * ‖F - G‖) * ‖P + H G‖ +
        (N.lowerConstant : ℝ) * ‖J (H (F - G))‖ := hmain
    _ ≤ ((N.perturbationConstant : ℝ) + N.principalConstant * (‖w‖ + 2 * r)) *
          (2 * ‖F - G‖) +
        (N.principalConstant : ℝ) * (2 * ‖F - G‖) * (‖P‖ + 2 * r) +
        (N.lowerConstant : ℝ) * (2 * Real.sqrt T * ‖F - G‖) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hhigh (by positivity))
        (mul_le_mul_of_nonneg_left hGhigh (by positivity)))
        (mul_le_mul_of_nonneg_left (norm_intermediate_high_le hT hT1 lambda (F - G))
          N.lowerConstant.coe_nonneg)
    _ = _ := by ring




theorem norm_initialForcingResidual_zero_le (hT : 0 ≤ T) :
    let P := (initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)
    ‖N.initialForcingResidual w hT 0‖ ≤
      ((N.perturbationConstant : ℝ) + N.principalConstant * ‖w‖ + N.lowerConstant) * ‖P‖ +
        ‖N.zero_memLp.toLp (fun t => N.toFun t 0)‖ := by
  let P := (initialHeatHigh_memLp_energy lambda w hT).1.toLp (initialHeatHigh lambda w)
  let Z := N.zero_memLp.toLp (fun t => N.toFun t 0)
  let C : ℝ := N.perturbationConstant + N.principalConstant * ‖w‖ + N.lowerConstant
  have hmain : ‖N.initialForcingResidual w hT 0‖ ≤
      C * ‖P‖ + 1 * ‖Z‖ + 0 * ‖(0 : ForcingSpace iota T)‖ := by
    apply norm_le_mixed _ _ _ _ (by dsimp [C]; positivity) zero_le_one le_rfl
    have hsource := N.initialForcingResidual_coe w hT 0
    simp only [map_zero] at hsource
    filter_upwards [hsource, (initialHeatHigh_memLp_energy lambda w hT).1.coeFn_toLp,
      N.zero_memLp.coeFn_toLp, Lp.coeFn_zero (State iota) 2 (timeMeasure T),
      N.ae_norm_le, ae_restrict_mem measurableSet_Ioc] with t hR hP hZ hz hN hmem
    change P t = initialHeatHigh lambda w t at hP
    change Z t = N.toFun t 0 at hZ
    simp only [hR, hz, Pi.zero_apply, add_zero, hP, hZ, one_mul, zero_mul]
    apply (hN (initialHeatHigh lambda w t)).trans
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (initialHeatHigh_trace lambda w hmem.1).2
        N.principalConstant.coe_nonneg)) le_rfl
  simpa only [one_mul, zero_mul, add_zero] using hmain

end PoincareConjecture.M63.TimeDependentSpectralResidual
