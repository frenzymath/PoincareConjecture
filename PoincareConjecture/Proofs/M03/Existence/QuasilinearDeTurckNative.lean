import PoincareConjecture.Proofs.M03.Existence.SpectralShiftedNative
import PoincareConjecture.Proofs.M03.Existence.SpectralForcingFixedPointNative
import PoincareConjecture.Proofs.M03.Existence.SpectralScaleNative
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace PoincareConjecture.QuasilinearDeTurckNative

open SpectralHeatNative

variable {iota : Type*} [Countable iota] {T : ℝ}

private theorem norm_l2_norm (F : ForcingSpace iota T) :
    ‖(Lp.memLp F).norm.toLp (fun t => ‖F t‖)‖ = ‖F‖ := by
  rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]

theorem norm_le_mixed (F G H K : ForcingSpace iota T) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : ∀ᵐ t ∂timeMeasure T,
      ‖F t‖ ≤ a * ‖G t‖ + b * ‖H t‖ + c * ‖K t‖) :
    ‖F‖ ≤ a * ‖G‖ + b * ‖H‖ + c * ‖K‖ := by
  let g : Lp ℝ 2 (timeMeasure T) := (Lp.memLp G).norm.toLp (fun t => ‖G t‖)
  let h' : Lp ℝ 2 (timeMeasure T) := (Lp.memLp H).norm.toLp (fun t => ‖H t‖)
  let k : Lp ℝ 2 (timeMeasure T) := (Lp.memLp K).norm.toLp (fun t => ‖K t‖)
  have hg : g =ᵐ[timeMeasure T] fun t => ‖G t‖ := (Lp.memLp G).norm.coeFn_toLp
  have hh : h' =ᵐ[timeMeasure T] fun t => ‖H t‖ := (Lp.memLp H).norm.coeFn_toLp
  have hk : k =ᵐ[timeMeasure T] fun t => ‖K t‖ := (Lp.memLp K).norm.coeFn_toLp
  have hdom : ‖F‖ ≤ ‖a • g + b • h' + c • k‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h, hg, hh, hk, Lp.coeFn_smul a g, Lp.coeFn_smul b h',
      Lp.coeFn_smul c k, Lp.coeFn_add (a • g) (b • h'),
      Lp.coeFn_add (a • g + b • h') (c • k)]
      with t ht hgt hht hkt hat hbt hct hab habc
    simp only [habc, Pi.add_apply, hab, hat, hbt, hct, Pi.smul_apply,
      hgt, hht, hkt, smul_eq_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact ht
  calc
    ‖F‖ ≤ ‖a • g + b • h' + c • k‖ := hdom
    _ ≤ ‖a • g‖ + ‖b • h'‖ + ‖c • k‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = a * ‖G‖ + b * ‖H‖ + c * ‖K‖ := by
      rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg hc,
        norm_l2_norm, norm_l2_norm, norm_l2_norm]

theorem norm_le_sqrt_time (hT : 0 ≤ T) (F : ForcingSpace iota T) {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ C) :
    ‖F‖ ≤ Real.sqrt T * C := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hC)).mp
  rw [forcing_norm_sq, mul_pow, Real.sq_sqrt hT]
  calc
    _ ≤ ∫ _t, C ^ 2 ∂timeMeasure T := by
      apply integral_mono_ae
        ((memLp_two_iff_integrable_sq_norm (Lp.memLp F).aestronglyMeasurable).mp
          (Lp.memLp F)) (integrable_const _)
      filter_upwards [hF] with t ht
      exact (sq_le_sq₀ (norm_nonneg _) hC).mpr ht
    _ = _ := by
      simp [timeMeasure, integral_const, Measure.real, Real.volume_Ioc,
        ENNReal.toReal_ofReal hT, smul_eq_mul]

theorem intermediate_high_eq_trace (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda F t) =
        shiftedTracePath hT lambda F ⟨t, ht⟩ := by
  filter_upwards [shiftedHighOperator_coeff hT lambda F] with t ht
  intro hmem
  apply lp.ext
  funext i
  change 1 / Real.sqrt (1 + (lambda i : ℝ)) *
    shiftedHighOperator hT lambda F t i = _
  rw [ht, shiftedTracePath_coeff]
  have hp : 0 < 1 + (lambda i : ℝ) := by positivity
  have hz : Real.sqrt (1 + (lambda i : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  field_simp
  rw [Real.sq_sqrt hp.le]

theorem intermediate_high_bound_general (hT : 0 ≤ T)
    (lambda : iota → NNReal) (F : ForcingSpace iota T) :
    ∀ᵐ t ∂timeMeasure T,
      ‖shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda F t)‖ ≤
        (Real.sqrt T + 1) * ‖F‖ := by
  filter_upwards [intermediate_high_eq_trace hT lambda F,
    ae_restrict_mem measurableSet_Ioc] with t ht hmem
  rw [ht (Ioc_subset_Icc_self hmem)]
  exact (ContinuousMap.norm_coe_le_norm _ _).trans (norm_shiftedTracePath_le hT lambda F)

theorem intermediate_high_bound (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (lambda : iota → NNReal) (F : ForcingSpace iota T) :
    ∀ᵐ t ∂timeMeasure T,
      ‖shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda F t)‖ ≤ 2 * ‖F‖ := by
  filter_upwards [intermediate_high_eq_trace hT lambda F,
    ae_restrict_mem measurableSet_Ioc] with t ht hmem
  rw [ht (Ioc_subset_Icc_self hmem)]
  calc
    _ ≤ ‖shiftedTracePath hT lambda F‖ := ContinuousMap.norm_coe_le_norm _ _
    _ ≤ (Real.sqrt T + 1) * ‖F‖ := norm_shiftedTracePath_le hT lambda F
    _ ≤ 2 * ‖F‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hs : Real.sqrt T ≤ 1 := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT1
      linarith

theorem norm_intermediate_high_le (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (lambda : iota → NNReal) (F : ForcingSpace iota T) :
    ‖(shiftedBaseMultiplier lambda).compLpL 2 (timeMeasure T)
      (shiftedHighOperator hT lambda F)‖ ≤ 2 * Real.sqrt T * ‖F‖ := by
  have h := norm_le_sqrt_time hT
    ((shiftedBaseMultiplier lambda).compLpL 2 (timeMeasure T)
      (shiftedHighOperator hT lambda F)) (by positivity : 0 ≤ 2 * ‖F‖) (by
        filter_upwards [(shiftedBaseMultiplier lambda).coeFn_compLpL
          (shiftedHighOperator hT lambda F), intermediate_high_bound hT hT1 lambda F]
          with t ht hbound
        rwa [ht])
  simpa only [mul_left_comm, mul_assoc] using h

def finiteHigh (lambda : iota → NNReal) (s : Finset iota) : State iota →L[ℝ] State iota := by
  classical
  have hsum : 0 ≤ ∑ i ∈ s, (1 + (lambda i : ℝ)) :=
    Finset.sum_nonneg (fun i _ => by positivity)
  exact multiplier (fun i => if i ∈ s then 1 + (lambda i : ℝ) else 0)
    (∑ i ∈ s, (1 + (lambda i : ℝ))) hsum (fun i => by
      split_ifs with hi
      · rw [abs_of_nonneg (by positivity)]
        exact Finset.single_le_sum (f := fun j => 1 + (lambda j : ℝ))
          (fun j _ => by positivity) hi
      · simpa only [abs_zero] using hsum)

theorem finiteHigh_apply (lambda : iota → NNReal) (s : Finset iota)
    (u : State iota) (i : iota) :
    finiteHigh lambda s u i = if i ∈ s then (1 + (lambda i : ℝ)) * u i else 0 := by
  classical
  simp only [finiteHigh, multiplier_apply, ite_mul, zero_mul]

theorem high_eq_finiteHigh_response (hT : 0 ≤ T) (lambda : iota → NNReal)
    (s : Finset iota) (F : ForcingSpace iota T) (hF : forcingProjection s F = F) :
    shiftedHighOperator hT lambda F =ᵐ[timeMeasure T]
      fun t => finiteHigh lambda s (responseState lambda F t) := by
  classical
  filter_upwards [shiftedHighOperator_coeff hT lambda F,
    ae_restrict_mem measurableSet_Ioc] with t ht hmem
  apply lp.ext
  funext i
  rw [ht, finiteHigh_apply]
  split_ifs with hi
  · rfl
  · rw [responseState_eq_zero_of_forcingProjection lambda s F hF
      (Ioc_subset_Icc_self hmem) hi, mul_zero]

theorem finiteProjection_response_eq (lambda : iota → NNReal)
    (s : Finset iota) (F : ForcingSpace iota T) (hF : forcingProjection s F = F)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    finiteProjection s (responseState lambda F t) = responseState lambda F t := by
  apply lp.ext
  funext i
  rw [finiteProjection_apply]
  split_ifs with hi
  · rfl
  · exact (responseState_eq_zero_of_forcingProjection lambda s F hF ht hi).symm

theorem intermediate_finiteHigh_response (hT : 0 ≤ T) (lambda : iota → NNReal)
    (s : Finset iota) (F : ForcingSpace iota T) (hF : forcingProjection s F = F)
    (t : Icc (0 : ℝ) T) :
    shiftedBaseMultiplier lambda (finiteHigh lambda s (responseState lambda F t)) =
      shiftedTracePath hT lambda F t := by
  apply lp.ext
  funext i
  change 1 / Real.sqrt (1 + (lambda i : ℝ)) *
    finiteHigh lambda s (responseState lambda F t) i = _
  rw [finiteHigh_apply, shiftedTracePath_coeff]
  split_ifs with hi
  · have hp : 0 < 1 + (lambda i : ℝ) := by positivity
    have hz : Real.sqrt (1 + (lambda i : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    field_simp
    rw [Real.sq_sqrt hp.le]
  · rw [responseState_eq_zero_of_forcingProjection lambda s F hF t.property hi,
      mul_zero, mul_zero]

theorem norm_intermediate_finiteHigh_response_le (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (lambda : iota → NNReal) (s : Finset iota) (F : ForcingSpace iota T)
    (hF : forcingProjection s F = F) (t : Icc (0 : ℝ) T) :
    ‖shiftedBaseMultiplier lambda (finiteHigh lambda s (responseState lambda F t))‖ ≤
      2 * ‖F‖ := by
  rw [intermediate_finiteHigh_response hT lambda s F hF t]
  apply ((ContinuousMap.norm_coe_le_norm _ _).trans
    (norm_shiftedTracePath_le hT lambda F)).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hs : Real.sqrt T ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT1
  linarith

structure SpatialResidual (lambda : iota → NNReal) where
  toFun : State iota → State iota
  continuous : Continuous toFun
  principalConstant : NNReal
  lowerConstant : NNReal
  mixed : ∀ x y, ‖toFun x - toFun y‖ ≤
    (principalConstant : ℝ) *
      (max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ * ‖x - y‖ +
        ‖shiftedBaseMultiplier lambda (x - y)‖ * ‖y‖) +
      (lowerConstant : ℝ) * ‖shiftedBaseMultiplier lambda (x - y)‖

namespace SpatialResidual

variable {lambda : iota → NNReal} (N : SpatialResidual lambda)

theorem norm_le (x : State iota) :
    ‖N.toFun x‖ ≤
      ((N.principalConstant : ℝ) * ‖shiftedBaseMultiplier lambda x‖ + N.lowerConstant) *
        ‖x‖ + ‖N.toFun 0‖ := by
  have h := N.mixed x 0
  simp only [map_zero, norm_zero, max_eq_left (norm_nonneg _), sub_zero,
    mul_zero, add_zero] at h
  calc
    _ ≤ ‖N.toFun x - N.toFun 0‖ + ‖N.toFun 0‖ := norm_le_norm_sub_add _ _
    _ ≤ ((N.principalConstant : ℝ) * ‖shiftedBaseMultiplier lambda x‖ * ‖x‖ +
        (N.lowerConstant : ℝ) * ‖x‖) + ‖N.toFun 0‖ := by
      apply add_le_add_left
      apply h.trans
      exact add_le_add (le_of_eq (mul_assoc _ _ _).symm) (mul_le_mul_of_nonneg_left
        (norm_shiftedBaseMultiplier_le lambda x) N.lowerConstant.coe_nonneg)
    _ = _ := by ring

theorem memLp_response_source (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    MemLp (fun t => N.toFun (shiftedHighOperator hT lambda F t)) 2 (timeMeasure T) := by
  let H := shiftedHighOperator hT lambda F
  let B : ℝ := N.principalConstant * ((Real.sqrt T + 1) * ‖F‖) + N.lowerConstant
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajor : MemLp (fun t => B * ‖H t‖ + ‖N.toFun 0‖) 2 (timeMeasure T) :=
    ((Lp.memLp H).norm.const_mul B).add (memLp_const _)
  apply hmajor.of_le (N.continuous.comp_aestronglyMeasurable (Lp.memLp H).aestronglyMeasurable)
  filter_upwards [intermediate_high_bound_general hT lambda F] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (N.norm_le (H t)).trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact add_le_add_left (mul_le_mul_of_nonneg_left ht N.principalConstant.coe_nonneg) _

def forcingResidual (hT : 0 ≤ T) (F : ForcingSpace iota T) : ForcingSpace iota T :=
  (N.memLp_response_source hT F).toLp (fun t => N.toFun (shiftedHighOperator hT lambda F t))

theorem forcingResidual_coe (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    N.forcingResidual hT F =ᵐ[timeMeasure T]
      fun t => N.toFun (shiftedHighOperator hT lambda F t) :=
  (N.memLp_response_source hT F).coeFn_toLp

theorem norm_forcingResidual_zero_le (hT : 0 ≤ T) :
    ‖N.forcingResidual hT 0‖ ≤ Real.sqrt T * ‖N.toFun 0‖ := by
  apply norm_le_sqrt_time hT _ (norm_nonneg _)
  have h := N.forcingResidual_coe hT 0
  simp only [map_zero] at h
  filter_upwards [h, Lp.coeFn_zero (State iota) 2 (timeMeasure T)] with t ht hz
  simp only [ht, hz, Pi.zero_apply, le_refl]

theorem norm_forcingResidual_sub_le (hT : 0 ≤ T) (hT1 : T ≤ 1)
    {r : ℝ} (hr : 0 ≤ r)
    (F G : ForcingSpace iota T) (hF : ‖F‖ ≤ r) (hG : ‖G‖ ≤ r) :
    ‖N.forcingResidual hT F - N.forcingResidual hT G‖ ≤
      (8 * N.principalConstant * r + 2 * N.lowerConstant * Real.sqrt T) * ‖F - G‖ := by
  have hb (H : ForcingSpace iota T) (hH : ‖H‖ ≤ r) :
      ∀ᵐ t ∂timeMeasure T,
        ‖shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda H t)‖ ≤ 2 * r :=
    (intermediate_high_bound hT hT1 lambda H).mono
      (fun _ ht => ht.trans (mul_le_mul_of_nonneg_left hH (by norm_num)))
  let A := shiftedHighOperator hT lambda
  let J := (shiftedBaseMultiplier lambda).compLpL 2 (timeMeasure T)
  have hmain : ‖N.forcingResidual hT F - N.forcingResidual hT G‖ ≤
      (N.principalConstant : ℝ) * (2 * r) * ‖A (F - G)‖ +
      (N.principalConstant : ℝ) * (2 * ‖F - G‖) * ‖A G‖ +
      (N.lowerConstant : ℝ) * ‖J (A (F - G))‖ := by
    apply norm_le_mixed _ _ _ _ (by positivity) (by positivity) N.lowerConstant.coe_nonneg
    filter_upwards [N.forcingResidual_coe hT F, N.forcingResidual_coe hT G,
      Lp.coeFn_sub (N.forcingResidual hT F) (N.forcingResidual hT G),
      Lp.coeFn_sub (A F) (A G), (shiftedBaseMultiplier lambda).coeFn_compLpL (A (F - G)),
      hb F hF, hb G hG, intermediate_high_bound hT hT1 lambda (F - G)]
      with t hNF hNG hsubN hsubA hJ hFt hGt hdiff
    have hAt : A (F - G) t = A F t - A G t := by rw [map_sub, hsubA, Pi.sub_apply]
    rw [hsubN, Pi.sub_apply, hNF, hNG]
    change ‖N.toFun (A F t) - N.toFun (A G t)‖ ≤ _
    have h := N.mixed (A F t) (A G t)
    rw [hAt] at hdiff
    have htop := mul_le_mul_of_nonneg_right (max_le hFt hGt)
      (norm_nonneg (A F t - A G t))
    have hcross := mul_le_mul_of_nonneg_right hdiff (norm_nonneg (A G t))
    apply h.trans
    change _ ≤ _ + _ + (N.lowerConstant : ℝ) * ‖J (A (F - G)) t‖
    rw [hJ, hAt]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add htop hcross)
      N.principalConstant.coe_nonneg]
  have hhigh : ‖shiftedHighOperator hT lambda (F - G)‖ ≤ 2 * ‖F - G‖ :=
    ((shiftedHighOperator hT lambda).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((norm_shiftedHighOperator_le hT lambda).trans
        (by linarith)) (norm_nonneg _))
  have hGhigh : ‖A G‖ ≤ 2 * r :=
    ((A.le_opNorm G).trans (mul_le_mul_of_nonneg_right
      ((norm_shiftedHighOperator_le hT lambda).trans (by linarith)) (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left hG (by norm_num))
  calc
    _ ≤ N.principalConstant * (2 * r) * ‖shiftedHighOperator hT lambda (F - G)‖ +
        N.principalConstant * (2 * ‖F - G‖) * ‖A G‖ +
        N.lowerConstant * ‖(shiftedBaseMultiplier lambda).compLpL 2 (timeMeasure T)
          (shiftedHighOperator hT lambda (F - G))‖ := hmain
    _ ≤ N.principalConstant * (2 * r) * (2 * ‖F - G‖) +
        N.principalConstant * (2 * ‖F - G‖) * (2 * r) +
        N.lowerConstant * (2 * Real.sqrt T * ‖F - G‖) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hhigh (by positivity))
        (mul_le_mul_of_nonneg_left hGhigh (by positivity)))
        (mul_le_mul_of_nonneg_left (norm_intermediate_high_le hT hT1 lambda (F - G))
          N.lowerConstant.coe_nonneg)
    _ = _ := by ring

def forcingRadius : ℝ := 1 / (64 * ((N.principalConstant : ℝ) + 1))

theorem forcingRadius_pos : 0 < N.forcingRadius := by
  unfold forcingRadius
  positivity

theorem exists_strict_forcing_interval :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧
      ‖N.forcingResidual hT.le 0‖ ≤ N.forcingRadius / 4 ∧
      ∀ F G : ForcingSpace iota T, ‖F‖ ≤ N.forcingRadius → ‖G‖ ≤ N.forcingRadius →
        ‖N.forcingResidual hT.le F - N.forcingResidual hT.le G‖ ≤
          ((1 / 4 : NNReal) : ℝ) * ‖F - G‖ := by
  let C1 : ℝ := N.principalConstant
  let C2 : ℝ := N.lowerConstant
  have hC1 : 0 ≤ C1 := N.principalConstant.coe_nonneg
  have hC2 : 0 ≤ C2 := N.lowerConstant.coe_nonneg
  let r := N.forcingRadius
  have hr : 0 < r := N.forcingRadius_pos
  let s := min 1 (min (1 / (16 * (C2 + 1))) (r / (4 * (‖N.toFun 0‖ + 1))))
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsC : s ≤ 1 / (16 * (C2 + 1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hsz : s ≤ r / (4 * (‖N.toFun 0‖ + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  let T := s ^ 2
  have hT : 0 < T := sq_pos_of_pos hs
  have hT1 : T ≤ 1 := by dsimp [T]; nlinarith
  have hroot : Real.sqrt T = s := Real.sqrt_sq hs.le
  have hrad : (64 * (C1 + 1)) * r = 1 := by
    dsimp [r, forcingRadius, C1]
    exact mul_one_div_cancel (by positivity)
  have hsmall1 : 8 * C1 * r ≤ 1 / 8 := by nlinarith
  have hsmall2 : 2 * C2 * Real.sqrt T ≤ 1 / 8 := by
    rw [hroot]
    have h := (le_div_iff₀ (by positivity : 0 < 16 * (C2 + 1))).mp hsC
    nlinarith
  have hsmallz : Real.sqrt T * ‖N.toFun 0‖ ≤ r / 4 := by
    rw [hroot]
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (‖N.toFun 0‖ + 1))).mp hsz
    nlinarith
  have hzero : ‖N.forcingResidual hT.le 0‖ ≤ r / 4 :=
    (N.norm_forcingResidual_zero_le hT.le).trans hsmallz
  have hLip (F G : ForcingSpace iota T) (hF : ‖F‖ ≤ r) (hG : ‖G‖ ≤ r) :
      ‖N.forcingResidual hT.le F - N.forcingResidual hT.le G‖ ≤
        ((1 / 4 : NNReal) : ℝ) * ‖F - G‖ := by
    apply (N.norm_forcingResidual_sub_le hT.le hT1 hr.le F G hF hG).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    norm_num
    linarith
  exact ⟨T, hT, hT1, hzero, hLip⟩

theorem exists_forcing_interval :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧
      ‖N.forcingResidual hT.le 0‖ ≤ (1 - ((1 / 2 : NNReal) : ℝ)) * N.forcingRadius ∧
      ∀ F G : ForcingSpace iota T, ‖F‖ ≤ N.forcingRadius → ‖G‖ ≤ N.forcingRadius →
        ‖N.forcingResidual hT.le F - N.forcingResidual hT.le G‖ ≤
          ((1 / 2 : NNReal) : ℝ) * ‖F - G‖ := by
  obtain ⟨T, hT, hT1, hzero, hLip⟩ := N.exists_strict_forcing_interval
  refine ⟨T, hT, hT1, hzero.trans ?_, ?_⟩
  · norm_num
    linarith [N.forcingRadius_pos]
  · intro F G hF hG
    exact (hLip F G hF hG).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))

theorem exists_strict_forcing_fixedPoint :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace iota T,
      N.forcingResidual hT.le F = F ∧ ‖F‖ ≤ N.forcingRadius / 3 ∧
      ‖F‖ < N.forcingRadius ∧
      ∀ G H : ForcingSpace iota T, ‖G‖ ≤ N.forcingRadius → ‖H‖ ≤ N.forcingRadius →
        ‖N.forcingResidual hT.le G - N.forcingResidual hT.le H‖ ≤
          ((1 / 4 : NNReal) : ℝ) * ‖G - H‖ := by
  obtain ⟨T, hT, hT1, hzero, hLip⟩ := N.exists_strict_forcing_interval
  have hr := N.forcingRadius_pos
  have hzero' : ‖N.forcingResidual hT.le 0‖ ≤
      (1 - ((1 / 4 : NNReal) : ℝ)) * N.forcingRadius := by
    norm_num
    linarith
  obtain ⟨F, hF, hfix, _, _⟩ := exists_forcing_fixedPoint
    (N.forcingResidual hT.le) hr.le (by norm_num : (1 / 4 : NNReal) < 1)
      hzero' hLip
  have hbound := hLip F 0 hF (by simpa using hr.le)
  rw [hfix, sub_zero] at hbound
  have hnorm := norm_le_norm_sub_add F (N.forcingResidual hT.le 0)
  have hthird : ‖F‖ ≤ N.forcingRadius / 3 := by
    norm_num at hbound
    linarith
  exact ⟨T, hT, hT1, F, hfix, hthird, by linarith, hLip⟩

theorem exists_quasilinear_response :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace iota T,
      ‖F‖ ≤ N.forcingRadius ∧ N.forcingResidual hT.le F = F ∧
      responseState lambda F 0 = 0 ∧
      ContinuousOn (responseState lambda F) (Icc (0 : ℝ) T) ∧
      MemLp (derivativeState lambda F) 2 (timeMeasure T) ∧
      MemLp (generatorState lambda F) 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T,
        HasDerivAt (responseState lambda F) (derivativeState lambda F t) t) ∧
      (∀ᵐ t ∂timeMeasure T,
        derivativeState lambda F t + generatorState lambda F t =
          N.toFun (shiftedHighOperator hT.le lambda F t)) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i,
        generatorState lambda F t i = (lambda i : ℝ) * responseState lambda F t i) ∧
      (∫ t, ‖derivativeState lambda F t‖ ^ 2 ∂timeMeasure T) +
        (∫ t, ‖generatorState lambda F t‖ ^ 2 ∂timeMeasure T) ≤
          N.forcingRadius ^ 2 := by
  obtain ⟨T, hT, hT1, hzero, hLip⟩ := N.exists_forcing_interval
  have hr := N.forcingRadius_pos
  obtain ⟨F, hF, hfix, _, _⟩ := exists_forcing_fixedPoint
    (N.forcingResidual hT.le) hr.le (by norm_num : (1 / 2 : NNReal) < 1)
      hzero hLip
  refine ⟨T, hT, hT1, F, hF, hfix, responseState_zero lambda F,
    continuousOn_responseState_of_memLp hT.le (Lp.memLp F) lambda,
    memLp_derivativeState_of_memLp hT.le (Lp.memLp F) lambda,
    memLp_generatorState_of_memLp hT.le (Lp.memLp F) lambda,
    ae_hasDerivAt_responseState_of_memLp hT.le (Lp.memLp F) lambda, ?_,
    ae_generatorState_apply_of_memLp hT.le (Lp.memLp F) lambda, ?_⟩
  · have hsource := N.forcingResidual_coe hT.le F
    rw [hfix] at hsource
    filter_upwards [derivativeState_add_generatorState_of_memLp hT.le (Lp.memLp F) lambda,
      hsource] with t heq hsrc
    exact heq.trans hsrc
  · calc
      _ ≤ ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T :=
        integral_response_energy_le_of_memLp hT.le (Lp.memLp F) lambda
      _ = ‖F‖ ^ 2 := (forcing_norm_sq F).symm
      _ ≤ N.forcingRadius ^ 2 := (sq_le_sq₀ (norm_nonneg _) hr.le).mpr hF

theorem exists_projected_responses (s : ℕ → Finset iota) (hs : Tendsto s atTop atTop) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧
      ∃ (F : ForcingSpace iota T) (G : ℕ → ForcingSpace iota T),
        ‖F‖ ≤ N.forcingRadius ∧ N.forcingResidual hT.le F = F ∧
        (∀ k, ‖G k‖ ≤ N.forcingRadius ∧
          forcingProjection (s k) (N.forcingResidual hT.le (G k)) = G k ∧
          forcingProjection (s k) (G k) = G k) ∧
        Tendsto G atTop (𝓝 F) ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
          Tendsto (fun k => responseState lambda (G k) t i) atTop
            (𝓝 (responseState lambda F t i)) := by
  obtain ⟨T, hT, hT1, hzero, hLip⟩ := N.exists_forcing_interval
  obtain ⟨F, G, hF, hfix, hG, _, hlim⟩ := exists_projected_forcing_fixedPoints
    (N.forcingResidual hT.le) N.forcingRadius_pos.le
      (by norm_num : (1 / 2 : NNReal) < 1) hzero hLip s hs
  exact ⟨T, hT, hT1, F, G, hF, hfix, hG, hlim,
    fun t ht i => tendsto_responseState_coeff_of_forcing hT.le lambda hlim ht i⟩

theorem projected_response_derivative (hT : 0 ≤ T) (s : Finset iota)
    (F : ForcingSpace iota T)
    (hfix : forcingProjection s (N.forcingResidual hT F) = F)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) {i : iota} (hi : i ∈ s) :
    HasDerivWithinAt (fun r => responseState lambda F r i)
      (N.toFun (finiteHigh lambda s (responseState lambda F t)) i -
        (lambda i : ℝ) * responseState lambda F t i) (Ici t) t := by
  have hsupp : forcingProjection s F = F := by rw [← hfix, forcingProjection_idempotent]
  apply projected_response_hasDerivWithinAt lambda s
    (fun u => N.toFun (finiteHigh lambda s u))
    (N.continuous.comp ((finiteHigh lambda s).continuous.comp (finiteProjection s).continuous))
    F (N.forcingResidual hT F) hfix ?_ ht hi
  filter_upwards [N.forcingResidual_coe hT F,
    high_eq_finiteHigh_response hT lambda s F hsupp] with r hr hhigh
  rw [hr, hhigh]

theorem exists_response_all_mass (s : ℕ → Finset iota) (hs : Tendsto s atTop atTop)
    {theta : ℝ} (htheta : theta ≤ 1)
    (hseed : ∀ k, InScale lambda k (N.toFun 0))
    (henergy : ∀ k, ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : Finset iota) (u : State iota),
      finiteProjection q u = u →
      ‖shiftedBaseMultiplier lambda (finiteHigh lambda q u)‖ ≤ 2 * N.forcingRadius →
      finiteWeightedEnergy lambda q k
        (fun i => N.toFun (finiteHigh lambda q u) i - N.toFun 0 i) ≤
        theta * finiteWeightedEnergy lambda q (k + 2) u +
          A * finiteWeightedEnergy lambda q (k + 1) u) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace iota T,
      ‖F‖ ≤ N.forcingRadius ∧ N.forcingResidual hT.le F = F ∧
      ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T,
        Summable (fun i => (1 + (lambda i : ℝ)) ^ (k + 1) *
          responseState lambda F t i ^ 2) ∧
        (∑' i, (1 + (lambda i : ℝ)) ^ (k + 1) *
          responseState lambda F t i ^ 2) ≤ B := by
  obtain ⟨T, hT, hT1, F, G, hF, hfix, hG, _, hlim⟩ := N.exists_projected_responses s hs
  refine ⟨T, hT, hT1, F, hF, hfix, ?_⟩
  intro k
  obtain ⟨A, hA, hAenergy⟩ := henergy k
  let S : ℝ := ‖scaleEncode lambda (k + 1) (N.toFun 0) (hseed (k + 1))‖ ^ 2
  have hS : 0 ≤ S := sq_nonneg _
  have hseedBound (j : ℕ) : finiteWeightedEnergy lambda (s j) (k + 1) (N.toFun 0) ≤ S := by
    dsimp [S, finiteWeightedEnergy]
    rw [norm_scaleEncode_sq_eq_mass]
    exact Summable.sum_le_tsum _ (fun i _ => by positivity)
      ((inScale_iff_summable_weighted_sq lambda (k + 1) (N.toFun 0)).mp (hseed (k + 1)))
  have hcont (j : ℕ) (i : iota) :
      ContinuousOn (fun t => responseState lambda (G j) t i) (Icc (0 : ℝ) T) :=
    (lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).continuous.comp_continuousOn
      (continuousOn_responseState_of_memLp hT.le (Lp.memLp (G j)) lambda)
  have hbound := weighted_sq_mass_le_of_galerkin lambda s hs k hT.le htheta hA hS
    (le_refl (0 : ℝ))
    (fun j t i => responseState lambda (G j) t i)
    (fun j t i => N.toFun (finiteHigh lambda (s j) (responseState lambda (G j) t)) i)
    (N.toFun 0) (fun t i => responseState lambda F t i)
    (fun j i _ => hcont j i)
    (fun j t ht i hi => N.projected_response_derivative hT.le (s j) (G j)
      (hG j).2.1 ht hi)
    (fun j t ht => hAenergy (s j) (responseState lambda (G j) t)
      (finiteProjection_response_eq lambda (s j) (G j) (hG j).2.2
        (Ico_subset_Icc_self ht))
      ((norm_intermediate_finiteHigh_response_le hT.le hT1 lambda (s j) (G j)
        (hG j).2.2 ⟨t, Ico_subset_Icc_self ht⟩).trans
          (mul_le_mul_of_nonneg_left (hG j).1 (by norm_num))))
    hseedBound
    (fun j => by simp [responseState_zero, finiteWeightedEnergy]) hlim
  refine ⟨gronwallBound 0 (3 + A) S T, ?_, hbound⟩
  exact (tsum_nonneg (fun i => by positivity)).trans
    (hbound 0 ⟨le_rfl, hT.le⟩).2

theorem exists_response_all_scale_paths (s : ℕ → Finset iota)
    (hs : Tendsto s atTop atTop) {theta : ℝ} (htheta : theta ≤ 1)
    (hseed : ∀ k, InScale lambda k (N.toFun 0))
    (henergy : ∀ k, ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : Finset iota) (u : State iota),
      finiteProjection q u = u →
      ‖shiftedBaseMultiplier lambda (finiteHigh lambda q u)‖ ≤ 2 * N.forcingRadius →
      finiteWeightedEnergy lambda q k
        (fun i => N.toFun (finiteHigh lambda q u) i - N.toFun 0 i) ≤
        theta * finiteWeightedEnergy lambda q (k + 2) u +
          A * finiteWeightedEnergy lambda q (k + 1) u) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace iota T,
      ‖F‖ ≤ N.forcingRadius ∧ N.forcingResidual hT.le F = F ∧
      ∀ k, ∃ Z : C(Icc (0 : ℝ) T, State iota),
        (∀ t, scaleDecode lambda k (Z t) = responseState lambda F t) ∧
        (∀ t i, Z t i = scaleWeight lambda k i * responseState lambda F t i) := by
  obtain ⟨T, hT, hT1, F, hF, hfix, hmass⟩ :=
    N.exists_response_all_mass s hs htheta hseed henergy
  refine ⟨T, hT, hT1, F, hF, hfix, ?_⟩
  intro k
  obtain ⟨B, hB, hb⟩ := hmass (2 * k)
  let U : Icc (0 : ℝ) T → State iota := fun t => responseState lambda F t
  have hU : Continuous U :=
    continuousOn_iff_continuous_restrict.mp
      (continuousOn_responseState_of_memLp hT.le (Lp.memLp F) lambda)
  have hscale (t : Icc (0 : ℝ) T) : InScale lambda (2 * k + 1) (U t) :=
    (inScale_iff_summable_weighted_sq lambda (2 * k + 1) (U t)).mpr (hb t t.property).1
  have hbound (t : Icc (0 : ℝ) T) :
      ‖scaleEncode lambda (2 * k) (U t)
        (inScale_mono lambda (by omega) (hscale t))‖ ≤ Real.sqrt B := by
    have hhigh : ‖scaleEncode lambda (2 * k + 1) (U t) (hscale t)‖ ≤ Real.sqrt B := by
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt hB, norm_scaleEncode_sq_eq_mass]
      exact (hb t t.property).2
    have heq : scaleEncode lambda (2 * k) (U t)
        (inScale_mono lambda (by omega) (hscale t)) =
        scaleDecode lambda 1 (scaleEncode lambda (2 * k + 1) (U t) (hscale t)) := by
      apply scaleDecode_injective lambda (2 * k)
      rw [scaleDecode_scaleEncode, ← ContinuousLinearMap.comp_apply,
        ← scaleDecode_add, scaleDecode_scaleEncode]
    rw [heq]
    exact (norm_scaleDecode_le lambda 1 _).trans hhigh
  refine ⟨⟨fun t => scaleEncode lambda k (U t)
    (inScale_mono lambda (by omega) (hscale t)),
    continuous_scaleEncode_of_double_bound lambda k U hU
      (fun t => inScale_mono lambda (by omega) (hscale t)) hbound⟩, ?_, ?_⟩
  · intro t
    exact scaleDecode_scaleEncode lambda k (U t) _
  · intro t i
    rfl

theorem fixedPoint_hasDerivWithinAt (hT : 0 ≤ T) (F : ForcingSpace iota T)
    (hfix : N.forcingResidual hT F = F) (Z : C(Icc (0 : ℝ) T, State iota))
    (hZ : ∀ t : Icc (0 : ℝ) T, scaleDecode lambda 2 (Z t) = responseState lambda F t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (responseState lambda F)
      (N.toFun (Z ⟨t, ht⟩) - (Z ⟨t, ht⟩ - responseState lambda F t))
      (Icc (0 : ℝ) T) t := by
  let Zext : ℝ → State iota := IccExtend hT (Z : Icc (0 : ℝ) T → State iota)
  have hZext : Continuous Zext := Z.continuous.Icc_extend'
  have hhigh : shiftedHighOperator hT lambda F =ᵐ[timeMeasure T] Zext := by
    filter_upwards [scaleDecode_shiftedHigh hT lambda F,
      ae_restrict_mem measurableSet_Ioc] with s hs hmem
    apply scaleDecode_injective lambda 2
    rw [hs, show Zext s = Z ⟨s, Ioc_subset_Icc_self hmem⟩ from
      IccExtend_of_mem hT _ (Ioc_subset_Icc_self hmem), hZ]
  have hforce : F =ᵐ[timeMeasure T] fun s => N.toFun (Zext s) := by
    have hsource := N.forcingResidual_coe hT F
    rw [hfix] at hsource
    filter_upwards [hsource, hhigh] with s hs hh
    exact hs.trans (congrArg N.toFun hh)
  have hd := hasDerivWithinAt_responseState_of_scale_path hT lambda F
    (N.continuous.comp hZext).continuousOn hforce Z hZ ht
  simpa only [Function.comp_apply, Zext, IccExtend_of_mem hT _ ht] using hd

private theorem weighted_mass_mono {k l : ℕ} (hkl : k ≤ l) (u : State iota)
    {B : ℝ}
    (h : Summable (fun i => (1 + (lambda i : ℝ)) ^ l * u i ^ 2) ∧
      (∑' i, (1 + (lambda i : ℝ)) ^ l * u i ^ 2) ≤ B) :
    Summable (fun i => (1 + (lambda i : ℝ)) ^ k * u i ^ 2) ∧
      (∑' i, (1 + (lambda i : ℝ)) ^ k * u i ^ 2) ≤ B := by
  have hpoint (i : iota) :
      (1 + (lambda i : ℝ)) ^ k * u i ^ 2 ≤
        (1 + (lambda i : ℝ)) ^ l * u i ^ 2 :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (le_add_of_nonneg_right (lambda i).coe_nonneg) hkl)
      (sq_nonneg _)
  have hs := h.1.of_nonneg_of_le (fun i => by positivity) hpoint
  exact ⟨hs, (hs.tsum_le_tsum hpoint h.1).trans h.2⟩

theorem exists_response_cofinal_mass (s : ℕ → Finset iota)
    (hs : Tendsto s atTop atTop) (orders : ℕ → ℕ)
    (horders : ∀ k, ∃ j, k ≤ orders j) {theta : ℝ} (htheta : theta ≤ 1)
    (hseed : ∀ k, InScale lambda k (N.toFun 0))
    (henergy : ∀ j, ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : Finset iota) (u : State iota),
      finiteProjection q u = u →
      ‖shiftedBaseMultiplier lambda (finiteHigh lambda q u)‖ ≤ 2 * N.forcingRadius →
      finiteWeightedEnergy lambda q (orders j)
        (fun i => N.toFun (finiteHigh lambda q u) i - N.toFun 0 i) ≤
        theta * finiteWeightedEnergy lambda q (orders j + 2) u +
          A * finiteWeightedEnergy lambda q (orders j + 1) u) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace iota T,
      ‖F‖ ≤ N.forcingRadius ∧ N.forcingResidual hT.le F = F ∧
      ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T,
        Summable (fun i => (1 + (lambda i : ℝ)) ^ (k + 1) *
          responseState lambda F t i ^ 2) ∧
        (∑' i, (1 + (lambda i : ℝ)) ^ (k + 1) *
          responseState lambda F t i ^ 2) ≤ B := by
  obtain ⟨T, hT, hT1, F, G, hF, hfix, hG, _, hlim⟩ := N.exists_projected_responses s hs
  refine ⟨T, hT, hT1, F, hF, hfix, ?_⟩
  intro k
  obtain ⟨j, hkj⟩ := horders k
  obtain ⟨A, hA, hAenergy⟩ := henergy j
  let S : ℝ := ‖scaleEncode lambda (orders j + 1) (N.toFun 0)
    (hseed (orders j + 1))‖ ^ 2
  have hS : 0 ≤ S := sq_nonneg _
  have hseedBound (l : ℕ) :
      finiteWeightedEnergy lambda (s l) (orders j + 1) (N.toFun 0) ≤ S := by
    dsimp [S, finiteWeightedEnergy]
    rw [norm_scaleEncode_sq_eq_mass]
    exact Summable.sum_le_tsum _ (fun i _ => by positivity)
      ((inScale_iff_summable_weighted_sq lambda (orders j + 1) (N.toFun 0)).mp
        (hseed (orders j + 1)))
  have hcont (l : ℕ) (i : iota) :
      ContinuousOn (fun t => responseState lambda (G l) t i) (Icc (0 : ℝ) T) :=
    (lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).continuous.comp_continuousOn
      (continuousOn_responseState_of_memLp hT.le (Lp.memLp (G l)) lambda)
  have hbound := weighted_sq_mass_le_of_galerkin lambda s hs (orders j) hT.le htheta hA hS
    (le_refl (0 : ℝ))
    (fun l t i => responseState lambda (G l) t i)
    (fun l t i => N.toFun (finiteHigh lambda (s l) (responseState lambda (G l) t)) i)
    (N.toFun 0) (fun t i => responseState lambda F t i)
    (fun l i _ => hcont l i)
    (fun l t ht i hi => N.projected_response_derivative hT.le (s l) (G l)
      (hG l).2.1 ht hi)
    (fun l t ht => hAenergy (s l) (responseState lambda (G l) t)
      (finiteProjection_response_eq lambda (s l) (G l) (hG l).2.2
        (Ico_subset_Icc_self ht))
      ((norm_intermediate_finiteHigh_response_le hT.le hT1 lambda (s l) (G l)
        (hG l).2.2 ⟨t, Ico_subset_Icc_self ht⟩).trans
          (mul_le_mul_of_nonneg_left (hG l).1 (by norm_num))))
    hseedBound
    (fun l => by simp [responseState_zero, finiteWeightedEnergy]) hlim
  refine ⟨gronwallBound 0 (3 + A) S T, ?_, ?_⟩
  · exact (tsum_nonneg (fun i => by positivity)).trans
      (hbound 0 ⟨le_rfl, hT.le⟩).2
  · intro t ht
    exact weighted_mass_mono (Nat.add_le_add_right hkj 1) (responseState lambda F t)
      (hbound t ht)

theorem exists_response_cofinal_scale_paths (s : ℕ → Finset iota)
    (hs : Tendsto s atTop atTop) (orders : ℕ → ℕ)
    (horders : ∀ k, ∃ j, k ≤ orders j) {theta : ℝ} (htheta : theta ≤ 1)
    (hseed : ∀ k, InScale lambda k (N.toFun 0))
    (henergy : ∀ j, ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : Finset iota) (u : State iota),
      finiteProjection q u = u →
      ‖shiftedBaseMultiplier lambda (finiteHigh lambda q u)‖ ≤ 2 * N.forcingRadius →
      finiteWeightedEnergy lambda q (orders j)
        (fun i => N.toFun (finiteHigh lambda q u) i - N.toFun 0 i) ≤
        theta * finiteWeightedEnergy lambda q (orders j + 2) u +
          A * finiteWeightedEnergy lambda q (orders j + 1) u) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace iota T,
      ‖F‖ ≤ N.forcingRadius ∧ N.forcingResidual hT.le F = F ∧
      ∀ k, ∃ Z : C(Icc (0 : ℝ) T, State iota),
        (∀ t, scaleDecode lambda k (Z t) = responseState lambda F t) ∧
        (∀ t i, Z t i = scaleWeight lambda k i * responseState lambda F t i) := by
  obtain ⟨T, hT, hT1, F, hF, hfix, hmass⟩ :=
    N.exists_response_cofinal_mass s hs orders horders htheta hseed henergy
  refine ⟨T, hT, hT1, F, hF, hfix, ?_⟩
  intro k
  obtain ⟨B, hB, hb⟩ := hmass (2 * k)
  let U : Icc (0 : ℝ) T → State iota := fun t => responseState lambda F t
  have hU : Continuous U :=
    continuousOn_iff_continuous_restrict.mp
      (continuousOn_responseState_of_memLp hT.le (Lp.memLp F) lambda)
  exact exists_continuous_scale_lift_of_mass lambda k U hU hB
    (fun t => weighted_mass_mono (by omega : 2 * k ≤ 2 * k + 1) (U t) (hb t t.property))

theorem exists_response_all_mass_of_even_energy (s : ℕ → Finset iota)
    (hs : Tendsto s atTop atTop) {theta : ℝ} (htheta : theta ≤ 1)
    (hseed : ∀ k, InScale lambda k (N.toFun 0))
    (henergy : ∀ k, ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : Finset iota) (u : State iota),
      finiteProjection q u = u →
      ‖shiftedBaseMultiplier lambda (finiteHigh lambda q u)‖ ≤ 2 * N.forcingRadius →
      finiteWeightedEnergy lambda q (2 * k)
        (fun i => N.toFun (finiteHigh lambda q u) i - N.toFun 0 i) ≤
        theta * finiteWeightedEnergy lambda q (2 * k + 2) u +
          A * finiteWeightedEnergy lambda q (2 * k + 1) u) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace iota T,
      ‖F‖ ≤ N.forcingRadius ∧ N.forcingResidual hT.le F = F ∧
      ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T,
        Summable (fun i => (1 + (lambda i : ℝ)) ^ (k + 1) *
          responseState lambda F t i ^ 2) ∧
        (∑' i, (1 + (lambda i : ℝ)) ^ (k + 1) *
          responseState lambda F t i ^ 2) ≤ B :=
  N.exists_response_cofinal_mass s hs (fun k => 2 * k) (fun k => ⟨k, by omega⟩)
    htheta hseed henergy

theorem exists_response_all_scale_paths_of_even_energy (s : ℕ → Finset iota)
    (hs : Tendsto s atTop atTop) {theta : ℝ} (htheta : theta ≤ 1)
    (hseed : ∀ k, InScale lambda k (N.toFun 0))
    (henergy : ∀ k, ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : Finset iota) (u : State iota),
      finiteProjection q u = u →
      ‖shiftedBaseMultiplier lambda (finiteHigh lambda q u)‖ ≤ 2 * N.forcingRadius →
      finiteWeightedEnergy lambda q (2 * k)
        (fun i => N.toFun (finiteHigh lambda q u) i - N.toFun 0 i) ≤
        theta * finiteWeightedEnergy lambda q (2 * k + 2) u +
          A * finiteWeightedEnergy lambda q (2 * k + 1) u) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧ ∃ F : ForcingSpace iota T,
      ‖F‖ ≤ N.forcingRadius ∧ N.forcingResidual hT.le F = F ∧
      ∀ k, ∃ Z : C(Icc (0 : ℝ) T, State iota),
        (∀ t, scaleDecode lambda k (Z t) = responseState lambda F t) ∧
        (∀ t i, Z t i = scaleWeight lambda k i * responseState lambda F t i) :=
  N.exists_response_cofinal_scale_paths s hs (fun k => 2 * k) (fun k => ⟨k, by omega⟩)
    htheta hseed henergy

theorem projected_response_even_mass_of_induction (hT : 0 < T) (hT1 : T ≤ 1)
    (s : ℕ → Finset iota) (G : ℕ → ForcingSpace iota T)
    (hG : ∀ j, ‖G j‖ ≤ N.forcingRadius ∧
      forcingProjection (s j) (N.forcingResidual hT.le (G j)) = G j)
    {theta : ℝ} (htheta : theta ≤ 1)
    (hseed : ∀ k, InScale lambda k (N.toFun 0))
    (hstep : ∀ k, ∀ B : ℝ, 0 ≤ B →
      (∀ j, ∀ t ∈ Icc (0 : ℝ) T,
        finiteWeightedEnergy lambda (s j) (2 * k - 1)
          (responseState lambda (G j) t) ≤ B) →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ j, ∀ t ∈ Ico (0 : ℝ) T,
        finiteWeightedEnergy lambda (s j) (2 * k)
          (fun i => N.toFun (finiteHigh lambda (s j) (responseState lambda (G j) t)) i -
            N.toFun 0 i) ≤
          theta * finiteWeightedEnergy lambda (s j) (2 * k + 2)
            (responseState lambda (G j) t) +
          A * finiteWeightedEnergy lambda (s j) (2 * k + 1)
            (responseState lambda (G j) t)) :
    ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ j, ∀ t ∈ Icc (0 : ℝ) T,
      finiteWeightedEnergy lambda (s j) (2 * k + 1)
        (responseState lambda (G j) t) ≤ B := by
  have hzero : ∀ j, ∀ t ∈ Icc (0 : ℝ) T,
      finiteWeightedEnergy lambda (s j) 0 (responseState lambda (G j) t) ≤
        N.forcingRadius ^ 2 := by
    intro j t ht
    let u := responseState lambda (G j) t
    have hu : Summable (fun i => |u i| ^ 2) := by
      simpa using (lp.memℓp u).summable
    calc
      _ = ∑ i ∈ s j, |u i| ^ 2 := by
        simp only [finiteWeightedEnergy, pow_zero, one_mul, sq_abs, u]
      _ ≤ ∑' i, |u i| ^ 2 :=
        hu.sum_le_tsum (s j) (fun i _ => sq_nonneg _)
      _ = ‖u‖ ^ 2 := (norm_sq_eq_tsum u).symm
      _ ≤ t * ‖G j‖ ^ 2 := by
        simpa only [forcing_norm_sq] using
          norm_responseState_sq_le_time_energy (Lp.memLp (G j)) lambda ht
      _ ≤ 1 * ‖G j‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (ht.2.trans hT1) (sq_nonneg _)
      _ ≤ N.forcingRadius ^ 2 := by
        rw [one_mul]
        exact (sq_le_sq₀ (norm_nonneg _) N.forcingRadius_pos.le).mpr (hG j).1
  have advance (k : ℕ) {B : ℝ} (hB : 0 ≤ B)
      (hprior : ∀ j, ∀ t ∈ Icc (0 : ℝ) T,
        finiteWeightedEnergy lambda (s j) (2 * k - 1)
          (responseState lambda (G j) t) ≤ B) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ∀ t ∈ Icc (0 : ℝ) T,
        finiteWeightedEnergy lambda (s j) (2 * k + 1)
          (responseState lambda (G j) t) ≤ C := by
    obtain ⟨A, hA, henergy⟩ := hstep k B hB hprior
    let S : ℝ := ‖scaleEncode lambda (2 * k + 1) (N.toFun 0) (hseed (2 * k + 1))‖ ^ 2
    have hS : 0 ≤ S := sq_nonneg _
    have hseedBound (j : ℕ) : finiteWeightedEnergy lambda (s j) (2 * k + 1) (N.toFun 0) ≤ S := by
      dsimp [S, finiteWeightedEnergy]
      rw [norm_scaleEncode_sq_eq_mass]
      exact Summable.sum_le_tsum _ (fun i _ => by positivity)
        ((inScale_iff_summable_weighted_sq lambda (2 * k + 1) (N.toFun 0)).mp
          (hseed (2 * k + 1)))
    have hbound (j : ℕ) : ∀ t ∈ Icc (0 : ℝ) T,
        finiteWeightedEnergy lambda (s j) (2 * k + 1)
          (responseState lambda (G j) t) ≤ gronwallBound 0 (3 + A) S T := by
      apply finiteWeightedEnergy_le_gronwall lambda (s j) (2 * k) hT.le htheta
        hA hS (le_refl (0 : ℝ))
        (fun t i => responseState lambda (G j) t i)
        (fun t i => N.toFun (finiteHigh lambda (s j) (responseState lambda (G j) t)) i)
        (N.toFun 0)
      · intro i _
        exact (lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).continuous.comp_continuousOn
          (continuousOn_responseState_of_memLp hT.le (Lp.memLp (G j)) lambda)
      · intro t ht i hi
        exact N.projected_response_derivative hT.le (s j) (G j) (hG j).2 ht hi
      · exact henergy j
      · exact hseedBound j
      · simp [responseState_zero, finiteWeightedEnergy]
    refine ⟨gronwallBound 0 (3 + A) S T, ?_, hbound⟩
    exact (finiteWeightedEnergy_nonneg lambda (s 0) (2 * k + 1)
      (responseState lambda (G 0) 0)).trans (hbound 0 0 ⟨le_rfl, hT.le⟩)
  intro k
  induction k with
  | zero =>
    exact advance 0 (sq_nonneg _) (by simpa only [Nat.mul_zero, Nat.zero_sub] using hzero)
  | succ k ih =>
    obtain ⟨B, hB, hprior⟩ := ih
    exact advance (k + 1) hB (by
      simpa only [show 2 * (k + 1) - 1 = 2 * k + 1 by omega] using hprior)

end SpatialResidual

section ParameterRegularity

variable {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem exists_contDiffAt_fixedPoint (R : P × X → X) {p : P} {x : X} {k : ℕ∞ω}
    (hk : k ≠ 0) (hR : ContDiffAt ℝ k R (p, x)) (hfix : R (p, x) = x)
    (hsmall : ‖(fderiv ℝ R (p, x)).comp (ContinuousLinearMap.inr ℝ P X)‖ < 1) :
    ∃ u : P → X, u p = x ∧ ContDiffAt ℝ k u p ∧
      (∀ᶠ q in 𝓝 p, R (q, u q) = u q) ∧
      (∀ᶠ q in 𝓝 (p, x), R q = q.2 ↔ u q.1 = q.2) := by
  let H : P × X → X := fun q => q.2 - R q
  have hH : ContDiffAt ℝ k H (p, x) := contDiffAt_snd.sub hR
  have hH0 : H (p, x) = 0 := sub_eq_zero.mpr hfix.symm
  have hD : fderiv ℝ H (p, x) = ContinuousLinearMap.snd ℝ P X - fderiv ℝ R (p, x) :=
    (hasFDerivAt_snd.sub (hR.differentiableAt hk).hasFDerivAt).fderiv
  have hpartial : (fderiv ℝ H (p, x)).comp (ContinuousLinearMap.inr ℝ P X) =
      1 - (fderiv ℝ R (p, x)).comp (ContinuousLinearMap.inr ℝ P X) := by
    rw [hD]
    ext y
    rfl
  have hinv : ((fderiv ℝ H (p, x)).comp (ContinuousLinearMap.inr ℝ P X)).IsInvertible := by
    rw [hpartial]
    obtain ⟨v, hv⟩ := isUnit_one_sub_of_norm_lt_one hsmall
    exact ⟨ContinuousLinearEquiv.ofUnit v, hv⟩
  refine ⟨hH.implicitFunction hk hinv, hH.implicitFunction_apply_self hk hinv,
    hH.contDiffAt_implicitFunction hk hinv, ?_, ?_⟩
  · filter_upwards [hH.eventually_apply_implicitFunction hk hinv] with q hq
    rw [hH0] at hq
    exact (sub_eq_zero.mp hq).symm
  · filter_upwards [hH.eventually_apply_eq_iff_implicitFunction hk hinv] with q hq
    rw [hH0] at hq
    simpa only [H, sub_eq_zero, eq_comm] using hq

theorem exists_contDiffAt_fixedPoint_of_contraction (R : P × X → X)
    {p : P} {x : X} {k : ℕ∞ω} {r K : ℝ} (hk : k ≠ 0)
    (hR : ContDiffAt ℝ k R (p, x)) (hfix : R (p, x) = x)
    (hx : ‖x‖ < r) (hK : 0 ≤ K) (hK1 : K < 1)
    (hLip : ∀ y z : X, ‖y‖ ≤ r → ‖z‖ ≤ r →
      ‖R (p, y) - R (p, z)‖ ≤ K * ‖y - z‖) :
    ∃ u : P → X, u p = x ∧ ContDiffAt ℝ k u p ∧
      (∀ᶠ q in 𝓝 p, R (q, u q) = u q) ∧
      (∀ᶠ q in 𝓝 (p, x), R q = q.2 ↔ u q.1 = q.2) := by
  apply exists_contDiffAt_fixedPoint R hk hR hfix
  have hslice : HasFDerivAt (fun y : X => R (p, y))
      ((fderiv ℝ R (p, x)).comp (ContinuousLinearMap.inr ℝ P X)) x := by
    have hprod : (0 : X →L[ℝ] P).prod (ContinuousLinearMap.id ℝ X) =
        ContinuousLinearMap.inr ℝ P X := by ext y <;> rfl
    simpa only [Function.comp_def, hprod] using
      (hR.differentiableAt hk).hasFDerivAt.comp x
        ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))
  apply (hslice.le_of_lip' hK ?_).trans_lt hK1
  filter_upwards [Metric.closedBall_mem_nhds_of_mem
    (show x ∈ Metric.ball (0 : X) r by simpa using hx)] with y hy
  exact hLip y x (by simpa using hy) hx.le

end ParameterRegularity

end PoincareConjecture.QuasilinearDeTurckNative
