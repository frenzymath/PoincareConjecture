import PoincareConjecture.Proofs.M03.Existence.SpectralLpOperatorNative
import PoincareConjecture.Proofs.M03.Existence.SpectralTraceOperatorNative
import PoincareConjecture.Proofs.M03.Existence.VolterraContractionNative
import Mathlib.MeasureTheory.Integral.DominatedConvergence









set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*} {T r : ℝ} {K : NNReal}


theorem exists_forcing_fixedPoint
    (R : ForcingSpace iota T → ForcingSpace iota T)
    (hr : 0 ≤ r) (hK : K < 1)
    (hzero : ‖R 0‖ ≤ (1 - (K : ℝ)) * r)
    (hLip : ∀ F G : ForcingSpace iota T, ‖F‖ ≤ r → ‖G‖ ≤ r →
      ‖R F - R G‖ ≤ (K : ℝ) * ‖F - G‖) :
    ∃ F : ForcingSpace iota T, ‖F‖ ≤ r ∧ R F = F ∧
      Tendsto (fun m : ℕ => R^[m] 0) atTop (𝓝 F) ∧
      ∀ m : ℕ, edist (R^[m] 0) F ≤
        edist 0 (R 0) * (K : ℝ≥0∞) ^ m / (1 - K) := by
  have hmaps : MapsTo R (Metric.closedBall 0 r) (Metric.closedBall 0 r) := by
    intro F hF
    have hFn : ‖F‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hF
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖R F‖ = ‖R F - R 0 + R 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖R F - R 0‖ + ‖R 0‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * ‖F‖ + (1 - (K : ℝ)) * r := by
        apply add_le_add _ hzero
        simpa only [sub_zero] using hLip F 0 hFn (by simpa only [norm_zero] using hr)
      _ ≤ (K : ℝ) * r + (1 - (K : ℝ)) * r :=
        add_le_add (mul_le_mul_of_nonneg_left hFn K.coe_nonneg) le_rfl
      _ = r := by ring
  have hcontract : ContractingWith K
      (hmaps.restrict R (Metric.closedBall 0 r) (Metric.closedBall 0 r)) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro F G
    change dist (R (F : ForcingSpace iota T)) (R (G : ForcingSpace iota T)) ≤
      (K : ℝ) * dist (F : ForcingSpace iota T) (G : ForcingSpace iota T)
    rw [dist_eq_norm, dist_eq_norm]
    apply hLip
    · simpa only [Metric.mem_closedBall, dist_zero_right] using F.property
    · simpa only [Metric.mem_closedBall, dist_zero_right] using G.property
  obtain ⟨F, hF, hfix, hiter, herror⟩ :=
    PoincareConjecture.volterra_closedBall_fixedPoint 0 hr R hmaps hcontract
  exact ⟨F, by simpa only [Metric.mem_closedBall, dist_zero_right] using hF,
    hfix, hiter, herror⟩


def nonlinearForcingResidual (lambda : iota → NNReal)
    (N : (ℝ → State iota) → ForcingSpace iota T)
    (F : ForcingSpace iota T) : ForcingSpace iota T :=
  N (responseState lambda F)


theorem exists_nonlinear_spectral_response [Countable iota]
    (hT : 0 ≤ T) (lambda : iota → NNReal)
    (N : (ℝ → State iota) → ForcingSpace iota T)
    (hr : 0 ≤ r) (hK : K < 1)
    (hzero : ‖nonlinearForcingResidual lambda N 0‖ ≤ (1 - (K : ℝ)) * r)
    (hLip : ∀ F G : ForcingSpace iota T, ‖F‖ ≤ r → ‖G‖ ≤ r →
      ‖nonlinearForcingResidual lambda N F - nonlinearForcingResidual lambda N G‖ ≤
        (K : ℝ) * ‖F - G‖) :
    ∃ (F : ForcingSpace iota T) (U D G : ℝ → State iota),
      ‖F‖ ≤ r ∧ U = responseState lambda F ∧ N U = F ∧
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (timeMeasure T) ∧ MemLp G 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T, D t + G t = (N U) t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i, G t i = (lambda i : ℝ) * U t i) ∧
      (∫ t, ‖D t‖ ^ 2 ∂timeMeasure T) + (∫ t, ‖G t‖ ^ 2 ∂timeMeasure T) ≤ r ^ 2 ∧
      Tendsto (fun m : ℕ => (nonlinearForcingResidual lambda N)^[m] 0)
        atTop (𝓝 F) := by
  obtain ⟨F, hF, hfix, hiter, _⟩ :=
    exists_forcing_fixedPoint (nonlinearForcingResidual lambda N) hr hK hzero hLip
  have hNF : N (responseState lambda F) = F := hfix
  refine ⟨F, responseState lambda F, derivativeState lambda F, generatorState lambda F,
    hF, rfl, hNF, responseState_zero lambda F,
    continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda,
    memLp_derivativeState_of_memLp hT (Lp.memLp F) lambda,
    memLp_generatorState_of_memLp hT (Lp.memLp F) lambda,
    ae_hasDerivAt_responseState_of_memLp hT (Lp.memLp F) lambda, ?_,
    ae_generatorState_apply_of_memLp hT (Lp.memLp F) lambda, ?_, hiter⟩
  · rw [hNF]
    exact derivativeState_add_generatorState_of_memLp hT (Lp.memLp F) lambda
  · calc
      _ ≤ ∫ t, ‖F t‖ ^ 2 ∂timeMeasure T :=
        integral_response_energy_le_of_memLp hT (Lp.memLp F) lambda
      _ = ‖F‖ ^ 2 := (forcing_norm_sq F).symm
      _ ≤ r ^ 2 := (sq_le_sq₀ (norm_nonneg F) hr).mpr hF


def finiteProjection (s : Finset iota) : State iota →L[ℝ] State iota := by
  classical
  exact multiplier (fun i => if i ∈ s then 1 else 0) 1 zero_le_one
    (fun i => by split <;> norm_num)

@[simp] theorem finiteProjection_apply (s : Finset iota) (u : State iota) (i : iota) :
    finiteProjection s u i = if i ∈ s then u i else 0 := by
  classical
  change (if i ∈ s then (1 : ℝ) else 0) * u i = _
  split <;> simp_all only [one_mul, zero_mul]

theorem finiteProjection_eq_sum (s : Finset iota) (u : State iota) :
    finiteProjection s u = ∑ i ∈ s, lp.single 2 i (u i) := by
  classical
  apply lp.ext
  funext i
  simp only [finiteProjection_apply, lp.coeFn_sum, lp.coeFn_single,
    Finset.sum_apply, Finset.sum_pi_single]

theorem norm_finiteProjection_apply_le (s : Finset iota) (u : State iota) :
    ‖finiteProjection s u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro i
  rw [finiteProjection_apply]
  split <;> simp

theorem norm_finiteProjection_le (s : Finset iota) : ‖finiteProjection s‖ ≤ 1 := by
  apply (finiteProjection s).opNorm_le_bound zero_le_one
  intro u
  simpa only [one_mul] using norm_finiteProjection_apply_le s u

@[simp] theorem finiteProjection_idempotent (s : Finset iota) (u : State iota) :
    finiteProjection s (finiteProjection s u) = finiteProjection s u := by
  classical
  apply lp.ext
  funext i
  simp only [finiteProjection_apply]
  split <;> rfl

theorem tendsto_finiteProjection (s : ℕ → Finset iota) (hs : Tendsto s atTop atTop)
    (u : State iota) : Tendsto (fun N => finiteProjection (s N) u) atTop (𝓝 u) := by
  classical
  have hsum : Tendsto (fun q : Finset iota => ∑ i ∈ q, lp.single 2 i (u i)) atTop (𝓝 u) := by
    simpa only [HasSum, SummationFilter.unconditional] using
      lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ∞) u
  simpa only [finiteProjection_eq_sum, Function.comp_def] using hsum.comp hs


def forcingProjection (s : Finset iota) : ForcingSpace iota T →L[ℝ] ForcingSpace iota T :=
  (finiteProjection s).compLpL 2 (timeMeasure T)

theorem forcingProjection_coe (s : Finset iota) (F : ForcingSpace iota T) :
    forcingProjection s F =ᵐ[timeMeasure T] fun t => finiteProjection s (F t) :=
  (finiteProjection s).coeFn_compLpL F

theorem norm_forcingProjection_le (s : Finset iota) :
    ‖forcingProjection (T := T) s‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans (norm_finiteProjection_le s)

theorem norm_forcingProjection_apply_le (s : Finset iota) (F : ForcingSpace iota T) :
    ‖forcingProjection s F‖ ≤ ‖F‖ := by
  calc
    _ ≤ ‖forcingProjection (T := T) s‖ * ‖F‖ := (forcingProjection s).le_opNorm F
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right (norm_forcingProjection_le s) (norm_nonneg F)
    _ = ‖F‖ := one_mul _

@[simp] theorem forcingProjection_idempotent (s : Finset iota) (F : ForcingSpace iota T) :
    forcingProjection s (forcingProjection s F) = forcingProjection s F := by
  apply Lp.ext
  filter_upwards [forcingProjection_coe s (forcingProjection s F), forcingProjection_coe s F]
    with t ht hF
  rw [ht, hF, finiteProjection_idempotent]



theorem tendsto_forcingProjection (s : ℕ → Finset iota) (hs : Tendsto s atTop atTop)
    (F : ForcingSpace iota T) : Tendsto (fun N => forcingProjection (s N) F) atTop (𝓝 F) := by
  let G : ℕ → ℝ → State iota := fun N t => finiteProjection (s N) (F t) - F t
  have hG : ∀ N, MemLp (G N) 2 (timeMeasure T) := fun N =>
    ((finiteProjection (s N)).comp_memLp' (Lp.memLp F)).sub (Lp.memLp F)
  have hnorm (N : ℕ) (t : ℝ) : ‖G N t‖ ≤ 2 * ‖F t‖ := by
    exact (norm_sub_le _ _).trans (by
      have h := norm_finiteProjection_apply_le (s N) (F t)
      linarith)
  have hi : Integrable (fun t => 4 * ‖F t‖ ^ 2) (timeMeasure T) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp F).aestronglyMeasurable).mp
      (Lp.memLp F)).const_mul 4
  have hconv : Tendsto (fun N => ∫ t, ‖G N t‖ ^ 2 ∂timeMeasure T) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := timeMeasure T)
      (F := fun N t => ‖G N t‖ ^ 2)
      (f := fun _ : ℝ => (0 : ℝ)) (fun t => 4 * ‖F t‖ ^ 2)
      (fun N => by simpa only [Pi.pow_def] using (hG N).aestronglyMeasurable.norm.pow 2) hi
      (fun N => Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hnorm N t, norm_nonneg (G N t), norm_nonneg (F t)]))
      (Eventually.of_forall (fun t => by
        have h := ((tendsto_finiteProjection s hs (F t)).sub_const (F t)).norm.pow 2
        simpa only [G, Function.comp_apply, sub_self, norm_zero,
          zero_pow (by decide : 2 ≠ 0)] using h))
    simpa only [integral_zero] using h
  have hsq (N : ℕ) : ‖forcingProjection (s N) F - F‖ ^ 2 =
      ∫ t, ‖G N t‖ ^ 2 ∂timeMeasure T := by
    rw [forcing_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (forcingProjection (s N) F) F,
      forcingProjection_coe (s N) F] with t ht hF
    rw [ht, Pi.sub_apply, hF]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnormSq : Tendsto (fun N => ‖forcingProjection (s N) F - F‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hconv
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hnormSq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot


theorem exists_projected_forcing_fixedPoint
    (R : ForcingSpace iota T → ForcingSpace iota T)
    (hr : 0 ≤ r) (hK : K < 1)
    (hzero : ‖R 0‖ ≤ (1 - (K : ℝ)) * r)
    (hLip : ∀ F G : ForcingSpace iota T, ‖F‖ ≤ r → ‖G‖ ≤ r →
      ‖R F - R G‖ ≤ (K : ℝ) * ‖F - G‖) (s : Finset iota) :
    ∃ F : ForcingSpace iota T, ‖F‖ ≤ r ∧ forcingProjection s (R F) = F ∧
      forcingProjection s F = F := by
  have hz : ‖forcingProjection s (R 0)‖ ≤ (1 - (K : ℝ)) * r :=
    (norm_forcingProjection_apply_le s (R 0)).trans hzero
  have hL : ∀ F G : ForcingSpace iota T, ‖F‖ ≤ r → ‖G‖ ≤ r →
      ‖forcingProjection s (R F) - forcingProjection s (R G)‖ ≤ (K : ℝ) * ‖F - G‖ := by
    intro F G hF hG
    rw [← map_sub]
    exact (norm_forcingProjection_apply_le s (R F - R G)).trans (hLip F G hF hG)
  obtain ⟨F, hF, hfix, _, _⟩ :=
    exists_forcing_fixedPoint (fun F => forcingProjection s (R F)) hr hK hz hL
  refine ⟨F, hF, hfix, ?_⟩
  rw [← hfix, forcingProjection_idempotent]


theorem projected_forcing_fixedPoint_error
    (R : ForcingSpace iota T → ForcingSpace iota T) (s : Finset iota)
    {F G : ForcingSpace iota T} (hF : ‖F‖ ≤ r) (hG : ‖G‖ ≤ r)
    (hfix : R F = F) (hproj : forcingProjection s (R G) = G)
    (hLip : ∀ U V : ForcingSpace iota T, ‖U‖ ≤ r → ‖V‖ ≤ r →
      ‖R U - R V‖ ≤ (K : ℝ) * ‖U - V‖) :
    (1 - (K : ℝ)) * ‖G - F‖ ≤ ‖forcingProjection s F - F‖ := by
  have hdiff : ‖G - forcingProjection s F‖ ≤ (K : ℝ) * ‖G - F‖ := by
    calc
      _ = ‖forcingProjection s (R G) - forcingProjection s (R F)‖ := by rw [hproj, hfix]
      _ = ‖forcingProjection s (R G - R F)‖ := by rw [map_sub]
      _ ≤ (K : ℝ) * ‖G - F‖ :=
        (norm_forcingProjection_apply_le s (R G - R F)).trans (hLip G F hG hF)
  have htri : ‖G - F‖ ≤ ‖G - forcingProjection s F‖ + ‖forcingProjection s F - F‖ := by
    simpa only [sub_add_sub_cancel] using
      norm_add_le (G - forcingProjection s F) (forcingProjection s F - F)
  nlinarith


theorem exists_projected_forcing_fixedPoints
    (R : ForcingSpace iota T → ForcingSpace iota T)
    (hr : 0 ≤ r) (hK : K < 1)
    (hzero : ‖R 0‖ ≤ (1 - (K : ℝ)) * r)
    (hLip : ∀ F G : ForcingSpace iota T, ‖F‖ ≤ r → ‖G‖ ≤ r →
      ‖R F - R G‖ ≤ (K : ℝ) * ‖F - G‖)
    (s : ℕ → Finset iota) (hs : Tendsto s atTop atTop) :
    ∃ (F : ForcingSpace iota T) (G : ℕ → ForcingSpace iota T),
      ‖F‖ ≤ r ∧ R F = F ∧
      (∀ N, ‖G N‖ ≤ r ∧ forcingProjection (s N) (R (G N)) = G N ∧
        forcingProjection (s N) (G N) = G N) ∧
      (∀ N, (1 - (K : ℝ)) * ‖G N - F‖ ≤ ‖forcingProjection (s N) F - F‖) ∧
      Tendsto G atTop (𝓝 F) := by
  obtain ⟨F, hF, hfix, _, _⟩ := exists_forcing_fixedPoint R hr hK hzero hLip
  choose G hG hGfix hGsupport using
    fun N => exists_projected_forcing_fixedPoint R hr hK hzero hLip (s N)
  have herr (N : ℕ) : (1 - (K : ℝ)) * ‖G N - F‖ ≤ ‖forcingProjection (s N) F - F‖ :=
    projected_forcing_fixedPoint_error R (s N) hF (hG N) hfix (hGfix N) hLip
  refine ⟨F, G, hF, hfix, fun N => ⟨hG N, hGfix N, hGsupport N⟩, herr, ?_⟩
  have hgap : 0 < 1 - (K : ℝ) := by
    have hKr : (K : ℝ) < 1 := by exact_mod_cast hK
    linarith
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (g := fun N => ‖forcingProjection (s N) F - F‖ / (1 - (K : ℝ)))
    (fun N => norm_nonneg (G N - F)) (fun N => ?_) ?_
  · exact (le_div_iff₀ hgap).mpr (by simpa only [mul_comm] using herr N)
  · have h := ((tendsto_forcingProjection s hs F).sub_const F).norm.div_const (1 - (K : ℝ))
    simpa only [sub_self, norm_zero, zero_div] using h



theorem tendsto_responseState_coeff_of_forcing [Countable iota]
    (hT : 0 ≤ T) (lambda : iota → NNReal) {F : ForcingSpace iota T}
    {G : ℕ → ForcingSpace iota T} (hG : Tendsto G atTop (𝓝 F))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : iota) :
    Tendsto (fun N => responseState lambda (G N) t i) atTop
      (𝓝 (responseState lambda F t i)) := by
  have heval : Continuous (fun P : ResponsePath iota T => P ⟨t, ht⟩ i) :=
    (lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).continuous.comp
      (ContinuousMap.evalCLM ℝ (⟨t, ht⟩ : Icc (0 : ℝ) T) :
        ResponsePath iota T →L[ℝ] State iota).continuous
  have h := (heval.comp (responseOperator hT lambda).continuous).continuousAt.tendsto.comp hG
  simpa only [Function.comp_def, responseOperator_apply, responsePath_apply] using h


theorem responseState_eq_zero_of_forcingProjection [Countable iota]
    (lambda : iota → NNReal) (s : Finset iota) (F : ForcingSpace iota T)
    (hF : forcingProjection s F = F) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    {i : iota} (hi : i ∉ s) : responseState lambda F t i = 0 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hae : (fun r => F r i) =ᵐ[timeMeasure T] fun _ => (0 : ℝ) := by
    have h := forcingProjection_coe s F
    rw [hF] at h
    filter_upwards [h] with r hr
    have hc := congrArg (fun x : State iota => x i) hr
    simpa only [finiteProjection_apply, if_neg hi] using hc
  rw [responseState_apply_of_memLp (Lp.memLp F) lambda ht]
  change spectralMode (lambda i) 0 (fun r => F r i) t = 0
  have heq := spectralMode_eq_of_ae_eq (lambda := (lambda i : ℝ)) (c := 0)
    (T := T) (t := t) (by simpa only [timeMeasure, uIoc_of_le hT] using hae)
    (by simpa only [uIcc_of_le hT] using ht)
  rw [heq]
  simp only [spectralMode, mul_zero, intervalIntegral.integral_zero, zero_add]



theorem hasDerivWithinAt_responseState_coeff_of_continuous [Countable iota]
    (lambda : iota → NNReal) (F : ForcingSpace iota T) (i : iota)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (heq : (fun r => F r i) =ᵐ[timeMeasure T] f)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun r => responseState lambda F r i)
      (f t - (lambda i : ℝ) * responseState lambda F t i) (Ici t) t := by
  have hT : 0 ≤ T := ht.1.trans ht.2.le
  have hmode : ∀ r ∈ Icc (0 : ℝ) T,
      responseState lambda F r i = spectralMode (lambda i) 0 f r := by
    intro r hr
    rw [responseState_apply_of_memLp (Lp.memLp F) lambda hr]
    exact spectralMode_eq_of_ae_eq (T := T)
      (by simpa only [timeMeasure, uIoc_of_le hT] using heq)
      (by simpa only [uIcc_of_le hT] using hr)
  have hd := (hasDerivWithinAt_spectralMode (lambda := (lambda i : ℝ)) (c := 0)
    hf (Ico_subset_Icc_self ht)).congr_of_mem hmode (Ico_subset_Icc_self ht)
  rw [← hmode t (Ico_subset_Icc_self ht)] at hd
  exact hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)



theorem projected_response_hasDerivWithinAt [Countable iota]
    (lambda : iota → NNReal) (s : Finset iota) (N : State iota → State iota)
    (hN : Continuous (fun z => N (finiteProjection s z)))
    (F H : ForcingSpace iota T) (hfix : forcingProjection s H = F)
    (hsource : H =ᵐ[timeMeasure T] fun r => N (responseState lambda F r))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) {i : iota} (hi : i ∈ s) :
    HasDerivWithinAt (fun r => responseState lambda F r i)
      (N (responseState lambda F t) i - (lambda i : ℝ) * responseState lambda F t i)
      (Ici t) t := by
  have hT : 0 ≤ T := ht.1.trans ht.2.le
  have hsupp : forcingProjection s F = F := by rw [← hfix, forcingProjection_idempotent]
  have hpath : ∀ r ∈ Icc (0 : ℝ) T,
      finiteProjection s (responseState lambda F r) = responseState lambda F r := by
    intro r hr
    apply lp.ext
    funext j
    rw [finiteProjection_apply]
    by_cases hj : j ∈ s
    · rw [if_pos hj]
    · rw [if_neg hj, responseState_eq_zero_of_forcingProjection lambda s F hsupp hr hj]
  have hc : ContinuousOn (fun r => N (responseState lambda F r)) (Icc (0 : ℝ) T) := by
    have h := hN.comp_continuousOn (continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda)
    exact h.congr (fun r hr => by simp only [Function.comp_apply, hpath r hr])
  have hci : ContinuousOn (fun r => N (responseState lambda F r) i) (Icc (0 : ℝ) T) :=
    (lp.evalCLM ℝ (fun _ : iota => ℝ) 2 i).continuous.comp_continuousOn hc
  refine hasDerivWithinAt_responseState_coeff_of_continuous lambda F i hci ?_ ht
  have hp := forcingProjection_coe s H
  rw [hfix] at hp
  filter_upwards [hp, hsource] with r hr hH
  have hcoord := congrArg (fun z : State iota => z i) hr
  simpa only [finiteProjection_apply, if_pos hi, hH] using hcoord

end PoincareConjecture.SpectralHeatNative
