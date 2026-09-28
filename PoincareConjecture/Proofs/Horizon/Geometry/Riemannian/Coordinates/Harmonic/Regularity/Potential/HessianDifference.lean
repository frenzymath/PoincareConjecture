import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.ThirdMoment
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution









noncomputable section
set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology NNReal RealInnerProductSpace

namespace Poincare.Parabolic.Interior.Kernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
private theorem continuous_heatD3Map (t : ℝ) (v w : V) :
    Continuous (heatD3Map t v w) := by
  unfold heatD3Map baseD3Map baseHeat baseHeatMass
  fun_prop



def heatD3ConvMap (t : ℝ) (v w : V) (f : V → F) (x : V) : V →L[ℝ] F :=
  ∫ y, (heatD3Map t v w (x - y)).smulRight (f y)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [CompleteSpace F] in
private theorem continuous_heatD3_integrand {f : V → F} (hf : Continuous f)
    (t : ℝ) (v w : V) :
    Continuous (fun q : V × V => (heatD3Map t v w (q.1 - q.2)).smulRight (f q.2)) := by
  have hk := continuous_heatD3Map t v w
  fun_prop

omit [Nontrivial V] [CompleteSpace F] in
private theorem integrable_heatD3_integrand {f : V → F} (hf : Continuous f)
    (hc : HasCompactSupport f) (t : ℝ) (v w x : V) :
    Integrable (fun y => (heatD3Map t v w (x - y)).smulRight (f y)) := by
  apply ((continuous_heatD3_integrand hf t v w).comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro y hy
  by_contra hy'
  exact hy (by simp [image_eq_zero_of_notMem_tsupport hy'])

omit [Nontrivial V] [CompleteSpace F] in


theorem heatD3ConvMap_apply_of_compact {f : V → F} (hf : Continuous f)
    (hc : HasCompactSupport f) (t : ℝ) (v w x u : V) :
    heatD3ConvMap t v w f x u = heatD3Conv t u v w f x := by
  unfold heatD3ConvMap heatD3Conv
  rw [ContinuousLinearMap.integral_apply (integrable_heatD3_integrand hf hc t v w x) u]
  simp only [ContinuousLinearMap.smulRight_apply, heatD3Map_apply]
  rw [← MeasureTheory.convolution_lsmul_swap]
  rfl

omit [Nontrivial V] [CompleteSpace F] in


theorem heatD2Conv_hasFDerivAt_of_compact {f : V → F} (hf : Continuous f)
    (hc : HasCompactSupport f) (t : ℝ) (v w x : V) :
    HasFDerivAt (heatD2Conv t v w f) (heatD3ConvMap t v w f x) x := by
  let G := fun z y => heatD2 t v w (z - y) • f y
  let DG := fun z y => (heatD3Map t v w (z - y)).smulRight (f y)
  have hGcont (z) : Continuous (G z) := by
    dsimp [G]
    unfold heatD2 baseD2 baseHeat baseHeatMass
    fun_prop
  have hGc (z) : HasCompactSupport (G z) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro y hy
    by_contra hy'
    exact hy (by simp [G, image_eq_zero_of_notMem_tsupport hy'])
  have hDGcont : Continuous (fun q : V × V => DG q.1 q.2) :=
    continuous_heatD3_integrand hf t v w
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x (1 : ℝ)).prod hc).exists_bound_of_continuousOn
    hDGcont.continuousOn
  let bound := (tsupport f).indicator (fun _ => max 0 C)
  have hboundI : Integrable bound := by
    dsimp [bound]
    rw [integrable_indicator_iff hc.measurableSet]
    exact integrableOn_const hc.measure_lt_top.ne
  have hbound : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x 1,
      ‖DG z y‖ ≤ bound y := by
    filter_upwards with y z hz
    by_cases hy : y ∈ tsupport f
    · rw [show bound y = max 0 C from indicator_of_mem hy _]
      exact (hC (z, y) ⟨Metric.ball_subset_closedBall hz, hy⟩).trans (le_max_right _ _)
    · simp [bound, hy, DG, image_eq_zero_of_notMem_tsupport hy]
  have hdiff : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x 1,
      HasFDerivAt (G · y) (DG z y) z := by
    filter_upwards with y z _
    have hsub : HasFDerivAt (fun q : V => q - y) (ContinuousLinearMap.id ℝ V) z :=
      (hasFDerivAt_id z).sub_const y
    dsimp [G, DG]
    simpa using ((heatD2_hasFDeriv v w (z - y)).comp z hsub).smul_const (f y)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := DG) (bound := bound)
    (Metric.ball_mem_nhds x zero_lt_one)
    (Eventually.of_forall fun z => (hGcont z).aestronglyMeasurable)
    ((hGcont x).integrable_of_hasCompactSupport (hGc x))
    (integrable_heatD3_integrand hf hc t v w x).aestronglyMeasurable
    hbound hboundI hdiff
  have heq : (fun z => ∫ y, G z y) = heatD2Conv t v w f := by
    funext z
    unfold G heatD2Conv
    rw [← MeasureTheory.convolution_lsmul_swap]
    rfl
  rw [heq] at h
  exact h



theorem heatD3ConvMap_norm_le_of_half_holder {f : V → F} (hc : HasCompactSupport f)
    {K : ℝ≥0} (hf : HolderWith K (1 / 2) f) {t : ℝ} (ht : 0 < t) (v w x : V) :
    ‖heatD3ConvMap t v w f x‖ ≤
      heatC3Half V * (K : ℝ) * ‖v‖ * ‖w‖ * t ^ (-(5 : ℝ) / 4) := by
  have hC := heatC3Half_nonneg (V := V)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [heatD3ConvMap_apply_of_compact (hf.continuous (by norm_num)) hc,
    heatD3Conv_eq_cancel_of_half_holder ht hf]
  exact (heatD3Cancel_norm_of_half_holder ht hf u v w x).trans_eq (by ring)


theorem heatD2Conv_sub_norm_le_of_half_holder {f : V → F} (hc : HasCompactSupport f)
    {K : ℝ≥0} (hf : HolderWith K (1 / 2) f) {t : ℝ} (ht : 0 < t) (v w x y : V) :
    ‖heatD2Conv t v w f x - heatD2Conv t v w f y‖ ≤
      heatC3Half V * (K : ℝ) * ‖v‖ * ‖w‖ * t ^ (-(5 : ℝ) / 4) * ‖x - y‖ := by
  exact (convex_univ : Convex ℝ (univ : Set V)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (heatD2Conv_hasFDerivAt_of_compact (hf.continuous (by norm_num))
      hc t v w z).hasFDerivWithinAt)
    (fun z _ => heatD3ConvMap_norm_le_of_half_holder hc hf ht v w z)
    (mem_univ y) (mem_univ x)


theorem heatD2Conv_sub_norm_le_uniform_half_holder {f : V → F}
    {K : ℝ≥0} (hf : HolderWith K (1 / 2) f) {t : ℝ} (ht : 0 < t) (v w x y : V) :
    ‖heatD2Conv t v w f x - heatD2Conv t v w f y‖ ≤
      2 * heatC2Half V * (K : ℝ) * ‖v‖ * ‖w‖ * t ^ (-(3 : ℝ) / 4) := by
  rw [heatD2Conv_eq_cancel ht hf, heatD2Conv_eq_cancel ht hf]
  exact (norm_sub_le _ _).trans
    ((add_le_add (heatD2Cancel_norm ht hf v w x) (heatD2Cancel_norm ht hf v w y)).trans_eq
      (by unfold heatScale34; ring))

end Poincare.Parabolic.Interior.Kernel
