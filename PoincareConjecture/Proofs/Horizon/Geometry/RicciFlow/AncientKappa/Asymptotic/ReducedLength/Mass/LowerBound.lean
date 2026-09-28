import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.UpperBound


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem le_lintegral_limitDensity_of_tendsto_reducedVolume
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hlim : TendstoLocallyUniformlyOn (fun k z => G.reducedLengthPullback k z.1 z.2)
      l atTop (univ ×ˢ Ioi (0 : ℝ))) {τ Vlim : ℝ} (hτ : 0 < τ)
    (hV : Tendsto
      (fun k => reducedVolume K.flow 0 S.reference (S.scale (G.subsequence k) * τ))
      atTop (𝓝 Vlim)) :
    ENNReal.ofReal Vlim ≤ ∫⁻ x,
      ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
        ∂(G.limit.flow.metric (-τ)).volumeMeasure := by
  let g := G.limit.flow.metric (-τ)
  let F (k : ℕ) (x : M) : ℝ≥0∞ := ENNReal.ofReal
    (τ ^ (-(n : ℝ) / 2) * Real.exp (-reducedLength K.flow 0 S.reference x
      (S.scale (G.subsequence k) * τ)))
  let f (x : G.limit.carrier.carrier) : ℝ≥0∞ :=
    ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
  have hF : ∀ k, Continuous (F k) := fun k =>
    ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_exp.comp
      (P.continuous_reducedLength S.reference (S.scale (G.subsequence k) * τ)
        (mul_pos (S.scale_pos _) hτ)).neg))
  have htotal (k : ℕ) : (∫⁻ x, F k x
      ∂((S.rescaling (G.subsequence k)).flow.metric (-τ)).volumeMeasure) =
      ENNReal.ofReal (reducedVolume K.flow 0 S.reference (S.scale (G.subsequence k) * τ)) := by
    simpa only [calibratedMetricVolume_eq_volumeMeasure] using
      S.lintegral_normalized_reducedLength_eq_reducedVolume P (G.subsequence k) hτ
  have htotalLim : Tendsto
      (fun k => ∫⁻ x, F k x ∂((S.rescaling (G.subsequence k)).flow.metric (-τ)).volumeMeasure)
      atTop (𝓝 (ENNReal.ofReal Vlim)) := by
    simpa only [htotal] using ENNReal.tendsto_ofReal hV
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨R, hR, htail⟩ := S.normalized_reducedLength_tails_small P hτ
    (show 0 < (ε : ℝ) from hε)
  let U := g.ball G.limit.base (2 * R)
  let : EMetricSpace G.limit.carrier.carrier := G.limit.carrier.metricEMetricSpace g
  have hU : IsOpen U := isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hUc : IsCompact (closure U) :=
    g.isCompact_closure_ball_of_metricComplete (G.limit.complete (-τ) (neg_neg_of_pos hτ))
      G.limit.base (2 * R)
  have hconv := G.tendsto_lintegral_reducedLengthPullback_on_precompact P hlim hτ
    hU.measurableSet hUc
  apply Poincare.Analysis.ennreal_le_of_forall_one_lt_pow_mul_add n
  intro C hC
  have hprod := (ENNReal.Tendsto.mul tendsto_const_nhds
    (Or.inl (pow_ne_zero n (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hC))))
    hconv (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))).add
      (tendsto_const_nhds (x := (ε : ℝ≥0∞)))
  have hlocal : ENNReal.ofReal Vlim ≤ ENNReal.ofReal C ^ n *
      (∫⁻ x in U, f x ∂g.volumeMeasure) + ε := by
    apply le_of_tendsto_of_tendsto htotalLim hprod
    filter_upwards [G.eventually_lintegral_sourcePoint_image_bounds (neg_neg_of_pos hτ) hC
      hU hUc F hF,
      G.eventually_source_base_ball_subset_sourcePoint_image_ball (neg_neg_of_pos hτ) hR
        (by norm_num : (1 : ℝ) < 2)] with k hk hcover
    let h := (S.rescaling (G.subsequence k)).flow.metric (-τ)
    let B := h.ball (S.base (G.subsequence k)) R
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨h.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    have hB : IsOpen B := isOpen_lt (continuous_const.edist continuous_id) continuous_const
    have htail' : (∫⁻ x in Bᶜ, F k x ∂h.volumeMeasure) ≤ (ε : ℝ≥0∞) := by
      simpa only [calibratedMetricVolume_eq_volumeMeasure, ENNReal.ofReal_coe_nnreal] using
        htail (G.subsequence k)
    rw [← lintegral_add_compl (F k) hB.measurableSet]
    exact add_le_add ((lintegral_mono_set hcover).trans hk.1) htail'
  exact hlocal.trans (add_le_add
    (mul_le_mul' le_rfl (by simpa only [setLIntegral_univ] using
      (lintegral_mono_set (μ := g.volumeMeasure) (f := f) (subset_univ U)))) le_rfl)

end PoincareConjecture.AncientCompactTimeConvergence
