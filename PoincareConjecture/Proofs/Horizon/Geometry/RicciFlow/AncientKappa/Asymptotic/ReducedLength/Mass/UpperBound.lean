import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.CompactIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.Distortion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Tails.TotalMass
import PoincareConjecture.Proofs.Horizon.Analysis.Asymptotics.MultiplicativeBounds


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

theorem lintegral_limitDensity_le_of_tendsto_reducedVolume
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hlim : TendstoLocallyUniformlyOn (fun k z => G.reducedLengthPullback k z.1 z.2)
      l atTop (univ ×ˢ Ioi (0 : ℝ))) {τ Vlim : ℝ} (hτ : 0 < τ)
    (hV : Tendsto
      (fun k => reducedVolume K.flow 0 S.reference (S.scale (G.subsequence k) * τ))
      atTop (𝓝 Vlim)) :
    (∫⁻ x, ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
      ∂(G.limit.flow.metric (-τ)).volumeMeasure) ≤ ENNReal.ofReal Vlim := by
  let F (k : ℕ) (x : M) : ℝ≥0∞ := ENNReal.ofReal
    (τ ^ (-(n : ℝ) / 2) * Real.exp (-reducedLength K.flow 0 S.reference x
      (S.scale (G.subsequence k) * τ)))
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
  have hlocal (U : Set G.limit.carrier.carrier) (hU : IsOpen U) (hUc : IsCompact (closure U)) :
      (∫⁻ x in U, ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
        ∂(G.limit.flow.metric (-τ)).volumeMeasure) ≤ ENNReal.ofReal Vlim := by
    apply Poincare.Analysis.ennreal_le_of_forall_one_lt_pow_mul n
    intro C hC
    have hconv := G.tendsto_lintegral_reducedLengthPullback_on_precompact P hlim hτ
      hU.measurableSet hUc
    have hprod := ENNReal.Tendsto.mul tendsto_const_nhds
      (Or.inl (pow_ne_zero n (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hC))))
      htotalLim (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    apply le_of_tendsto_of_tendsto hconv hprod
    filter_upwards [G.eventually_lintegral_sourcePoint_image_bounds (neg_neg_of_pos hτ) hC
      hU hUc F hF] with k hk
    exact hk.2.trans (mul_le_mul' le_rfl (by
      simpa only [setLIntegral_univ] using
        (lintegral_mono_set (μ := ((S.rescaling (G.subsequence k)).flow.metric (-τ)).volumeMeasure)
          (f := F k) (subset_univ (G.sourcePoint k '' U)))))
  calc
    _ = ∫⁻ x in ⋃ j, G.exhaustion j,
        ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
          ∂(G.limit.flow.metric (-τ)).volumeMeasure := by
      rw [G.exhaustion_covers, setLIntegral_univ]
    _ = ⨆ j, ∫⁻ x in G.exhaustion j,
        ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
          ∂(G.limit.flow.metric (-τ)).volumeMeasure :=
      setLIntegral_iUnion_of_directed _ (fun i j => ⟨max i j,
        G.exhaustion_monotone (le_max_left _ _), G.exhaustion_monotone (le_max_right _ _)⟩)
    _ ≤ ENNReal.ofReal Vlim := iSup_le fun j =>
      hlocal (G.exhaustion j) (G.exhaustion_open j) (G.exhaustion_compactClosure j)

end PoincareConjecture.AncientCompactTimeConvergence
