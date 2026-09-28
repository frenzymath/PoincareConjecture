import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.LimitRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

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

theorem tendsto_lintegral_reducedLengthPullback_on_precompact
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hlim : TendstoLocallyUniformlyOn (fun k z => G.reducedLengthPullback k z.1 z.2)
      l atTop (univ ×ˢ Ioi (0 : ℝ))) {τ : ℝ} (hτ : 0 < τ)
    {V : Set G.limit.carrier.carrier} (hV : MeasurableSet V) (hcompact : IsCompact (closure V)) :
    Tendsto
      (fun k => ∫⁻ x in V, ENNReal.ofReal
        (τ ^ (-(n : ℝ) / 2) * Real.exp (-G.reducedLengthPullback k x τ))
        ∂(G.limit.flow.metric (-τ)).volumeMeasure)
      atTop (𝓝 (∫⁻ x in V, ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
        ∂(G.limit.flow.metric (-τ)).volumeMeasure)) := by
  let g := G.limit.flow.metric (-τ)
  let c : ℝ := τ ^ (-(n : ℝ) / 2)
  have hc : 0 ≤ c := Real.rpow_nonneg hτ.le _
  apply tendsto_lintegral_filter_of_dominated_convergence' (fun _ => ENNReal.ofReal c)
  · obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
    filter_upwards [eventually_ge_atTop j,
      eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0)] with k hjk hk
    have hsource : V ⊆ G.exhaustion k :=
      subset_closure.trans (hj.trans (G.exhaustion_monotone hjk))
    have hmap : ContinuousOn (G.sourcePoint k) V := by
      exact (((G.embedding k).spatialHomeomorph (G.exhaustion_open k) hk).continuousOn.mono hsource)
    have hcont : ContinuousOn (fun x => ENNReal.ofReal
        (τ ^ (-(n : ℝ) / 2) * Real.exp (-G.reducedLengthPullback k x τ))) V :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
          (((P.continuous_reducedLength S.reference (S.scale (G.subsequence k) * τ)
            (mul_pos (S.scale_pos _) hτ)).comp_continuousOn hmap).neg)))
    exact hcont.aemeasurable hV
  · exact .of_forall fun k => .of_forall fun x => ENNReal.ofReal_le_ofReal (by
      have hpos := G.reducedLengthPullback_pos P k x hτ
      have hexp : Real.exp (-G.reducedLengthPullback k x τ) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hpos.le)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hc)
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by
        rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
        exact (measure_mono subset_closure |>.trans_lt (hcompact.measure_lt_top (μ := g.volumeMeasure))).ne)
  · exact .of_forall fun x => ENNReal.tendsto_ofReal
      (tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp
        ((hlim.tendsto_at
          (show (x, τ) ∈ univ ×ˢ Ioi (0 : ℝ) from ⟨mem_univ x, hτ⟩)).neg)))

end PoincareConjecture.AncientCompactTimeConvergence
