import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.CapEstimates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Volume.Convergence












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem eventually_volume_image_le_eight_of_isCompact_closure
    (hconv : M23TerminalMetricConvergence G e)
    {U : Set G.limit.carrier.carrier} (hU : IsOpen U)
    (hcompact : IsCompact (closure U)) :
    ∀ᶠ k in atTop,
      calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
          ((fun x ↦ ((e k).toFun (0, x)).2) '' U) ≤
        8 * calibratedMetricVolume (G.limit.flow.flow.metric 0) U := by
  filter_upwards [hconv.eventually_volume_image_bounds hU hcompact
    (by norm_num : (1 : ℝ) < 2)] with k hk
  simpa only [ENNReal.ofReal_ofNat, show (2 : ℝ≥0∞) ^ 3 = 8 by norm_num] using hk.1



theorem eventually_cap_volume_image_le_eight
    (hconv : M23TerminalMetricConvergence G e)
    (A : CapCertificate (G.limit.flow.flow.metric 0)) :
    ∀ᶠ k in atTop,
      calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
          ((fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier) ≤
        8 * calibratedMetricVolume (G.limit.flow.flow.metric 0) A.carrier :=
  hconv.eventually_volume_image_le_eight_of_isCompact_closure A.carrier_open
    (A.isCompact_closure_carrier (G.limit.flow.complete 0 le_rfl))



theorem eventually_cap_volume_bound_original_constant
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (A : CapCertificate (G.limit.flow.flow.metric 0)) :
    ∀ᶠ k in atTop,
      calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
          ((fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier) <
        ENNReal.ofReal A.cap_constant *
          ENNReal.ofReal ((scalarCurvatureSupOn
            ((S.term (G.subsequence k)).flow.flow.metric 0)
            ((S.term (G.subsequence k)).flow.flow.connection 0)
            ((fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier)) ^ (-3 / 2 : ℝ)) := by
  have hscale := (hconv.tendsto_cap_scalarSup hfixed A).rpow_const
    (p := (-3 / 2 : ℝ)) (Or.inl A.scalar_sup_pos.ne')
  have hright := ENNReal.Tendsto.const_mul
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hscale)
    (Or.inr (ENNReal.ofReal_ne_top (r := A.cap_constant)))
  exact (hconv.tendsto_cap_volume_image A).eventually_lt hright A.volume_bound



theorem eventually_cap_volume_bound
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (A : CapCertificate (G.limit.flow.flow.metric 0)) :
    ∀ᶠ k in atTop,
      calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
          ((fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier) <
        ENNReal.ofReal (16 * A.cap_constant) *
          ENNReal.ofReal ((scalarCurvatureSupOn
            ((S.term (G.subsequence k)).flow.flow.metric 0)
            ((S.term (G.subsequence k)).flow.flow.connection 0)
            ((fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier)) ^ (-3 / 2 : ℝ)) := by
  filter_upwards [hconv.eventually_cap_volume_bound_original_constant hfixed A] with k hk
  apply hk.trans_le
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (show A.cap_constant ≤ 16 * A.cap_constant by linarith [A.cap_constant_pos])) le_rfl

end M23TerminalMetricConvergence

end PoincareConjecture
