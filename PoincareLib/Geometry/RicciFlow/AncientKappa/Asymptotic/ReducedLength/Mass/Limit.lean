import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.LowerBound
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedVolume

/-! # Exact total mass of the ancient reduced-length limit

The uniform Gaussian tails identify the full limiting density mass with the
original asymptotic reduced volume at every positive backward time.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem exists_constant_limitDensity_mass
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hlim : TendstoLocallyUniformlyOn (fun k z => G.reducedLengthPullback k z.1 z.2)
      l atTop (univ ×ˢ Ioi (0 : ℝ))) :
    ∃ V : ℝ, 0 ≤ V ∧ V < euclideanReducedVolume n ∧ ∀ τ : ℝ, 0 < τ →
      (∫⁻ x, ENNReal.ofReal (τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
        ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) = ENNReal.ofReal V := by
  obtain ⟨V, hV0, hVE, hVlim⟩ := ancientRescalingSequence_reducedVolume_limit S P
  refine ⟨V, hV0, hVE, fun τ hτ => ?_⟩
  rw [calibratedMetricVolume_eq_volumeMeasure]
  have hlimV := (hVlim τ hτ).comp G.subsequence_strictMono.tendsto_atTop
  exact le_antisymm (G.lintegral_limitDensity_le_of_tendsto_reducedVolume P hlim hτ hlimV)
    (G.le_lintegral_limitDensity_of_tendsto_reducedVolume P hlim hτ hlimV)

end PoincareMT.AncientCompactTimeConvergence
