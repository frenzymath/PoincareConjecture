import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.Actual
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.Integrable


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} (S : AncientRescalingSequence K)

theorem exists_ancient_reducedLength_limit_with_constant_mass
    (P : AncientAsymptoticSolitonPredecessors K) :
    ∃ G : AncientCompactTimeConvergence S, ∃ l : G.limit.carrier.carrier × ℝ → ℝ,
      ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)) ∧
      (∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z) ∧
      TendstoLocallyUniformlyOn (fun k z => G.reducedLengthPullback k z.1 z.2)
        l atTop (univ ×ˢ Ioi (0 : ℝ)) ∧
      (∀ A : Set (G.limit.carrier.carrier × ℝ), IsCompact A → A ⊆ univ ×ˢ Ioi (0 : ℝ) →
        TendstoUniformlyOn (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop A) ∧
      (∀ q : G.limit.carrier.carrier,
        LocallyLipschitzOn ((chartAt (EuclideanSpace ℝ (Fin n)) q).target ×ˢ Ioi (0 : ℝ))
          (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
            l ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1, z.2))) ∧
      ∃ V : ℝ, 0 ≤ V ∧ V < euclideanReducedVolume n ∧ ∀ τ : ℝ, 0 < τ →
        Integrable (fun x => τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ)))
          (calibratedMetricVolume (G.limit.flow.metric (-τ))) ∧
        (∫ x, τ ^ (-(n : ℝ) / 2) * Real.exp (-l (x, τ))
          ∂calibratedMetricVolume (G.limit.flow.metric (-τ))) = V := by
  obtain ⟨G, l, hl, hl0, hlim, hcompact, hlip⟩ := S.exists_ancient_reducedLength_limit P
  exact ⟨G, l, hl, hl0, hlim, hcompact, hlip,
    G.exists_integrable_constant_limitDensity_mass P hl hlim⟩

end PoincareConjecture.AncientRescalingSequence
