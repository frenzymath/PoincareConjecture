import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitGradient.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

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

theorem reducedLengthPullback_limit_gradient_norm_bound_ae
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ))) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᵐ x ∂(G.limit.flow.metric (-τ)).volumeMeasure,
      (G.limit.flow.metric (-τ)).tangentNorm x
        ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x) ≤
        Real.sqrt (3 / τ) * Real.sqrt (l (x, τ)) := by
  filter_upwards [G.reducedLengthPullback_limit_gradient_bound_ae P hσ l hlim hτ] with x hx
  have h := Real.sqrt_le_sqrt hx
  rw [Real.sqrt_sq (show 0 ≤ (G.limit.flow.metric (-τ)).tangentNorm x
    ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x) from
      Real.sqrt_nonneg _)] at h
  rwa [show 3 * l (x, τ) / τ = (3 / τ) * l (x, τ) by ring,
    Real.sqrt_mul (show 0 ≤ 3 / τ by positivity)] at h

end PoincareConjecture.AncientCompactTimeConvergence
