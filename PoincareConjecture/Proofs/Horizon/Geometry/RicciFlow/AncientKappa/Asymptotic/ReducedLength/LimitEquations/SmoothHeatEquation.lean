import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.GlobalClassical

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

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

theorem limitReducedLength_heat_equation
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    (x : G.limit.carrier.carrier) {τ : ℝ} (hτ : 0 < τ) :
    deriv (fun t => l (x, t)) τ -
      (G.limit.flow.connection (-τ)).laplacian (fun y => l (y, τ)) x +
      (G.limit.flow.metric (-τ)).inner x
        ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x)
        ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x) -
      (G.limit.flow.connection (-τ)).scalarCurvature x + (n : ℝ) / (2 * τ) = 0 := by
  apply RicciFlow.ConjugateHeat.potential_heat_equation_of_contMDiffOn_weakPairing_eq_zero
    G.limit.flow (G.limitReducedLength_contMDiffOn P hl hl0 hlim) ?_ x hτ
  intro φ hφ hφc hφs
  exact G.limitReducedLength_weakPairing_eq_zero P hl hl0 hlim hφ hφc hφs

end PoincareConjecture.AncientCompactTimeConvergence
