import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.SmoothHeatEquation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.SmoothHamiltonJacobi
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Equation.BackwardPotential

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

theorem limitReducedLength_soliton_equation
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ))) :
    ∀ t < 0, ∀ x : G.limit.carrier.carrier, ∀ v w : TangentSpace (𝓡 n) x,
      (G.limit.flow.connection t).ricci x v w +
        (G.limit.flow.connection t).hessian (fun y => l (y, -t)) x v w +
        (1 / (2 * t)) * (G.limit.flow.metric t).inner x v w = 0 := by
  have hs := G.limitReducedLength_contMDiffOn P hl hl0 hlim
  apply G.limit.flow.soliton_equation_of_backward_scalar_equalities hs
  · intro τ hτ x
    exact G.limitReducedLength_heat_equation P hl hl0 hlim x hτ
  · intro τ hτ x
    exact G.limitReducedLength_hamiltonJacobi_of_smooth P strictMono_id l hlim hs x hτ

theorem limitReducedLength_entropyFactor_eq_zero
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hl0 : ∀ z ∈ univ ×ˢ Ioi (0 : ℝ), 0 ≤ l z)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ))) :
    ∀ t < 0, ∀ x : G.limit.carrier.carrier,
      G.limit.flow.entropyFactor (fun z => l (z.1, -z.2)) t x = 0 := by
  intro t ht x
  have hh := G.limitReducedLength_heat_equation P hl hl0 hlim x (neg_pos.mpr ht)
  have hj := G.limitReducedLength_hamiltonJacobi_of_smooth P strictMono_id l hlim
    (G.limitReducedLength_contMDiffOn P hl hl0 hlim) x (neg_pos.mpr ht)
  generalize hs : - -t = s at hh hj
  have hst : s = t := hs.symm.trans (neg_neg t)
  clear hs
  subst s
  change -t * (2 * (G.limit.flow.connection t).laplacian (fun y => l (y, -t)) x -
    (G.limit.flow.metric t).inner x
      ((G.limit.flow.connection t).gradient (fun y => l (y, -t)) x)
      ((G.limit.flow.connection t).gradient (fun y => l (y, -t)) x) +
    (G.limit.flow.connection t).scalarCurvature x) + l (x, -t) - n = 0
  field_simp [ne_of_lt ht] at hh hj
  nlinarith

end PoincareConjecture.AncientCompactTimeConvergence
