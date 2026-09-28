import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.ActualMass
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Soliton
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Nonflat.Gaussian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Scalar

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u
namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

theorem horizon_ancientAsymptoticSolitonLimits
    (n : ℕ)
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    AncientAsymptoticSolitonConclusion S := by
  obtain ⟨G, l, hl, hl0, hlim, hcompact, hlip, hmass⟩ :=
    S.exists_ancient_reducedLength_limit_with_constant_mass P
  have hs := G.limitReducedLength_contMDiffOn P hl hl0 hlim
  have hsol := G.limitReducedLength_soliton_equation P hl hl0 hlim
  have hzero := G.limitReducedLength_entropyFactor_eq_zero P hl hl0 hlim
  exact ⟨{
    convergence := G
    nonflat_at := G.nonflat_at_of_limitReducedLength_soliton_entropy P hs hlim hsol hzero
    kappa_noncollapsed := G.kappa_noncollapsed
    scalar_curvature_nonnegative_time_derivative := G.scalar_derivative_nonnegative P
    potential := fun z => l (z.1, -z.2)
    potential_smooth := RicciFlow.contMDiffOn_reverse_potential hs
    soliton_equation := hsol }⟩

end PoincareConjecture
