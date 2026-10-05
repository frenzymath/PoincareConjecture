import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.ActualMass
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Soliton
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Nonflat.Gaussian
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Noncollapse
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Scalar

/-!
# Asymptotic soliton limits of the specified ancient rescalings

Morgan--Tian, Theorem 9.11 and Remark 9.12, pp. 183--185.
The statement preserves the M18 target and predecessor services at Mapher
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
-/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u
namespace PoincareMT

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

/-- Every specified ancient rescaling sequence has a complete nonflat pointed
smooth limit with the shrinking soliton equation. -/
theorem ancientAsymptoticSolitonLimits
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

end PoincareMT
