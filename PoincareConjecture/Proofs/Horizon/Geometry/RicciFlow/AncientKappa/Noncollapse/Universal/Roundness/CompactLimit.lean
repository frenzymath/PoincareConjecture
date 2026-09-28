import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.AncientCriterion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.Convergence.CompactPinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientKappaRoundness

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]




theorem isRoundAncientKappaSolution_of_compact_round_limit
    {d : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
    (K : AncientKappaSolution 3 M) (S : AncientRescalingSequence K)
    (G : AncientCompactTimeConvergence S)
    (hcompact : CompactSpace G.limit.carrier.carrier)
    (hround : ConstantPositiveSectionalCurvature
      (G.limit.flow.metric (-1)) (G.limit.flow.connection (-1))) :
    IsRoundAncientKappaSolution K := by
  let : CompactSpace M := G.compactSpace_of_compact_limit hcompact
  let hcalculus (k : ℕ) := H.tensor_calculus 3 M
    ((S.rescaling (G.subsequence k)).flow.metric (-1))
    ((S.rescaling (G.subsequence k)).flow.connection (-1))
  have hlimit := (G.limit.flow.connection (-1)).intrinsicCurvatureTensorCalculus
  apply isRoundAncientKappaSolution_of_early_pinching H K
  intro c hc t ht
  have hpinch := eventually_rescaling_ricciComplement_mem G hcompact hcalculus hlimit hround hc
  have hlarge := (S.scale_tendsto.comp G.subsequence_strictMono.tendsto_atTop).eventually
    (eventually_gt_atTop (-t))
  obtain ⟨k, hk, hklarge⟩ := (hpinch.and hlarge).exists
  dsimp only [Function.comp_def] at hklarge
  refine ⟨S.scale (G.subsequence k) * (-1), by nlinarith, ?_⟩
  intro x
  exact ricciComplement_mem_of_rescaling (S.rescaling (G.subsequence k)) (by norm_num)
    (H.tensor_calculus 3 M _ _) (hcalculus k) x c (hk x)

end PoincareConjecture.AncientKappaRoundness
