import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.RoundLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Construction









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem compact_nonround_asymptotic_limit_noncompact
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) (hnonround : ¬ IsRoundAncientKappaSolution K)
    (S : AncientRescalingSequence K) (L : AncientAsymptoticSolitonLimitData S) :
    ¬ IsCompact (Set.univ : Set L.convergence.limit.carrier.carrier) := by
  intro hcompact
  let : CompactSpace L.convergence.limit.carrier.carrier := ⟨hcompact⟩
  apply hnonround
  exact compact_isRound_of_compact_round_limit P K S L.convergence inferInstance
    (L.constantPositiveSectionalCurvature_of_compact ricciFlowCurvatureTheory (-1) (by norm_num))

end PoincareConjecture
