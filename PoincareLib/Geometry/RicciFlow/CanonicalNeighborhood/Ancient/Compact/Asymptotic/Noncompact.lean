import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.RoundLimit
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Compact
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-!
# Noncompact asymptotic limits of nonround solutions

Compact shrinking-soliton classification and ancient pinching rule out a
compact asymptotic limit. This is the use of Corollary 9.44 in the bounded
diameter branch of Morgan--Tian, Theorem 9.89, p. 241.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- Every actual asymptotic soliton limit of a nonround ancient solution is noncompact. -/
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

end PoincareMT
