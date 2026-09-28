import PoincareConjecture.Definitions.M19TwoDimensionalClassification
import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Statements.M18AsymptoticSoliton

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

structure TwoDimensionalClassificationPredecessors : Prop where
  compactness :
    ∀ {T' T : ℝ}, T' < 0 → 0 < T →
      ∀ H : PointedRicciFlowCompactnessHypotheses 2 T' T,
        Nonempty (PointedRicciFlowCompactnessConclusion H)
  m18 :
    ∀ (K : AncientKappaSolution 2 M) (S : AncientRescalingSequence K),
      AncientAsymptoticSolitonConclusion S

structure TwoDimensionalAsymptoticRoundTheory
    (K : AncientKappaSolution 2 M) : Prop where
  classify :
    ∀ S : AncientRescalingSequence K,
      ∃ L : AncientAsymptoticSolitonLimitData S,
        TwoDimensionalAsymptoticRoundCertificate S L

structure TwoDimensionalClassificationTheory : Prop where
  asymptotic_round : ∀ K : AncientKappaSolution 2 M,
    Nonempty (TwoDimensionalAsymptoticRoundTheory K)
  shrinking_soliton : ∀ S : GradientShrinkingSolitonData 2 M,
    Nonempty (TwoDimensionalShrinkingSolitonConclusion S)
  ancient_classification : ∀ K : AncientKappaSolution 2 M,
    Nonempty (TwoDimensionalAncientRoundCertificate K)

end PoincareConjecture
