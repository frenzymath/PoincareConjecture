import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Applications.Classification
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Roundness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Existence

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem horizon_twoDimensionalAncientAndShrinkingSolitonClassification
    (P : TwoDimensionalClassificationPredecessors (M := M)) :
    TwoDimensionalClassificationTheory (M := M) := by
  refine {
    asymptotic_round := P.asymptoticRoundTheory
    shrinking_soliton := exists_twoDimensionalShrinkingSolitonConclusion
    ancient_classification := ?_ }
  intro K
  have hsequence : Nonempty (AncientRescalingSequence K) :=
    K.exists_ancientRescalingSequence
  obtain ⟨S⟩ := hsequence
  exact ⟨P.ancientRoundCertificate_of_sequence K S⟩

end PoincareConjecture
