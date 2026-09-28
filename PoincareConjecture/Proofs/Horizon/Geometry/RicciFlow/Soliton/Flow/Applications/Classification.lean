import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Generation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Models
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Roundness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Models
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.Homothety

set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

section Surface

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_twoDimensionalShrinkingSolitonConclusion_of_round
    (S : GradientShrinkingSolitonData 2 M)
    (hround : ConstantPositiveSectionalCurvature S.metric S.connection) :
    Nonempty (TwoDimensionalShrinkingSolitonConclusion S) := by
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  exact ⟨⟨G, .compactRound ⟨S.compactSpace, G.round_at_time hround⟩⟩⟩

theorem exists_twoDimensionalShrinkingSolitonConclusion
    (S : GradientShrinkingSolitonData 2 M) :
    Nonempty (TwoDimensionalShrinkingSolitonConclusion S) :=
  exists_twoDimensionalShrinkingSolitonConclusion_of_round S S.round

end Surface

section ThreeDimensional

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_threeDimensionalClassificationData_of_compact_round
    (S : GradientShrinkingSolitonData 3 M) (hc : CompactSpace M)
    (hround : ConstantPositiveSectionalCurvature S.metric S.connection) :
    Nonempty (ThreeDimensionalClassificationData S) := by
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  exact ⟨⟨⟨G, .compactRound ⟨hc, G.round_at_time_three hround⟩⟩⟩⟩

end ThreeDimensional

end PoincareConjecture
