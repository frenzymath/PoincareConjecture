import PoincareLib.Geometry.RicciFlow.Soliton.Flow.Generation
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Models
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Compactness
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Roundness
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Models
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.Homothety

/-!
# Compact-round classification from the generated flow

The surface roundness theorem and the generated flow give the complete
frozen M19 shrinking-soliton conclusion. The M20 compact-round branch is
assembled from its static geometric hypotheses. Every time-slice roundness
certificate concerns the flow constructed from the original soliton datum.
Morgan--Tian, Theorem 9.42 and Claim 9.43, pp. 206-208.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

section Surface

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Apply the generated flow to the M19 shrinking-soliton conclusion.
Compactness follows from the original surface soliton hypotheses. -/
theorem exists_twoDimensionalShrinkingSolitonConclusion_of_round
    (S : GradientShrinkingSolitonData 2 M)
    (hround : ConstantPositiveSectionalCurvature S.metric S.connection) :
    Nonempty (TwoDimensionalShrinkingSolitonConclusion S) := by
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  exact ⟨⟨G, .compactRound ⟨S.compactSpace, G.round_at_time hround⟩⟩⟩

/-- The full M19 shrinking-soliton output from the exact frozen datum. -/
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

/-- Apply the generated flow to the compact-round branch of the frozen M20
classification output, on the same carrier and original metric. -/
theorem exists_threeDimensionalClassificationData_of_compact_round
    (S : GradientShrinkingSolitonData 3 M) (hc : CompactSpace M)
    (hround : ConstantPositiveSectionalCurvature S.metric S.connection) :
    Nonempty (ThreeDimensionalClassificationData S) := by
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  exact ⟨⟨⟨G, .compactRound ⟨hc, G.round_at_time_three hround⟩⟩⟩⟩

end ThreeDimensional

end PoincareMT
