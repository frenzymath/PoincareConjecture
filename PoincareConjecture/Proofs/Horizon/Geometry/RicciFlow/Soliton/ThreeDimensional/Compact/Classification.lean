import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.Roundness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.Homothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Models
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Generation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [CompactSpace M]

theorem exists_compactRoundShrinkingModel (hC : RicciFlowCurvatureTheory.{u})
    (S : GradientShrinkingSolitonData 3 M) :
    ∃ G : ShrinkingSolitonFlow S, Nonempty (CompactRoundShrinkingModel G) := by
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  exact ⟨G, G.compactRoundModel hC⟩

theorem constantPositiveSectionalCurvature_of_compact
    (hC : RicciFlowCurvatureTheory.{u}) (S : GradientShrinkingSolitonData 3 M) :
    ConstantPositiveSectionalCurvature S.metric S.connection := by
  obtain ⟨G, ⟨C⟩⟩ := S.exists_compactRoundShrinkingModel hC
  let E : HomotheticMetricSlice (G.flow.metric (-1)) S.metric 1 :=
    { map := Diffeomorph.refl (𝓡 3) M ∞
      inner_eq := by
        intro x v w
        simp [G.at_minus_one] }
  exact E.constantPositiveSectionalCurvature_three (by norm_num)
    (G.flow.connection (-1)) S.connection (C.round_at_time (-1) (by norm_num))


theorem threeDimensionalClassificationData_of_compact
    (hC : RicciFlowCurvatureTheory.{u}) (S : GradientShrinkingSolitonData 3 M) :
    Nonempty (ThreeDimensionalClassificationData S) := by
  obtain ⟨G, ⟨C⟩⟩ := S.exists_compactRoundShrinkingModel hC
  exact ⟨⟨⟨G, .compactRound C⟩⟩⟩

end PoincareConjecture.GradientShrinkingSolitonData
