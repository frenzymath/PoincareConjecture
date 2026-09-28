import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.Classification
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Contradiction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Realization

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem ShrinkingSolitonFlow.threeDimensionalSolitonModel
    {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)
    (hP : ThreeDimensionalClassificationPredecessors.{u}) :
    Nonempty (ThreeDimensionalSolitonModel S G) := by
  classical
  by_cases hc : CompactSpace M
  · letI : CompactSpace M := hc
    obtain ⟨C⟩ := G.compactRoundModel hP.curvature
    exact ⟨.compactRound C⟩
  · obtain ⟨x, v, w, hv, hw, hvw, hzero⟩ := S.exists_null_plane_of_noncompact hP hc
    exact global_model_of_splitting_obligation
      (G.globalSplittingObligation_of_null_plane hP x v w hv hw hvw hzero)

theorem GradientShrinkingSolitonData.threeDimensionalClassificationData
    (S : GradientShrinkingSolitonData 3 M)
    (hP : ThreeDimensionalClassificationPredecessors.{u}) :
    Nonempty (ThreeDimensionalClassificationData S) := by
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  obtain ⟨model⟩ := G.threeDimensionalSolitonModel hP
  exact ⟨⟨⟨G, model⟩⟩⟩

end PoincareConjecture
