import PoincareConjecture.Statements.M83OrientationExclusion
import PoincareConjecture.Proofs.M02
import PoincareConjecture.Proofs.M83.OpenEmbedding_Pullback
import PoincareConjecture.Proofs.M83.LocalOrientationFromAtlas
import PoincareConjecture.Proofs.M83.ProjectivePlaneThickening_NonOrientable









set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture










theorem m83OrientationExclusion : M83OrientationExclusionStatement.{u} := by
  intro M _ _ _ _ _ A
  rintro ⟨f, hf⟩
  let X := RealProjectiveTwo × Proofs.M83.NormalInterval
  let : Nonempty X := Nonempty.map Proofs.M83.projectivePlaneCover inferInstance
  let : T2Space X := hf.isEmbedding.t2Space
  let : SecondCountableTopology X := hf.isEmbedding.secondCountableTopology
  let P := Proofs.M83.positiveThreeAtlasOpenEmbedding f hf
    (Proofs.M02.Topology.positiveThreeAtlasOfSigned M A)
  let : ChartedSpace (EuclideanSpace Real (Fin 3)) X := P.charts
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace Real (Fin 3)) X
  obtain ⟨O⟩ := Proofs.M83.exists_localOrientation_of_positiveThreeAtlas P
  exact Proofs.M83.projectivePlaneThickening_not_orientable O




theorem m83NoProjectivePlaneFromTopology
    (hM83 : M83OrientationExclusionStatement.{u})
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (H : ClosedSimplyConnectedThreeManifoldConclusion (M := M)) :
    NoTrivialNormalProjectivePlane (M := M) := by
  obtain ⟨O⟩ := H.orientation
  exact hM83 M O





theorem m83NoProjectivePlaneFromMilestones
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [SimplyConnectedSpace M] :
    NoTrivialNormalProjectivePlane (M := M) := by
  obtain ⟨H⟩ := closedSimplyConnectedThreeManifoldTopology (M := M)
  exact m83NoProjectivePlaneFromTopology m83OrientationExclusion H

end PoincareConjecture
