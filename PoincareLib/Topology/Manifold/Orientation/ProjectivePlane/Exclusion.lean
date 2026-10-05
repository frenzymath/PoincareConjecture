import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Statement
import PoincareLib.Topology.Manifold.ThreeDimensional.ClosedSimplyConnected
import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Atlas.OpenEmbedding
import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Atlas.LocalOrientation
import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Nonorientable

/-!
# M83 projective-plane exclusion proof entry

One theorem owns the topological orientation obstruction. The two checked
adapters use the exact orientation output of M02; they add no hypothesis to
the final Poincare statements and do not alter M02's frozen contract.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

/-- M83: on any Hausdorff second-countable smooth three-manifold without
boundary, a compatible signed atlas excludes every topological open embedding
of `RealProjectiveTwo` times `(-1,1)`. No compactness, connectedness, metric,
or smoothness of the proposed embedding is assumed.

Source: Morgan--Tian Theorem 0.3, footnote 2, printed p. xii. The proof must
transport topological orientation and exclude the orientation-reversing deck
map on `S^2 x (-1,1)`. See the source contract and the initial-projective-plane
producer erratum dated 2026-09-17. No Section 19.2 correction applies. -/
theorem m83OrientationExclusion : M83OrientationExclusionStatement.{u} := by
  intro M _ _ _ _ _ A
  rintro ⟨f, hf⟩
  let X := RealProjectiveTwo × Poincare.Topology.Orientation.ProjectivePlane.NormalInterval
  let : Nonempty X := Nonempty.map Poincare.Topology.Orientation.ProjectivePlane.projectivePlaneCover inferInstance
  let : T2Space X := hf.isEmbedding.t2Space
  let : SecondCountableTopology X := hf.isEmbedding.secondCountableTopology
  let P := Poincare.Topology.Orientation.ProjectivePlane.positiveThreeAtlasOpenEmbedding f hf
    (Poincare.Topology.positiveThreeAtlasOfSigned M A)
  let : ChartedSpace (EuclideanSpace Real (Fin 3)) X := P.charts
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace Real (Fin 3)) X
  obtain ⟨O⟩ := Poincare.Topology.Orientation.ProjectivePlane.exists_localOrientation_of_positiveThreeAtlas P
  exact Poincare.Topology.Orientation.ProjectivePlane.projectivePlaneThickening_not_orientable O

/-- Given M83's orientation obstruction and an actual M02 topology conclusion
on M, its orientation field supplies the global surgery exclusion on M.
This is checked composition of M02 with Theorem 0.3, footnote 2. -/
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

/-- Every compact Hausdorff second-countable simply connected smooth
three-manifold satisfies the projective-plane exclusion required by surgery.
Apply M02 for orientation and M83 for the topological obstruction; no new
admission or classification hypothesis occurs in this assembly. -/
theorem m83NoProjectivePlaneFromMilestones
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [SimplyConnectedSpace M] :
    NoTrivialNormalProjectivePlane (M := M) := by
  obtain ⟨H⟩ := closedSimplyConnectedThreeManifoldTopology (M := M)
  exact m83NoProjectivePlaneFromTopology m83OrientationExclusion H

end PoincareMT
